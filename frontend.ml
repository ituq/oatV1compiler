open Ll
open Llutil
open Ast

(* instruction streams ------------------------------------------------------ *)

(* As in the last project, we'll be working with a flattened representation
   of LLVMlite programs to make emitting code easier. This version
   additionally makes it possible to emit elements will be gathered up and
   "hoisted" to specific parts of the constructed CFG
   - G of gid * Ll.gdecl: allows you to output global definitions in the middle
     of the instruction stream. You will find this useful for compiling string
     literals
   - E of uid * insn: allows you to emit an instruction that will be moved up
     to the entry block of the current function. This will be useful for
     compiling local variable declarations
*)

type elt =
  | L of Ll.lbl             (* block labels *)
  | I of uid * Ll.insn      (* instruction *)
  | T of Ll.terminator      (* block terminators *)
  | G of gid * Ll.gdecl     (* hoisted globals (usually strings) *)
  | E of uid * Ll.insn      (* hoisted entry block instructions *)

type stream = elt list
let ( >@ ) x y = y @ x
let ( >:: ) x y = y :: x
let lift : (uid * insn) list -> stream = List.rev_map (fun (x,i) -> I (x,i))

(* Build a CFG and collection of global variable definitions from a stream *)
let cfg_of_stream (code:stream) : Ll.cfg * (Ll.gid * Ll.gdecl) list  =
    let gs, einsns, insns, term_opt, blks = List.fold_left
      (fun (gs, einsns, insns, term_opt, blks) e ->
        match e with
        | L l ->
           begin match term_opt with
           | None ->
              if (List.length insns) = 0 then (gs, einsns, [], None, blks)
              else failwith @@ Printf.sprintf "build_cfg: block labeled %s has\
                                               no terminator" l
           | Some term ->
              (gs, einsns, [], None, (l, {insns; term})::blks)
           end
        | T t  -> (gs, einsns, [], Some (Llutil.Parsing.gensym "tmn", t), blks)
        | I (uid,insn)  -> (gs, einsns, (uid,insn)::insns, term_opt, blks)
        | G (gid,gdecl) ->  ((gid,gdecl)::gs, einsns, insns, term_opt, blks)
        | E (uid,i) -> (gs, (uid, i)::einsns, insns, term_opt, blks)
      ) ([], [], [], None, []) code
    in
    match term_opt with
    | None -> failwith "build_cfg: entry block has no terminator"
    | Some term ->
       let insns = einsns @ insns in
       ({insns; term}, blks), gs


(* compilation contexts ----------------------------------------------------- *)

(* To compile OAT variables, we maintain a mapping of source identifiers to the
   corresponding LLVMlite operands. Bindings are added for global OAT variables
   and local variables that are in scope. *)

module Ctxt = struct

  type t = (Ast.id * (Ll.ty * Ll.operand)) list
  let empty = []

  (* Add a binding to the context *)
  let add (c:t) (id:id) (bnd:Ll.ty * Ll.operand) : t = (id,bnd)::c

  (* Lookup a binding in the context *)
  let lookup (id:Ast.id) (c:t) : Ll.ty * Ll.operand =
    List.assoc id c

  (* Lookup a function, fail otherwise *)
  let lookup_function (id:Ast.id) (c:t) : Ll.ty * Ll.operand =
    match List.assoc id c with
    | Ptr (Fun (args, ret)), g -> Ptr (Fun (args, ret)), g
    | _ -> failwith @@ id ^ " not bound to a function"

  let lookup_function_option (id:Ast.id) (c:t) : (Ll.ty * Ll.operand) option =
    try Some (lookup_function id c) with _ -> None

end

(* compiling OAT types ------------------------------------------------------ *)

(* The mapping of source types onto LLVMlite is straightforward. Booleans and ints
   are represented as the corresponding integer types. OAT strings are
   pointers to bytes (I8). Arrays are the most interesting type: they are
   represented as pointers to structs where the first component is the number
   of elements in the following array.

   The trickiest part of this project will be satisfying LLVM's rudimentary type
   system. Recall that global arrays in LLVMlite need to be declared with their
   length in the type to statically allocate the right amount of memory. The
   global strings and arrays you emit will therefore have a more specific type
   annotation than the output of cmp_rty. You will have to carefully bitcast
   gids to satisfy the LLVM type checker.
*)

let rec cmp_ty : Ast.ty -> Ll.ty = function
  | Ast.TBool  -> I1
  | Ast.TInt   -> I64
  | Ast.TRef r -> Ptr (cmp_rty r)

and cmp_rty : Ast.rty -> Ll.ty = function
  | Ast.RString  -> I8
  | Ast.RArray u -> Struct [I64; Array(0, cmp_ty u)]
  | Ast.RFun (ts, t) ->
      let args, ret = cmp_fty (ts, t) in
      Fun (args, ret)

and cmp_ret_ty : Ast.ret_ty -> Ll.ty = function
  | Ast.RetVoid  -> Void
  | Ast.RetVal t -> cmp_ty t

and cmp_fty (ts, r) : Ll.fty =
  List.map cmp_ty ts, cmp_ret_ty r


let typ_of_binop : Ast.binop -> Ast.ty * Ast.ty * Ast.ty = function
  | Add | Mul | Sub | Shl | Shr | Sar | IAnd | IOr -> (TInt, TInt, TInt)
  | Eq | Neq | Lt | Lte | Gt | Gte -> (TInt, TInt, TBool)
  | And | Or -> (TBool, TBool, TBool)

let typ_of_unop : Ast.unop -> Ast.ty * Ast.ty = function
  | Neg | Bitnot -> (TInt, TInt)
  | Lognot       -> (TBool, TBool)

(* Compiler Invariants

   The LLVM IR type of a variable (whether global or local) that stores an Oat
   array value (or any other reference type, like "string") will always be a
   double pointer.  In general, any Oat variable of Oat-type t will be
   represented by an LLVM IR value of type Ptr (cmp_ty t).  So the Oat variable
   x : int will be represented by an LLVM IR value of type i64*, y : string will
   be represented by a value of type i8**, and arr : int[] will be represented
   by a value of type {i64, [0 x i64]}**.  Whether the LLVM IR type is a
   "single" or "double" pointer depends on whether t is a reference type.

   We can think of the compiler as paying careful attention to whether a piece
   of Oat syntax denotes the "value" of an expression or a pointer to the
   "storage space associated with it".  This is the distinction between an
   "expression" and the "left-hand-side" of an assignment statement.  Compiling
   an Oat variable identifier as an expression ("value") does the load, so
   cmp_exp called on an Oat variable of type t returns (code that) generates a
   LLVM IR value of type cmp_ty t.  Compiling an identifier as a left-hand-side
   does not do the load, so cmp_lhs called on an Oat variable of type t returns
   and operand of type (cmp_ty t)*.  Extending these invariants to account for
   array accesses: the assignment e1[e2] = e3; treats e1[e2] as a
   left-hand-side, so we compile it as follows: compile e1 as an expression to
   obtain an array value (which is of pointer of type {i64, [0 x s]}* ).
   compile e2 as an expression to obtain an operand of type i64, generate code
   that uses getelementptr to compute the offset from the array value, which is
   a pointer to the "storage space associated with e1[e2]".

   On the other hand, compiling e1[e2] as an expression (to obtain the value of
   the array), we can simply compile e1[e2] as a left-hand-side and then do the
   load.  So cmp_exp and cmp_lhs are mutually recursive.  [[Actually, as I am
   writing this, I think it could make sense to factor the Oat grammar in this
   way, which would make things clearer, I may do that for next time around.]]


   Consider globals7.oat

   /--------------- globals7.oat ------------------
   global arr = int[] null;

   int foo() {
     var x = new int[3];
     arr = x;
     x[2] = 3;
     return arr[2];
   }
   /------------------------------------------------

   The translation (given by cmp_ty) of the type int[] is {i64, [0 x i64}* so
   the corresponding LLVM IR declaration will look like:

   @arr = global { i64, [0 x i64] }* null

   This means that the type of the LLVM IR identifier @arr is {i64, [0 x i64]}**
   which is consistent with the type of a locally-declared array variable.

   The local variable x would be allocated and initialized by (something like)
   the following code snippet.  Here %_x7 is the LLVM IR uid containing the
   pointer to the "storage space" for the Oat variable x.

   %_x7 = alloca { i64, [0 x i64] }*                              ;; (1)
   %_raw_array5 = call i64*  @oat_alloc_array(i64 3)              ;; (2)
   %_array6 = bitcast i64* %_raw_array5 to { i64, [0 x i64] }*    ;; (3)
   store { i64, [0 x i64]}* %_array6, { i64, [0 x i64] }** %_x7   ;; (4)

   (1) note that alloca uses cmp_ty (int[]) to find the type, so %_x7 has
       the same type as @arr

   (2) @oat_alloc_array allocates len+1 i64's

   (3) we have to bitcast the result of @oat_alloc_array so we can store it
        in %_x7

   (4) stores the resulting array value (itself a pointer) into %_x7

  The assignment arr = x; gets compiled to (something like):

  %_x8 = load { i64, [0 x i64] }*, { i64, [0 x i64] }** %_x7     ;; (5)
  store {i64, [0 x i64] }* %_x8, { i64, [0 x i64] }** @arr       ;; (6)

  (5) load the array value (a pointer) that is stored in the address pointed
      to by %_x7

  (6) store the array value (a pointer) into @arr

  The assignment x[2] = 3; gets compiled to (something like):

  %_x9 = load { i64, [0 x i64] }*, { i64, [0 x i64] }** %_x7      ;; (7)
  %_index_ptr11 = getelementptr { i64, [0 x  i64] },
                  { i64, [0 x i64] }* %_x9, i32 0, i32 1, i32 2   ;; (8)
  store i64 3, i64* %_index_ptr11                                 ;; (9)

  (7) as above, load the array value that is stored %_x7

  (8) calculate the offset from the array using GEP

  (9) store 3 into the array

  Finally, return arr[2]; gets compiled to (something like) the following.
  Note that the way arr is treated is identical to x.  (Once we set up the
  translation, there is no difference between Oat globals and locals, except
  how their storage space is initially allocated.)

  %_arr12 = load { i64, [0 x i64] }*, { i64, [0 x i64] }** @arr    ;; (10)
  %_index_ptr14 = getelementptr { i64, [0 x i64] },
                 { i64, [0 x i64] }* %_arr12, i32 0, i32 1, i32 2  ;; (11)
  %_index15 = load i64, i64* %_index_ptr14                         ;; (12)
  ret i64 %_index15

  (10) just like for %_x9, load the array value that is stored in @arr

  (11)  calculate the array index offset

  (12) load the array value at the index

*)

(* Global initialized arrays:

  There is another wrinkle: To compile global initialized arrays like in the
  globals4.oat, it is helpful to do a bitcast once at the global scope to
  convert the "precise type" required by the LLVM initializer to the actual
  translation type (which sets the array length to 0).  So for globals4.oat,
  the arr global would compile to (something like):

  @arr = global { i64, [0 x i64] }* bitcast
           ({ i64, [4 x i64] }* @_global_arr5 to { i64, [0 x i64] }* )
  @_global_arr5 = global { i64, [4 x i64] }
                  { i64 4, [4 x i64] [ i64 1, i64 2, i64 3, i64 4 ] }

*)



(* Some useful helper functions *)

(* Generate a fresh temporary identifier. Since OAT identifiers cannot begin
   with an underscore, these should not clash with any source variables *)
let gensym : string -> string =
  let c = ref 0 in
  fun (s:string) -> incr c; Printf.sprintf "_%s%d" s (!c)

(* Amount of space an Oat type takes when stored in the satck, in bytes.
   Note that since structured values are manipulated by reference, all
   Oat values take 8 bytes on the stack.
*)
let size_oat_ty (t : Ast.ty) = 8L

(* Generate code to allocate a zero-initialized array of source type TRef (RArray t) of the
   given size. Note "size" is an operand whose value can be computed at
   runtime *)
let oat_alloc_array (t:Ast.ty) (size:Ll.operand) : Ll.ty * operand * stream =
  let ans_id, arr_id = gensym "array", gensym "raw_array" in
  let ans_ty = cmp_ty @@ TRef (RArray t) in
  let arr_ty = Ptr I64 in
  ans_ty, Id ans_id, lift
    [ arr_id, Call(arr_ty, Gid "oat_alloc_array", [I64, size])
    ; ans_id, Bitcast(arr_ty, Id arr_id, ans_ty) ]

(* Compiles an expression exp in context c, outputting the Ll operand that will
   recieve the value of the expression, and the stream of instructions
   implementing the expression.

   Tips:
   - use the provided cmp_ty function!

   - string literals (CStr s) should be hoisted. You'll need to make sure
     either that the resulting gid has type (Ptr I8), or, if the gid has type
     [n x i8] (where n is the length of the string), convert the gid to a
     (Ptr I8), e.g., by using getelementptr.

   - use the provided "oat_alloc_array" function to implement literal arrays
     (CArr) and the (NewArr) expressions

*)

let rec cmp_exp (c:Ctxt.t) (exp:Ast.exp node) : Ll.ty * Ll.operand * stream =
  let bop_arith = function Ast.Add -> Ll.Add | Ast.Sub -> Ll.Sub | Ast.Mul -> Ll.Mul | _ -> Ll.Add in
  let bop_shift = function Ast.Shl -> Ll.Shl | Ast.Shr -> Ll.Lshr | Ast.Sar -> Ll.Ashr | _ -> Ll.Shl in
  let bop_bit   = function Ast.IAnd -> Ll.And | Ast.IOr -> Ll.Or | _ -> Ll.And in
  let cnd_cmp   = function
    | Ast.Eq -> Ll.Eq | Ast.Neq -> Ll.Ne
    | Ast.Lt -> Ll.Slt | Ast.Lte -> Ll.Sle
    | Ast.Gt -> Ll.Sgt | Ast.Gte -> Ll.Sge
    | _ -> Ll.Eq
  in
  match exp.elt with
  | Ast.CInt i   -> (Ll.I64, Ll.Const i, [])
  | Ast.CBool b  -> (Ll.I1,  Ll.Const (if b then 1L else 0L), [])
  | Ast.CNull r  -> (cmp_ty (Ast.TRef r), Ll.Null, [])
  | Ast.CStr s ->
      let gid = gensym "str" in
      let n = String.length s + 1 in
      let arr_ty = Ll.Array (n, Ll.I8) in
      let ptr_uid = gensym "strptr" in
      (Ll.Ptr Ll.I8, Ll.Id ptr_uid,
       [ G (gid, (arr_ty, Ll.GString s));
         I (ptr_uid, Ll.Bitcast (Ll.Ptr arr_ty, Ll.Gid gid, Ll.Ptr Ll.I8)) ])
  | Ast.Id x ->
      begin match Ctxt.lookup_function_option x c with
      | Some (fty, fop) -> (fty, fop, [])
      | None ->
          let (pty, pop) = Ctxt.lookup x c in
          match pty with
          | Ll.Ptr tau ->
              let u = gensym ("ld_" ^ x) in
              (tau, Ll.Id u, [ I (u, Ll.Load (pty, pop)) ])
          | _ -> failwith "id expects pointer"
      end

  | Ast.Uop (Ast.Neg, e) ->
      let (_t, o, code) = cmp_exp c e in
      let u = gensym "neg" in
      (Ll.I64, Ll.Id u, I (u, Ll.Binop (Ll.Sub, Ll.I64, Ll.Const 0L, o)) :: code)
  | Ast.Uop (Ast.Bitnot, e) ->
      let (_t, o, code) = cmp_exp c e in
      let u = gensym "bnot" in
      (Ll.I64, Ll.Id u, I (u, Ll.Binop (Ll.Xor, Ll.I64, o, Ll.Const (-1L))) :: code)
  | Ast.Uop (Ast.Lognot, e) ->
      let (_t, o, code) = cmp_exp c e in
      let u = gensym "lnot" in
      (Ll.I1, Ll.Id u, I (u, Ll.Binop (Ll.Xor, Ll.I1, o, Ll.Const 1L)) :: code)

  | Ast.Bop (b, e1, e2) ->
      let (_t1, o1, c1) = cmp_exp c e1 in
      let (_t2, o2, c2) = cmp_exp c e2 in
      begin match b with
      | Ast.Add | Ast.Sub | Ast.Mul ->
          let u = gensym "arith" in
          (Ll.I64, Ll.Id u, I (u, Ll.Binop (bop_arith b, Ll.I64, o1, o2)) :: (c2 @ c1))
      | Ast.Shl | Ast.Shr | Ast.Sar ->
          let u = gensym "shift" in
          (Ll.I64, Ll.Id u, I (u, Ll.Binop (bop_shift b, Ll.I64, o1, o2)) :: (c2 @ c1))
      | Ast.IAnd | Ast.IOr ->
          let u = gensym "ibit" in
          (Ll.I64, Ll.Id u, I (u, Ll.Binop (bop_bit b, Ll.I64, o1, o2)) :: (c2 @ c1))
      | Ast.And | Ast.Or ->
          let u = gensym "lbool" in
          let bop = if b = Ast.And then Ll.And else Ll.Or in
          (Ll.I1, Ll.Id u, I (u, Ll.Binop (bop, Ll.I1, o1, o2)) :: (c2 @ c1))
      | Ast.Eq | Ast.Neq | Ast.Lt | Ast.Lte | Ast.Gt | Ast.Gte ->
          let u = gensym "cmp" in
          (Ll.I1, Ll.Id u, I (u, Ll.Icmp (cnd_cmp b, Ll.I64, o1, o2)) :: (c2 @ c1))
      end

  | Ast.Call (fexp, args) ->
      let (fty, fop, fcode) = cmp_exp c fexp in
      (match fty with
       | Ll.Ptr (Ll.Fun (_arg_tys, ret_ty)) ->
           let arg_infos = List.map (fun a -> cmp_exp c a) args in
           let arg_code = List.concat (List.map (fun (_,_,code)->code) arg_infos) in
           let call_args = List.map (fun (t,o,_) -> (t,o)) arg_infos in
           let u = gensym "call" in
           (ret_ty, Ll.Id u, I (u, Ll.Call (ret_ty, fop, call_args)) :: (arg_code @ fcode))
       | _ -> failwith "call target not a function pointer")

  | Ast.CArr (elt_ty_oat, es) ->
      let elt_ty = cmp_ty elt_ty_oat in
      let elems = List.map (cmp_exp c) es in
      let elem_codes = List.concat (List.map (fun (_,_,cd) -> cd) elems) in
      let n = List.length es in
      let arr_ll_ty, arr_op, alloc_code = oat_alloc_array elt_ty_oat (Ll.Const (Int64.of_int n)) in
      let store_stream =
        List.mapi (fun i (_t, o, _) ->
          let gep_uid = gensym "index_ptr" in
          let su = gensym "st" in
          [ I (su, Ll.Store (elt_ty, o, Ll.Id gep_uid))
          ; I (gep_uid, Ll.Gep (arr_ll_ty, arr_op,
                                [ Ll.Const 0L; Ll.Const 1L; Ll.Const (Int64.of_int i) ]))
          ]
        ) elems |> List.concat
      in
      (arr_ll_ty, arr_op, store_stream @ alloc_code @ elem_codes)

  | Ast.NewArr (elt_ty_oat, sz_exp) ->
      let (_t_sz, sz_op, sz_code) = cmp_exp c sz_exp in
      let arr_ll_ty, arr_op, alloc_code = oat_alloc_array elt_ty_oat sz_op in
      (arr_ll_ty, arr_op, alloc_code @ sz_code)

  | Ast.Index (arr_exp, idx_exp) ->
      let (arr_t, arr_o, arr_code) = cmp_exp c arr_exp in
      let (_tidx, idx_o, idx_code) = cmp_exp c idx_exp in
      let elt_ty =
        match arr_t with
        | Ll.Ptr (Ll.Struct [Ll.I64; Ll.Array (0, et)]) -> et
        | _ -> failwith "indexing non-array value"
      in
      let gep_uid = gensym "index_ptr" in
      let ld_uid = gensym "index" in
      let gep_insn = I (gep_uid, Ll.Gep (arr_t, arr_o, [Ll.Const 0L; Ll.Const 1L; idx_o])) in
      let ld_insn  = I (ld_uid, Ll.Load (Ll.Ptr elt_ty, Ll.Id gep_uid)) in
      (elt_ty, Ll.Id ld_uid, ld_insn :: (gep_insn :: (idx_code @ arr_code)))



(* Compile a statement in context c with return typ rt. Return a new context,
   possibly extended with new local bindings, and the instruction stream
   implementing the statement.

   Left-hand-sides of assignment statements must either be OAT identifiers,
   or an index into some arbitrary expression of array type. Otherwise, the
   program is not well-formed and your compiler may throw an error.

   Tips:
   - for local variable declarations, you will need to emit Allocas in the
     entry block of the current function using the E() constructor.

   - don't forget to add a bindings to the context for local variable
     declarations

   - you can avoid some work by translating For loops to the corresponding
     While loop, building the AST and recursively calling cmp_stmt

   - you might find it helpful to reuse the code you wrote for the Call
     expression to implement the SCall statement

   - compiling the left-hand-side of an assignment is almost exactly like
     compiling the Id or Index expression. Instead of loading the resulting
     pointer, you just need to store to it!

 *)

let rec cmp_stmt (c:Ctxt.t) (rt:Ll.ty) (stmt:Ast.stmt node) : Ctxt.t * stream = match stmt.elt with
  | Ast.Ret None -> c, [T (Ll.Ret (Ll.Void, None))]
  | Ast.Ret (Some e) -> let (_, o, code) = cmp_exp c e in c, T (Ll.Ret (rt, Some o)) :: code

  | Ast.Decl (x, init) ->
      let (t, o, init_code) = cmp_exp c init in
      let slot = gensym x in
      let c' = Ctxt.add c x (Ll.Ptr t, Ll.Id slot) in
      let alloca = E (slot, Ll.Alloca t) in
      let store_uid = gensym "st_decl" in
      let store_insn = I (store_uid, Ll.Store (t, o, Ll.Id slot)) in
      let g_inits = List.filter (function G _ -> true | _ -> false) init_code in
      let local_inits = List.filter (function I _ -> true | _ -> false) init_code in
      c', alloca :: (g_inits @ local_inits @ [store_insn])

  | Ast.Assn (lhs, rhs) ->
      let (_tr, orhs, code_rhs) = cmp_exp c rhs in
      begin match lhs.elt with
      | Ast.Id x ->
          let (pty, pop) = Ctxt.lookup x c in
          begin match pty with
          | Ll.Ptr tau ->
              let su = gensym "st" in
              c, I (su, Ll.Store (tau, orhs, pop)) :: code_rhs
          | _ -> failwith "lhs not a pointer"
          end
      | Ast.Index (arr_e, idx_e) ->
          let (arr_t, arr_o, arr_code) = cmp_exp c arr_e in
          let (_tidx, idx_o, idx_code) = cmp_exp c idx_e in
          let elt_ty =
            match arr_t with
            | Ll.Ptr (Ll.Struct [Ll.I64; Ll.Array (0, et)]) -> et
            | _ -> failwith "array assignment to non-array"
          in
          let gep_uid = gensym "index_ptr" in
          let gep_insn = I (gep_uid, Ll.Gep (arr_t, arr_o, [Ll.Const 0L; Ll.Const 1L; idx_o])) in
          let su = gensym "st" in
          let lhs_code = gep_insn :: (idx_code @ arr_code) in
          c, I (su, Ll.Store (elt_ty, orhs, Ll.Id gep_uid)) :: (lhs_code @ code_rhs)
      | _ -> failwith "invalid assignment lhs"
      end

  | Ast.SCall (fexp, args) ->
    let (fty, fop, fcode) = cmp_exp c fexp in
    begin match fty with
    | Ll.Ptr (Ll.Fun (_ats, rty)) ->
        let arg_infos = List.map (fun a -> cmp_exp c a) args in
        let arg_code = List.concat (List.map (fun (_,_,cd)->cd) arg_infos) in
        let call_args = List.map (fun (t,o,_)-> (t,o)) arg_infos in
        let u = gensym "scall" in
        c, I (u, Ll.Call (rty, fop, call_args)) :: (arg_code @ fcode)
    | _ -> failwith "SCall target not function pointer"
    end

  | Ast.If (e, b_then, b_else) ->
    let then_lbl = gensym "then_lbl" in
    let else_lbl = gensym "else_lbl" in
    let post_lbl = gensym "post_lbl" in
    let test_lbl = gensym "test_lbl" in

    let (_, opn, con_stream) = cmp_exp c e in
    let (_, then_stream) = cmp_block c rt b_then in
    let (_, else_stream) = cmp_block c rt b_else in

    let stmt =
      [L post_lbl]

      @ [T (Ll.Br (post_lbl))]
      @ else_stream
      @ [L else_lbl]

      @ [T (Ll.Br (post_lbl))]
      @ then_stream
      @ [L then_lbl]

      @ [T (Ll.Cbr (Ll.Id test_lbl, then_lbl, else_lbl))]
      @ [I (test_lbl, Ll.Icmp (Ll.Eq, Ll.I1, opn, Ll.Const 1L))]
      @ con_stream
      in
    c, stmt

  | Ast.While (e, body) ->
    let pre_lbl  = gensym "while_pre" in
    let body_lbl = gensym "while_body" in
    let post_lbl = gensym "while_post" in
    let test_lbl = gensym "test_lbl" in

    let (_, opn, con_stream) = cmp_exp c e in
    let (_, body_stream) = cmp_block c rt body in

    let while_reverse =
      [L post_lbl]

      @ [T (Ll.Br (pre_lbl))]
      @ body_stream
      @ [L body_lbl]

      @ [T (Ll.Cbr (Ll.Id test_lbl, body_lbl, post_lbl))]
      @ [I (test_lbl, Ll.Icmp (Ll.Eq, Ll.I1, opn, Ll.Const 1L))]
      @ con_stream
      @ [L pre_lbl]
      @ [T (Ll.Br (pre_lbl))]
    in
    c, while_reverse

  | Ast.For (decls, cond_opt, up_opt, body) ->
    let pre_lbl  = gensym "for_pre" in
    let body_lbl = gensym "for_body" in
    let post_lbl = gensym "for_post" in
    let test_lbl = gensym "test_lbl" in

    let (c', decl_stream) =
      List.fold_left (fun (c, code) (x, init_exp) ->
        let (c, decl_code) = cmp_stmt c rt (Ast.no_loc (Ast.Decl (x, init_exp))) in
        (c, code >@ decl_code)
      ) (c, []) decls in

    let (_, opn, con_stream) = match cond_opt with
      | Some e -> cmp_exp c' e
      | None -> (Ll.I1, Const 0L, []) in
    let (_, up_stream) = match up_opt with
      | Some e -> cmp_stmt c' (Ll.I1) e
      | None -> (c', []) in
    let (_, body_stream) = cmp_block c' rt body in

    let stmt =
      [L post_lbl]

      @ [T (Ll.Br (pre_lbl))]
      @ up_stream
      @ body_stream
      @ [L body_lbl]

      @ [T (Ll.Cbr (Ll.Id test_lbl, body_lbl, post_lbl))]
      @ [I (test_lbl, Ll.Icmp (Ll.Eq, Ll.I1, opn, Ll.Const 1L))]
      @ con_stream
      @ [L pre_lbl]
      @ [T (Ll.Br (pre_lbl))]

      @ decl_stream
    in
    c', stmt

(* Compile a series of statements *)
and cmp_block (c:Ctxt.t) (rt:Ll.ty) (stmts:Ast.block) : Ctxt.t * stream =
  List.fold_left (fun (c, code) s ->
      let c, stmt_code = cmp_stmt c rt s in
      c, code >@ stmt_code
    ) (c,[]) stmts



(* Adds each function identifer to the context at an
   appropriately translated type.

   NOTE: The Gid of a function is just its source name
*)
let cmp_function_ctxt (c:Ctxt.t) (p:Ast.prog) : Ctxt.t =
    List.fold_left (fun c -> function
      | Ast.Gfdecl { elt={ frtyp; fname; args } } ->
         let ft = TRef (RFun (List.map fst args, frtyp)) in
         Ctxt.add c fname (cmp_ty ft, Gid fname)
      | _ -> c
    ) c p

(* Populate a context with bindings for global variables
   mapping OAT identifiers to LLVMlite gids and their types.

   Only a small subset of OAT expressions can be used as global initializers
   in well-formed programs. (The constructors starting with C).
*)
let cmp_global_ctxt (c:Ctxt.t) (p:Ast.prog) : Ctxt.t =
  let ty_of_gexp (e:Ast.exp node) : Ast.ty =
      match e.elt with
      | CNull r -> TRef r
      | CBool _ -> TBool
      | CInt _ -> TInt
      | CStr _ -> TRef RString
      | CArr (elt_ty, _inits) -> TRef (RArray elt_ty)
      | _ -> failwith "cmp_global_ctxt: non-constant global initializer"
    in
    let add_binding (c:Ctxt.t) (d:decl) =
      match d with
      | Ast.Gvdecl { elt = { name; init }; loc } -> Ctxt.add c name (Ptr (cmp_ty (ty_of_gexp init)), Gid name)
      | _ -> c
    in
    List.fold_left add_binding c p

(* Compile a function declaration in global context c. Return the LLVMlite cfg
   and a list of global declarations containing the string literals appearing
   in the function.

   You will need to
   1. Allocate stack space for the function parameters using Alloca
   2. Store the function arguments in their corresponding alloca'd stack slot
   3. Extend the context with bindings for function variables
   4. Compile the body of the function using cmp_block
   5. Use cfg_of_stream to produce a LLVMlite cfg from
 *)

 let cmp_fdecl (c:Ctxt.t) (f:Ast.fdecl node) : Ll.fdecl * (Ll.gid * Ll.gdecl) list =
   let { Ast.frtyp; fname = _; args; body } = f.elt in
   let ll_ret_ty = cmp_ret_ty frtyp in
   let ll_arg_tys = List.map (fun (t, _) -> cmp_ty t) args in
   let f_ty : Ll.fty = (ll_arg_tys, ll_ret_ty) in
   let param_uids = List.map (fun (_, x) -> gensym ("arg_" ^ x)) args in
   let params = List.map2 (fun (t, x) uid -> (cmp_ty t, x, uid)) args param_uids in

   let c_with_params, prologue =
     List.fold_left
       (fun (cacc, acc) (tll, x, uid) ->
          let slot = gensym ("_" ^ x) in
          let cacc = Ctxt.add cacc x (Ptr tll, Id slot) in
          let ealloca = E (slot, Alloca tll) in
          let estore  = E (gensym "st_param", Store (tll, Id uid, Id slot)) in
          (cacc, acc @ [ealloca; estore]))
       (c, [])
       params
   in

   let _, body_stream = cmp_block c_with_params ll_ret_ty body in
   let combined = prologue @ body_stream in

   let has_term = List.exists (function T _ -> true | _ -> false) combined in
   let final_stream =
     if has_term then combined
     else match ll_ret_ty with
          | Void -> combined @ [ T (Ret (Void, None)) ]
          | _ -> failwith "cmp_fdecl: missing return in non-void function"
   in

   let cfg, hoisted_globals = cfg_of_stream final_stream in
   ({ f_ty; f_param = param_uids; f_cfg = cfg }, hoisted_globals)



(* Compile a global initializer, returning the resulting LLVMlite global
   declaration, and a list of additional global declarations.

   Tips:
   - Only CNull, CBool, CInt, CStr, and CArr can appear as global initializers
     in well-formed OAT programs. Your compiler may throw an error for the other
     cases

   - OAT arrays are always handled via pointers. A global array of arrays will
     be an array of pointers to arrays emitted as additional global declarations.
*)

let rec cmp_gexp c (e:Ast.exp node) : Ll.gdecl * (Ll.gid * Ll.gdecl) list =
  match e.elt with
  | CNull r -> (cmp_ty (TRef r), GNull), []
  | CBool b -> (I1, GInt (if b then 1L else 0L)), []
  | CInt i -> (I64, GInt i), []
  | CStr s ->
      let gid = gensym "str" in
      let n = String.length s + 1 in
      let arr_ty = Array (n, I8) in
      let str_decl : Ll.gdecl = (arr_ty, GString s) in
      let init = GBitcast (Ptr arr_ty, GGid gid, Ptr I8) in
      (Ptr I8, init), [ (gid, str_decl) ]
  | CArr (elt_ty_oat, elems) ->
      let compiled = List.map (cmp_gexp c) elems in
      let elem_inits : (Ll.ty * Ll.ginit) list = List.map fst compiled in
      let extra_gs : (Ll.gid * Ll.gdecl) list = List.concat (List.map snd compiled) in
      let n = List.length elem_inits in
      let ll_elt_ty = cmp_ty elt_ty_oat in

      let elem_inits =
        List.map (fun (t_i, gi) ->
          if t_i = ll_elt_ty then (t_i, gi)
          else failwith "cmp_gexp: array element type mismatch"
        ) elem_inits
      in

      let precise_ty = Ll.Struct [ Ll.I64; Ll.Array (n, ll_elt_ty) ] in
      let precise_init =
        Ll.GStruct
          [ (Ll.I64, Ll.GInt (Int64.of_int n))
          ; (Ll.Array (n, ll_elt_ty), Ll.GArray elem_inits)
          ]
      in
      let payload_gid = gensym "global_arr" in
      let payload_decl : (Ll.gid * Ll.gdecl) = (payload_gid, (precise_ty, precise_init)) in
      let general_arr_ty = cmp_ty (Ast.TRef (Ast.RArray elt_ty_oat)) in
      let init =
        Ll.GBitcast (Ll.Ptr precise_ty, Ll.GGid payload_gid, general_arr_ty)
      in
      (general_arr_ty, init), (payload_decl :: extra_gs)
  | _ -> failwith "cmp_gexp: non-constant global initializer"

(* Oat internals function context ------------------------------------------- *)
let internals = [
    "oat_alloc_array",         Ll.Fun ([I64], Ptr I64)
  ]

(* Oat builtin function context --------------------------------------------- *)
let builtins =
  [ "array_of_string",  cmp_rty @@ RFun ([TRef RString], RetVal (TRef(RArray TInt)))
  ; "string_of_array",  cmp_rty @@ RFun ([TRef(RArray TInt)], RetVal (TRef RString))
  ; "length_of_string", cmp_rty @@ RFun ([TRef RString],  RetVal TInt)
  ; "string_of_int",    cmp_rty @@ RFun ([TInt],  RetVal (TRef RString))
  ; "string_cat",       cmp_rty @@ RFun ([TRef RString; TRef RString], RetVal (TRef RString))
  ; "print_string",     cmp_rty @@ RFun ([TRef RString],  RetVoid)
  ; "print_int",        cmp_rty @@ RFun ([TInt],  RetVoid)
  ; "print_bool",       cmp_rty @@ RFun ([TBool], RetVoid)
  ]

(* Compile a OAT program to LLVMlite *)
let cmp_prog (p:Ast.prog) : Ll.prog =
  (* add built-in functions to context *)
  let init_ctxt =
    List.fold_left (fun c (i, t) -> Ctxt.add c i (Ll.Ptr t, Gid i))
      Ctxt.empty builtins
  in
  let fc = cmp_function_ctxt init_ctxt p in

  (* build global variable context *)
  let c = cmp_global_ctxt fc p in

  (* compile functions and global variables *)
  let fdecls, gdecls =
    List.fold_right (fun d (fs, gs) ->
        match d with
        | Ast.Gvdecl { elt=gd } ->
           let ll_gd, gs' = cmp_gexp c gd.init in
           (fs, (gd.name, ll_gd)::gs' @ gs)
        | Ast.Gfdecl fd ->
           let fdecl, gs' = cmp_fdecl c fd in
           (fd.elt.fname,fdecl)::fs, gs' @ gs
      ) p ([], [])
  in

  (* gather external declarations *)
  let edecls = internals @ builtins in
  { tdecls = []; gdecls; fdecls; edecls }
