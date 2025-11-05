%{
open Ast

let loc (startpos:Lexing.position) (endpos:Lexing.position) (elt:'a) : 'a node =
  { elt ; loc=Range.mk_lex_range startpos endpos }

%}

/* Declare your tokens here. */
%token EOF
%token <int64>  INT
%token NULL
%token <bool> BOOL
%token <string> STRING
%token <string> IDENT


%token TINT     /* int */
%token TBOOL    /* bool */
%token TVOID    /* void */
%token TSTRING  /* string */
%token ARROWRIGHT /* -> */
%token NEW     /* new */
%token IF       /* if */
%token ELSE     /* else */
%token WHILE    /* while */
%token FOR     /* for */
%token RETURN   /* return */
%token VAR      /* var */
%token SEMI     /* ; */
%token COMMA    /* , */
%token LBRACE   /* { */
%token RBRACE   /* } */
%token LSHIFT  /* << */
%token RSHIFT  /* >> */
%token RSHIFTAR /* >>> */
%token PLUS     /* + */
%token DASH     /* - */
%token STAR     /* * */
%token EQEQ     /* == */
%token EQ       /* = */
%token LT      /* < */
%token LE      /* <= */
%token GT     /* > */
%token GE     /* >= */
%token NEQ    /* != */
%token LAND    /* & */
%token LOR    /* | */
%token BITAND  /* [&] */
%token BITOR   /* [|] */
%token LPAREN   /* ( */
%token RPAREN   /* ) */
%token LBRACKET /* [ */
%token RBRACKET /* ] */
%token TILDE    /* ~ */
%token BANG     /* ! */
%token GLOBAL   /* global */

%left  BITOR                        /* [|] 20 */
%left  BITAND                       /* [&] 30 */
%left  LOR                          /* |   40 */
%left  LAND                         /* &   50 */
%nonassoc EQEQ NEQ                  /* 60 */
%nonassoc LT LE GT GE               /* 70 */
%left  LSHIFT RSHIFT RSHIFTAR       /* 80 */
%left  PLUS DASH                    /* 90 */
%left  STAR                         /* 100 */
%nonassoc BANG
%nonassoc TILDE
%nonassoc LBRACKET
%nonassoc LPAREN

/* ---------------------------------------------------------------------- */

%start prog
%start exp_top
%start stmt_top
%type <Ast.exp Ast.node> exp_top
%type <Ast.stmt Ast.node> stmt_top

%type <Ast.prog> prog
%type <Ast.exp Ast.node> exp
%type <Ast.stmt Ast.node> stmt
%type <Ast.block> block
%type <Ast.ty> ty
%%

exp_top:
  | e=exp EOF { e }

stmt_top:
  | s=stmt EOF { s }

prog:
  | p=list(decl) EOF  { p }

decl:
  | GLOBAL name=IDENT EQ init=gexp SEMI
    { Gvdecl (loc $startpos $endpos { name; init }) }
  | frtyp=ret_ty fname=IDENT LPAREN args=arglist RPAREN body=block
    { Gfdecl (loc $startpos $endpos { frtyp; fname; args; body }) }

arglist:
  | l=separated_list(COMMA, pair(ty,IDENT)) { l }

ty:
  | TINT   { TInt }
  | TBOOL  { TBool }
  | r=rtyp { TRef r }



%inline ret_ty:
  | TVOID  { RetVoid }
  | t=ty   { RetVal t }

%inline rtyp:
  | TSTRING { RString }
  | t=ty LBRACKET RBRACKET { RArray t }

%inline bop:
  | PLUS   { Add }
  | DASH   { Sub }
  | STAR   { Mul }
  | EQEQ   { Eq }
  | NEQ    { Neq }
  | LT     { Lt }
  | LE     { Lte }
  | GT     { Gt }
  | GE     { Gte }
  | LSHIFT { Shl }
  | RSHIFT { Shr }
  | RSHIFTAR { Sar }
  | LAND   { And }
  | LOR    { Or }
  | BITAND { IAnd }
  | BITOR  { IOr }

%inline uop:
  | DASH  { Neg }
  | BANG  { Lognot }
  | TILDE { Bitnot }

gexp:
  | t=rtyp NULL  { loc $startpos $endpos @@ CNull t }
  | i=INT      { loc $startpos $endpos @@ CInt i }
  | s=STRING { loc $startpos $endpos @@ CStr s }
  | b=BOOL              { loc $startpos $endpos @@ CBool b }
  | NEW t=ty LBRACKET RBRACKET LBRACE s=separated_list(COMMA, gexp) RBRACE
                        {loc $startpos $endpos @@ CArr (t,s) }
lhs:
  | id=IDENT            { loc $startpos $endpos @@ Id id }
  | e=exp LBRACKET i=exp RBRACKET
                        { loc $startpos $endpos @@ Index (e, i) }

exp:
  | i=INT               { loc $startpos $endpos @@ CInt i }
  | b=BOOL              { loc $startpos $endpos @@ CBool b }
  | t=rtyp NULL           { loc $startpos $endpos @@ CNull t }
  | e1=exp b=bop e2=exp { loc $startpos $endpos @@ Bop (b, e1, e2) }
  | u=uop e=exp         { loc $startpos $endpos @@ Uop (u, e) }
  | id=IDENT            { loc $startpos $endpos @@ Id id }
  | s=STRING            { loc $startpos $endpos @@ CStr s }
  | e=exp LBRACKET i=exp RBRACKET
                        { loc $startpos $endpos @@ Index (e, i) }
  | e=exp LPAREN es=separated_list(COMMA, exp) RPAREN
                        { loc $startpos $endpos @@ Call (e, es) }
  | LPAREN e=exp RPAREN { e }
  | NEW t=ty LBRACKET RBRACKET LBRACE s=separated_list(COMMA, gexp) RBRACE
                        {loc $startpos $endpos @@ CArr (t,s) }
  | NEW t=ty LBRACKET e=exp RBRACKET
                        { loc $startpos $endpos @@ NewArr (t, e) }

vdecl:
  | VAR id=IDENT EQ init=exp { (id, init) }

vdecls:
  | es=separated_list(COMMA, vdecl) {es}

fty:
  | LPAREN separated_list(COMMA,ty) ARROWRIGHT ret_ty {}

stmt:
  | d=vdecl SEMI        { loc $startpos $endpos @@ Decl(d) }
  | p=lhs EQ e=exp SEMI { loc $startpos $endpos @@ Assn(p,e) }
  | e=exp LPAREN es=separated_list(COMMA, exp) RPAREN SEMI
                        { loc $startpos $endpos @@ SCall (e, es) }
  | ifs=if_stmt         { ifs }
  | RETURN SEMI         { loc $startpos $endpos @@ Ret(None) }
  | RETURN e=exp SEMI   { loc $startpos $endpos @@ Ret(Some e) }
  | FOR LPAREN v=vdecls SEMI o1=option(exp) SEMI o2=option(stmt) RPAREN la=block
    {loc $startpos $endpos @@ For(v,o1,o2,la) }
  | WHILE LPAREN e=exp RPAREN b=block
                        { loc $startpos $endpos @@ While(e, b) }

block:
  | LBRACE stmts=list(stmt) RBRACE { stmts }

if_stmt:
  | IF LPAREN e=exp RPAREN b1=block b2=else_stmt
    { loc $startpos $endpos @@ If(e,b1,b2) }

else_stmt:
  | (* empty *)       { [] }
  | ELSE b=block      { b }
  | ELSE ifs=if_stmt  { [ ifs ] }
