%{
open Util
open Ast

let map f g (x,y) = (Option.map f x, Option.map g y)
%}

%token
/* punctuation */ DOT COMMA UNDER SEMI COLON BANG PLUS DASH ASTERISK SLASH ARROW
DBLARROW BAR LE LT GE GT EQ EQEQ RPAREN LPAREN RBRACE LBRACE RBRACK LBRACK
/* keywords */ TYPE DEF THE LET IN END EMPTY OR FOR DO FIX AS FN CASE BOX UNBOX
IF THEN ELSE
/* end of file */ EOF

%token <Ast.base> BASE          /* base types */
%token <Ast.lit> LITERAL        /* literals */
%token <string> ID CAPID        /* lower/uppercase identifiers */

/* ---------- Associativity / fixity ---------- */
// This seems to force "Foo x" (and similar) to parse as
//
//     Tag "Foo" (Var "x")
//
// rather than
//
//     App (Tag "Foo" (Tuple [])) (Var "x")
//
%right CAPID LITERAL LPAREN LBRACE ID EMPTY

/* ---------- Types for nonterminals ---------- */
%start <unit> unused
%start <Ast.tp> tp test_tp
%start <Ast.pat> pat test_pat
%start <Ast.expr> exp test_exp
%start <Ast.expr Ast.decl list> decls test_decls

%%
/* Argh. */
unused: ASTERISK DASH DO DOT END EQEQ FIX GE GT LE LT PLUS SLASH
AS BOX CASE ELSE EMPTY FOR IF IN LBRACK RBRACK LET LITERAL OR THE THEN UNBOX UNDER
    {()};

/* ---------- Types ---------- */
test_tp: tp EOF { $1 }
tp:
| tp_arrow {$1}
| separated_nonempty_list(BAR, CAPID tp_atom {$1,$2}) {Sum $1}

tp_arrow: tp_product            { $1 }
| tp_product DBLARROW tp_arrow  { Arrow($1, $3) }
| tp_product ARROW tp_arrow     { Arrow(Box $1, $3) }

tp_product: tp_atom { $1 }
| tp_atom COMMA { Product [$1] }
| tp_atom nonempty_list(COMMA tp_atom { $2 }) { Product($1::$2) }

tp_atom:
| LPAREN RPAREN     { Product [] }
| BASE              { Base $1 }
| ID                { Name $1 }
| BANG tp_atom      { Box $2 }
| LBRACE tp RBRACE  { Set $2 }
| LPAREN tp RPAREN  { $2 }

/* ---------- Decls ---------- */
test_decls: decls EOF {$1}
decls: SEMI* separated_list(SEMI*,decl) {$2}
decl:
| TYPE ID EQ tp {Type($2,$4) }
| DEF pat_atom option(COLON tp {$2}) def_exp { Def($2,$3,$4) }

def_exp:
| EQ exp { $2 }
| fnexpr { E(($symbolstartpos,$endpos), $1) }

fnexpr: FN args DBLARROW exp { Lam($2,$4) }
args: list(pat_atom) {$1}

/* ---------- Patterns ---------- */
test_pat: pat EOF {$1}
pat: pat_app { $1 }
| pat_app nonempty_list(COMMA pat_app {$2}) { PTuple($1::$2) }

pat_app: pat_atom {$1}
| CAPID pat_atom { PTag($1,$2) }
| BOX pat_atom { PBox $2 }

pat_atom:
| ID { PVar $1 }
| UNDER { PWild }
| CAPID { PTag($1, PTuple []) }
| LITERAL { PLit $1 }
| LPAREN RPAREN { PTuple [] }
| LPAREN pat_app COMMA RPAREN { PTuple [$2] }
| LPAREN pat RPAREN { $2 }

/* ---------- Expressions ---------- */
%inline annot(X): X { E(($symbolstartpos,$endpos),$1) }

test_exp: exp EOF {$1}
exp: annot(expr) {$1}
exp_infix: annot(expr_infix) {$1}
exp_app: annot(expr_app) {$1}
exp_atom: annot(expr_atom) {$1}

expr: expr_infix {$1}
/* TODO: FOR, etc. */
| THE tp_atom exp { The($2,$3) }
| fnexpr { $1 }
| LET decls IN exp { Let($2,$4) }
/* TODO: resolve the shift-reduce conflict here */
| CASE exp_infix nonempty_list(BAR pat DBLARROW exp_infix {$2,$4}) { Case($2,$3) }
| IF exp THEN exp ELSE exp
  { Case($2, [PLit(LBool true), $4; PLit(LBool false), $6]) }
| do_exp { match $1 with E(_,e) -> e }

do_exp: DO exp { $2 }
| annot(comp do_exp {$1 $2}) { $1 }

expr_infix: expr_app {$1}
| exp_app nonempty_list(COMMA exp_app {$2}) { Tuple($1::$2) }
| exp_app nonempty_list(OR exp_app {$2}) { Lub($1::$2) }

expr_app: expr_atom {$1}
| CAPID exp_atom { Tag($1,$2) }
| BOX exp_atom { Box $2 }
| UNBOX exp_atom { Unbox $2 }
| exp_app exp_atom { App($1,$2) }

expr_atom:
| ID { Var $1 }
| CAPID { Tag($1, E(($symbolstartpos,$endpos), Tuple [])) }
| LITERAL { Lit $1 }
| EMPTY { Lub [] }
| LBRACE separated_list(COMMA,exp_app) RBRACE { MkSet $2 }
| LPAREN RPAREN { Tuple [] }
| LPAREN exp_app COMMA RPAREN { Tuple [$2] }
| LPAREN expr RPAREN { $2 }
/* TODO: set comprehensions */

/* ---------- Comprehensions ---------- */
comp: FIX pat { fun e -> Fix($2,e) }
| IF exp_infix { fun e -> For([When $2], e) }
| FOR separated_list(COMMA, patinexp) { fun e -> For($2, e) }

/* arg, another problem! */
patinexp:
| pat_app IN exp_app { In($1,$3) }
| exp_app LBRACK pat RBRACK { In($3,$1) }
