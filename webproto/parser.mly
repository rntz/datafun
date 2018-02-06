%{
open Sigs
open Util
open Ast

let getpos () = (Parsing.symbol_start_pos (), Parsing.symbol_end_pos ())
let rangepos n m = (Parsing.rhs_start_pos n, Parsing.rhs_end_pos m)
%}

/* punctuation */
%token DOT
%token COMMA
%token UNDER
%token SEMI
%token COLON
%token BANG
%token PLUS
%token DASH
%token ASTERISK
%token SLASH
%token ARROW                    /* -> */
%token DBLARROW                 /* => */
%token BAR

%token LE                       /* <= */
%token LT                       /* < */
%token GE                       /* >= */
%token GT                       /* > */
%token EQ                       /* = */
%token EQEQ                     /* == */

/* brackets */
%token RPAREN
%token LPAREN
%token RBRACE
%token LBRACE
%token RBRACK
%token LBRACK

/* type tokens */
%token <Ast.base> BASE

/* decl tokens */
%token TYPE
%token DEF

/* expression tokens */
%token THE
%token LET
%token IN
%token END
%token EMPTY
%token OR
%token FOR
%token AS
%token FN
%token CASE
%token BOX
%token UNBOX
%token IF
%token THEN
%token ELSE

/* atoms */
%token <Ast.lit> LITERAL
/* lowercase & uppercase identifiers */
%token <string> ID
%token <string> CAPID

%token EOF


/* ---------- Associativity / fixity ---------- */
/* %nonassoc IN
 * %nonassoc THEN ELSE
 * %nonassoc IF
 * %nonassoc LET
 * %right CONS
 * %left COLON
 * %right DOUBLECOLON
 * %right OR
 * %right ANDAND
 * %left EQUAL LT LEQ GEQ GT
 * %left PLUS MINUS
 * %left TIMES */


/* ---------- Types for nonterminals ---------- */
%type <Ast.tp> tp
%type <Ast.tp> test_tp

%type <Ast.pat> pat
%type <Ast.pat> test_pat

%type <Ast.loc Ast.exp> exp
%type <Ast.loc Ast.exp> test_exp

%start tp test_tp pat test_pat exp test_exp


%%
/* ---------- Syntax of types ---------- */
test_tp : tp EOF {$1};

tp : tp_arrow { $1 } | tp_summands { Sum $1 };

/* currently there is no way to write the empty sum type */
tp_summands :
| CAPID tp_atom                 { [$1,$2] }
| CAPID tp_atom BAR tp_summands { ($1,$2)::$4 };

tp_arrow : tp_product           { $1 }
| tp_product DBLARROW tp_arrow  { Arrow($1, $3) }
| tp_product ARROW tp_arrow     { Arrow(Box $1, $3) };

tp_product : tp_atom       { $1 }
| tp_atom COMMA tp_factors { Product ($1 :: $3) };

tp_factors :               { [] }
| tp_atom                  { [$1] }
| tp_atom COMMA tp_factors { $1 :: $3 };

tp_atom :
| LPAREN RPAREN     { Product [] }
| BASE              { Base $1 }
| BANG tp_atom      { Box $2 }
| LBRACE tp RBRACE  { Set $2 }
| LPAREN tp RPAREN  { $2 };


/* ---------- Syntax of patterns ---------- */
test_pat : pat EOF {$1};

pat : pat_app            { $1 }
| pat_app COMMA pat_apps { PTuple($1::$3) };

pat_apps :                  { [] }
| pat_app                   { [$1] }
| pat_app COMMA pat_apps    { $1::$3 };

pat_app : pat_atom { $1 }
| CAPID pat_atom { PTag($1, $2) };

pat_atom :
| BANG pat_atom      { PBox $2 }
| UNDER              { PWild }
| ID                 { PVar $1 }
| LITERAL            { PLit $1 }
| LPAREN pat RPAREN  { $2 };


/* ---------- Syntax of expressions ---------- */
test_exp : exp EOF {$1};
exp : expr { E(getpos(), $1) };
exp_infix: expr_infix { E(getpos(), $1) };
exp_app: expr_app { E(getpos(), $1) };
exp_atom: expr_atom { E(getpos(), $1) };

exps : {[]} | exp_app {[$1]} | exp_app COMMA exps; {$1::$3};

expr : expr_infix { $1 }
| THE tp_atom exp { The($2,$3) }
| pat_atom AS exp { Fix($1,$3) }
/* TODO: let-expressions */
| FN args DBLARROW exp { Lam($2,$4) }
| FOR LPAREN comps RPAREN exp { For($3, $5) }
| CASE exp_infix branches { Case($2,$3) }
;

expr_infix : expr_app { $1 }
| expr_disjuncts { Lub($1) }
| exp_app expr_disjuncts { Lub($1::$2) }
| expr_tuple { Tuple($1) }
;

expr_disjuncts : OR exp_app expr_disjuncts_empty { $2::$3 };
expr_disjuncts_empty : {[]} | expr_disjuncts {$1};

expr_tuple : exp_app COMMA expr_tuple_empty { $1::$3 };
expr_tuple_empty : {[]} | exp_app {[$1]} | expr_tuple {$1};

expr_app : expr_atom { $1 }
| exp_app exp_atom { App($1,$2) }
| CAPID exp_atom { Tag($1,$2) }
| BOX exp_atom { Box($2) }
| UNBOX exp_atom { Unbox($2) }
;

expr_atom :
| ID        { Var $1 }
| LITERAL   { Lit $1 }
| EMPTY     { Lub [] }
| LBRACE exps RBRACE { MkSet $2 }
;

/* TODO: args, comps, branches */
args : | pat { [$1] } ;
comps : { [] };
branches: { [] };
