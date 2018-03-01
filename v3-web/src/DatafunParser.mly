%{
open Util
open Ast
let map f g (x,y) = Option.(x => f, y => g)
%}

%token
/* punctuation */ DOT COMMA UNDER SEMI COLON BANG PLUS DASH ASTERISK SLASH
PERCENT ARROW DBLARROW DBLARROWMINUS BAR LE LT GE GT EQ EQEQ RPAREN LPAREN
RBRACE LBRACE RBRACK LBRACK
/* keywords */ TYPE DEF THE LET IN END EMPTY OR FOR DO FIX AS FN CASE IF THEN
ELSE SHADOW
/* end of file */ EOF

%token <Ast.base> BASE          /* base types */
%token <Ast.lit> LITERAL        /* literals */
%token <string> ID CAPID        /* lower/uppercase identifiers */

/* ---------- Associativity / fixity ---------- */
// This seems to force "Foo x" (and similar) to parse as
//
//     `Tag "Foo" (`Var "x")
//
// as desired, rather than as
//
//     `App (`Tag "Foo" (`Tuple [])) (`Var "x")
//
%right CAPID UNDER LPAREN LITERAL LBRACE ID EMPTY

/* ---------- Types for nonterminals ---------- */
%start <unit> unused
%start <Ast.tp> tp test_tp
%start <Ast.pat> pat test_pat
%start <Ast.expr> exp test_exp
%start <Ast.pat option * Ast.expr option> patexp test_patexp
%start <Ast.expr Ast.decl list> decls test_decls
%start <Repl.cmd> replcmd

%%
/* Argh. */
unused: ASTERISK DO DOT END EQEQ FIX GE GT LE LT SLASH {()};

/* ---------- The repl ---------- */
replcmd:
| decls SEMI { `Decls($1) }
| exp SEMI { `Expr($1) }
| PERCENT ID SEMI { `Cmd($2) }

/* ---------- Types ---------- */
test_tp: tp EOF { $1 }
tp:
| tp_arrow {$1}
| separated_nonempty_list(BAR, CAPID tp_atom {$1,$2}) {`Sum $1}

tp_arrow: tp_product                { $1 }
| tp_product DBLARROW tp_arrow      { `Fn(`Id, $1, $3) }
| tp_product DBLARROWMINUS tp_arrow { `Fn(`Op, $1, $3) }
| tp_product ARROW tp_arrow         { `Fn(`Iso, $1, $3) }

tp_product: tp_atom { $1 }
| tp_atom COMMA { `Tuple [$1] }
| tp_atom nonempty_list(COMMA tp_atom { $2 }) { `Tuple($1::$2) }

tp_atom:
| LPAREN RPAREN     { `Tuple [] }
| BASE              { $1 :> tp }
| ID                { `Name $1 }
| LBRACE tp RBRACE  { `Set $2 }
| LPAREN tp RPAREN  { $2 }

/* ---------- Decls ---------- */
test_decls: decls EOF {$1}
/* decls: SEMI* separated_list(SEMI*,decl) {$2} */
decls: list(decl) {$1}
decl:
| TYPE ID EQ tp {Type($2,$4) }
| DEF option(tone_char) pat_atom option(COLON tp {$2}) def_exp { Def($3,$2,$4,$5) }
| SHADOW list(ID) { Shadow $2 }

tone_char: PLUS { `Id } | DASH { `Op } | BANG { `Iso }

def_exp:
| EQ exp { $2 }
| fnexpr { (($symbolstartpos,$endpos), $1) }

fnexpr: FN args DBLARROW exp { `Lam($2,$4) }
args: list(pat_atom) {$1}

/* ---------- Comprehensions ---------- */
comps: separated_list(COMMA, comp) {$1}
comp:
| exp_app { When $1 }
| pat_app IN exp_app { In($1,$3) }
| exp_app LBRACK pat RBRACK { In($3,$1) }

/* ---------- Patterns/expressions ----------
 *
 * We collapse these as an awful hack to make parsing comprehensions LR(1).
 * In particular, both `PAT in EXPR` and `EXPR` are valid comprehensions.
 * With PAT and EXPR as separate productions, menhir complains and gives us
 * a reduce/reduce conflict. This way it Just Works, at the expense of having
 * to manually "parse both ways at once", so to speak.
 */
%inline annot(X): X
    { match $1 with
      | None, None -> $syntaxerror
      | x, None    -> x, None
      | x, Some y  -> x, Some (($symbolstartpos,$endpos), y) }
%inline getPat(X): X { match fst $1 with | Some x -> x | None -> $syntaxerror }
%inline getExp(X): X { match snd $1 with | Some x -> x | None -> $syntaxerror }

test_patexp: patexp EOF {$1}; test_exp: exp EOF {$1}; test_pat: pat EOF {$1}
patexp: annot(pe) {$1}
patexp_infix: annot(pe_infix) {$1}
patexp_app: annot(pe_app) {$1}
patexp_atom: annot(pe_atom) {$1}

pat: getPat(patexp) {$1}; exp: getExp(patexp) {$1}
pat_infix: getPat(patexp_infix) {$1}; exp_infix: getExp(patexp_infix) {$1}
pat_app: getPat(patexp_app) {$1}; exp_app: getExp(patexp_app) {$1}
pat_atom: getPat(patexp_atom) {$1}; exp_atom: getExp(patexp_atom) {$1}

pe: pe_infix {$1} | e {None, Some $1}
e:
| THE tp_atom exp    { `The($2,$3) }
| pat_infix AS exp   { `Fix($1,$3) }
| fnexpr             { $1 }
| LET decls IN exp   { `Let($2,$4) }
| FOR LPAREN c=comps RPAREN e=exp { `For(c,e) }
/* TODO: use precedence(?) to resolve the shift/reduce conflict here */
| CASE exp_infix nonempty_list(BAR pat DBLARROW exp {$2,$4}) { `Case($2,$3) }
| IF exp THEN exp ELSE exp
  { `Case($2, [(`Bool true), $4; (`Bool false), $6]) }

pe_infix: pe_app {$1}
| patexp_app nonempty_list(COMMA patexp_app {$2})
  { let (xs,ys) = List.split ($1::$2) in
    let tuple x = `Tuple x in   (* we need let-generalization here *)
    map tuple tuple Option.(list xs, list ys) }
/* expressions only */
| ioption(OR) exp_app nonempty_list(OR exp_app {$2})
  { None, Some (`Lub ($2::$3)) }

pe_app: pe_atom {$1}
| CAPID patexp_atom { map (fun x -> `Tag($1,x)) (fun x -> `Tag($1,x)) $2 }
/* expressions only */
| exp_app exp_atom { None, Some (`App ($1,$2)) }

pe_atom:
| CAPID { Some (`Tag ($1, `Tuple [])),
          Some (`Tag ($1, (($symbolstartpos,$endpos), `Tuple []))) }
| ID        { Some (`Var $1), Some (`Var $1) }
| LITERAL   { Some ($1 :> pat), Some ($1: lit :> expr expF) }
| LPAREN RPAREN { Some (`Tuple []), Some (`Tuple []) }
| LPAREN patexp_app COMMA RPAREN
  { map (fun x -> `Tuple [x]) (fun x -> `Tuple [x]) $2 }
| LPAREN pe RPAREN { $2 }
/* patterns only */
| UNDER     { Some `Wild, None }
/* expressions only */
| EMPTY     { None, Some (`Lub []) }
| LBRACE separated_list(COMMA, exp_app) RBRACE { None, Some (`Set $2) }
| LBRACE exp_app BAR comps RBRACE
  { None, Some (`For ($4, (($symbolstartpos,$endpos), `Set([$2])))) }
