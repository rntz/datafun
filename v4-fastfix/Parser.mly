%{
    open Util open Types
    module B = Backend
%}

// TODO: filter this to only what I need
%token
/* punctuation */ AT DOT COMMA UNDER SEMI COLON BANG PLUS DASH ASTERISK SLASH
PERCENT ARROW DBLARROW BAR LE LT GE GT EQ EQEQ RPAREN LPAREN
RBRACE LBRACE RBRACK LBRACK BACKSLASH
/* keywords */ TYPE DEF LET IN END EMPTY OR FOR DO FIX IS CASE IF THEN WHEN
ELSE SHADOW AS
/* end of file */ EOF

%token <string> STRING
%token <bool> BOOL
%token <string> ID CAPID        /* lower/uppercase identifiers */

// Operator precedence
//%nonassoc EQ LE LT GE GT

// Types for nonterminals
%start <[ `Cmd of string | `Expr of Backend.expr | `Type of Backend.tp]> replcmd
%start <unit> unused

%%
// ---------- PARSING RULES ----------

unused: ASTERISK BANG BAR CAPID CASE COLON DASH DBLARROW DEF ELSE END EQEQ GE GT
IF LE LT PERCENT PLUS SEMI SHADOW SLASH THEN TYPE UNDER {()};

// ===== Types =====
tp: tp_product {$1}
| a=tp_product ARROW b=tp { `Fn(a, b) }

tp_product: tp_atom { $1 }
| tp_atom COMMA { `Tuple [$1] }
| x=tp_atom xs=nonempty_list(COMMA tp_atom {$2}) { `Tuple(x::xs) }

tp_atom:
| LPAREN RPAREN { `Tuple [] }
| ID { match $1 with
         | "bool" -> `Bool
         | "string" -> `String
         | _ -> $syntaxerror (* parseError "unrecognized type name" *) }
| LBRACK tp RBRACK { `Box $2 }
| LBRACE eqtp RBRACE { `Set $2 }
| LPAREN tp RPAREN { $2 }

// Need this because `Set takes an eqtp.
eqtp: tp { match firstOrder $1 with
           | Some a -> a
           | None -> $syntaxerror (* parseError "not an eqtp" *) }

// ===== The repl =====
replcmd:
| AT a=tp SEMI { `Type a }
| e=expr SEMI { `Expr e }
| PERCENT c=ID SEMI { `Cmd c }
| EOF { `Cmd "quit" }

// ===== Terms & Expressions =====
// TODO: explain precedence here.
// TODO: ifThenElse, proj
term: expr {B.expr $1}          /* reduce/reduce */
| term_app {$1}
| term_app nonempty_list(COMMA term_app {$2}) { B.tuple ($1::$2) }
| term_app nonempty_list(OR term_app {$2}) { B.union ($1::$2) }
| BACKSLASH xs=nonempty_list(var) DOT body=term
    { List.fold_right B.lam xs body }
| cs=list(comp) DO body=term { List.fold_right (fun f x -> f x) cs body }
// let bindings. I probably want patterns, actually.
| LET LBRACK x=var RBRACK EQ e=expr IN body=term { B.letBox x e body }
| LET x=var EQ e=expr IN body=term { B.letIn x e body }
| LET LPAREN xs=separated_list(COMMA, var) RPAREN EQ e=expr IN body=term
    { B.letTuple xs e body }
| FIX x=var IS e=term | x=var AS e=term { B.fix x e }

comp: FOR x=var IN e=expr { B.forIn x e }
| WHEN term_app { B.guard $2 }

term_app: term_atom {$1}
| expr_app { B.expr $1 }        /* reduce/reduce */

term_atom:
| expr_atom { B.expr $1 }       /* reduce/reduce */
| EMPTY { B.union [] }
| STRING { B.string $1 }
| BOOL { B.bool $1 }
| LPAREN RPAREN { B.tuple [] }
| LPAREN term RPAREN { $2 }
| LBRACK term RBRACK { B.box $2 }
| LBRACE separated_list(COMMA, term_app) RBRACE { B.set $2 }
// set comprehensions
| LBRACE term_app nonempty_list(comp) RBRACE
  { List.fold_right (fun f x -> f x) $3 (B.set [$2]) }

expr: expr_app {$1}
| AT tp_atom term { B.asc $2 $3 }

expr_app: expr_fnapp { $1 }
| expr_fnapp EQ expr_fnapp { B.equals $1 $3 }

expr_fnapp: expr_atom { $1 }
| expr_fnapp term_atom { B.app $1 $2 }

expr_atom: var { B.var $1 }
| LPAREN expr RPAREN { $2 }

// NB. We generate symbols which always have id 0. I think this is safe, because
// symbol comparison also uses the symbol's name, and I _think_ all my code
// handles shadowing properly. I admit I'm not entirely confident, though.
var: ID { {name = $1; id = 0; degree = 0} }
