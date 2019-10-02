%{
    open Util open Type
    module B = Backend
%}

// TODO: filter this to only what I need
%token
/* punctuation */ AT DOT COMMA UNDER SEMI COLON BANG PLUS DASH ASTERISK SLASH
PERCENT ARROW DBLARROW BAR LE LT GE GT EQ EQEQ RPAREN LPAREN
RBRACE LBRACE RBRACK LBRACK BACKSLASH
/* keywords */ TYPE DEF LET IN END EMPTY OR FOR DO CASE IF THEN WHEN
ELSE SHADOW AS
/* end of file */ EOF

%token <string> STRING
%token <bool> BOOL
%token <int> INTEGER
%token <string> ID CAPID        /* lower/uppercase identifiers */

// Operator precedence
//%nonassoc EQ LE LT GE GT

// Types for nonterminals
%start <[ `Cmd of string | `Expr of Backend.term | `Type of Backend.tp]> replcmd
%start <unit> unused

%%
// ---------- PARSING RULES ----------

unused: ASTERISK BANG BAR CAPID CASE COLON DASH DBLARROW DEF ELSE END EQEQ GE GT
IF LE LT PLUS SHADOW SLASH THEN TYPE UNDER {()};

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
         | "str" -> `String
         | "nat" -> `Nat
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
| e=term SEMI { `Expr e }
| PERCENT c=ID SEMI { `Cmd c }
| EOF { `Cmd "quit" }

// ===== Expressions =====
// TODO: ifThenElse, proj
term: term1 {$1}
| AT a=tp_atom m=term | m=term1 COLON a=tp { B.asc a m }
| BACKSLASH xs=nonempty_list(var) DOT body=term
    { List.fold_right B.lam xs body }
| cs=list(comp) DO body=term { List.fold_right (fun f x -> f x) cs body }
// let-bindings.
| LET LBRACK x=var RBRACK EQ e=term IN body=term { B.letBox x e body }
| LET x=var EQ e=term IN body=term { B.letIn x e body }
| LET LPAREN xs=separated_list(COMMA, var) RPAREN EQ e=term IN body=term
    { B.letTuple xs e body }
| x=var AS e=term { B.fix x e }

// Comprehensions (for & when)
comp: FOR x=var IN e=term { B.forIn x e } | WHEN term { B.guard $2 }

// Tuples and unions
term1: term2 {$1}
| term2 nonempty_list(COMMA term2 {$2}) { B.tuple ($1::$2) }
| term2 nonempty_list(OR term2 {$2}) { B.union ($1::$2) }

// Equality tests
term2: term3 {$1} | term3 EQ term3 { B.equals $1 $3 }

// function applications
term3: term_atom { $1 } | term3 term_atom { B.app $1 $2 }

term_atom:
| var { B.var $1 }
| EMPTY { B.union [] }
| STRING { B.string $1 }
| BOOL { B.bool $1 }
| INTEGER { if $1 < 0 then $syntaxerror else B.nat $1 }
| LPAREN RPAREN { B.tuple [] }
| LPAREN term RPAREN { $2 }
| LBRACK term RBRACK { B.box $2 }
| LBRACE separated_list(COMMA, term2) RBRACE { B.set $2 }
// set comprehensions
| LBRACE term nonempty_list(comp) RBRACE
  { List.fold_right (fun f x -> f x) $3 (B.set [$2]) }

// NB. We generate symbols which always have id 0. I think this is safe, because
// symbol comparison also uses the symbol's name, and I _think_ all my code
// handles shadowing properly. I admit I'm not entirely confident, though.
var: ID { {name = $1; id = 0; degree = 0} }
