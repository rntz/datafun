%parameter <B: Lang.SURFACE>

%{
    open Type
%}

// Operator precedence & associativity. Operators listed later bind tighter.
// (see 4.1.4 in http://gallium.inria.fr/~fpottier/menhir/manual.html)
%nonassoc EQ
%right PLUS

// Types for nonterminals
%start <[ `Cmd of string | `Expr of B.term | `Type of B.tp]> replcmd
%start <B.term> term_eof
%start <unit> unused

%%
// ---------- PARSING RULES ----------
unused: ASTERISK BANG BAR CAPID CASE COLON DASH DBLARROW DEF ELSE END EQEQ GE GT
IF LE LT PLUS SHADOW SLASH THEN TYPE UNDER {()};

// ===== Start symbols =====
term_eof: term list(SEMI) EOF { $1 }
replcmd:
| AT a=tp SEMI { `Type a }
| e=term SEMI { `Expr e }
| PERCENT c=ID SEMI { `Cmd c }
| EOF { `Cmd "quit" }

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

// ===== Expressions =====
// TODO: ifThenElse, proj
term: term1 {$1}
| AT a=tp_atom m=term | m=term1 COLON a=tp { B.asc a m }
| BACKSLASH xs=nonempty_list(var) DOT body=term
    { List.fold_right B.lam xs body }
// | cs=list(comp) DO body=term { List.fold_right (fun f x -> f x) cs body }
| FOR "(" x=var IN e=term ")" body=term { B.forIn x e body }
| WHEN "(" e=term ")" body=term { B.guard e body }
| FIX x=var IS e=term { B.fix x e }
// let-bindings.
| LET LBRACK x=var RBRACK EQ e=term IN body=term { B.letBox x e body }
| LET x=var EQ e=term IN body=term { B.letIn x e body }
| LET LPAREN xs=separated_list(COMMA, var) RPAREN EQ e=term IN body=term
    { B.letTuple xs e body }
// type-annotated forms
| FIX x=var ":" a=tp IS e=term { B.asc a (B.fix x e) }
| LET x=var ":" a=tp "=" e=term IN body=term { B.letIn x (B.asc a e) body }
| LET "[" x=var ":" a=tp "]" "=" e=term IN body=term
    { B.letBox x (B.asc (`Box a) e) body }

// Comprehensions (for & when)
comp: FOR x=var IN e=term { B.forIn x e } | WHEN term { B.guard $2 }

// Tuples and unions
term1: term2 {$1}
| term2 nonempty_list(COMMA term2 {$2}) { B.tuple ($1::$2) }
| term2 nonempty_list(OR term2 {$2}) { B.union ($1::$2) }

// Equality tests
term2: term3 {$1}
| term2 EQ term2 { B.equals $1 $3 }
| term2 PLUS term2 { B.binop `Plus $1 $3 }

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

var: ID { Sym.intern $1 }
