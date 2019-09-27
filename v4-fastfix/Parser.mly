%{
    open Util
    open Types
    (* open Langs *)

    let parseError msg = todo ("parse error: " ^ msg)
%}

/* TODO: filter this to only what I need */
%token
/* punctuation */ DOT COMMA UNDER SEMI COLON BANG PLUS DASH ASTERISK SLASH
PERCENT ARROW DBLARROW BAR LE LT GE GT EQ EQEQ RPAREN LPAREN
RBRACE LBRACE RBRACK LBRACK
/* keywords */ TYPE DEF THE LET IN END EMPTY OR FOR DO FIX AS FN CASE IF THEN
ELSE SHADOW
/* end of file */ EOF

%token <string> STRING
%token <bool> BOOL
%token <string> ID CAPID        /* lower/uppercase identifiers */

// Operator precedence
// %nonassoc EQ LE LT GE GT

/* Types for nonterminals */
%start <Types.modaltp> tp test_tp
%start <unit> unused

%%
/* ---------- PARSING RULES ---------- */

unused: AS ASTERISK BANG BAR BOOL CAPID CASE COLON DASH DBLARROW DEF DO DOT ELSE
EMPTY END EQ EQEQ FIX FN FOR GE GT IF IN LBRACK LE LET LT OR PERCENT PLUS RBRACK
SEMI SHADOW SLASH STRING THE THEN TYPE UNDER {()};

test_tp: tp EOF { $1 }
tp: tp_product {$1}
| tp_product ARROW tp { `Fn($1, $3) }

tp_product: tp_atom
| tp_atom COMMA { `Tuple [$1] }
| tp_atom nonempty_list(COMMA tp_atom {$2}) { `Tuple($1::$2) }

tp_atom:
| LPAREN RPAREN { `Tuple [] }
| ID { match $1 with
         | "bool" -> `Bool
         | "string" -> `String
         | _ -> parseError "unrecognized type name" }
| LBRACK tp RBRACK { `Box $2 }
| LBRACE eqtp RBRACE { `Set $2 }
| LPAREN tp RPAREN { $2 }

/* I need eqtp productions because eg. `Set takes an eqtp. */
eqtp: tp {
  match firstOrder $1 with
  | Some a -> a
  | None -> parseError "not an eqtp"
}
  
