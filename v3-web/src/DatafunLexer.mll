{
  open DatafunParser
}
let comment = "#" [^'\n']* "\n"
let digit  = ['0'-'9']
let integer = '-'? digit+
let lident = ['a' - 'z']['a'-'z' 'A'-'Z' '0'-'9' '_' '-' ]*
let uident = ['A' - 'Z']['a'-'z' 'A'-'Z' '0'-'9' '_' '-' ]*
let whitespace = ['\t' ' ' '']+
let new_line = '\n' | '\r' | '\r' '\n'
let string_literal = ([^'\\' '\"' '\n'] | "\\n" | "\\t" | "\\\\" |"\\\"" )*

rule token = parse
  (* punctuation *)
  | "_" {UNDER}
  | "," {COMMA} | "." {DOT} | "!" {BANG}
  | ":" {COLON} | ";" {SEMI}
  | "+" {PLUS}  | "-" {DASH} | "*" {ASTERISK} | "/" {SLASH}  | "%" {PERCENT}
  | "->" {ARROW} | "=>" {DBLARROW} | "=>-" {DBLARROWMINUS}
  | "|" {BAR}

  | "<=" {LE} | "<" {LT} | ">=" {GE} | ">" {GT}
  | "=" {EQ} | "==" {EQEQ}

  (* brackets *)
  | "(" {LPAREN} | ")" {RPAREN}
  | "{" {LBRACE} | "}" {RBRACE}
  | "[" {LBRACK} | "]" {RBRACK}

  (* type keywords *)
  | "bool" {BASE `Bool} | "int" {BASE `Int} | "str" {BASE `Str}

  (* decl keywords *)
  | "type" {TYPE} | "def" {DEF} | "shadow" {SHADOW}

  (* expression keywords *)
  | "the" {THE}
  | "let" {LET} | "in" {IN} | "end" {END}
  | "empty" {EMPTY} | "or" {OR} | "for" {FOR} | "do" {DO}
  | "fix" {FIX} | "as" {AS}
  | "fn" {FN}
  | "case" {CASE}
  | "if" {IF} | "then" {THEN} | "else" {ELSE}

  (* literals *)
  | "true" {LITERAL(`Bool true)}
  | "false" {LITERAL(`Bool false)}
  | integer as n         {LITERAL(`Int (int_of_string n))}
  | '\"' (string_literal as s) '\"'
    {for i = 0 to String.length s - 1 do
       if s.[i] = '\n' then Lexing.new_line lexbuf else ()
     done;
     LITERAL(`Str (Scanf.unescaped s))}

  (* identifiers*)
  | lident as s {ID s} | uident as s {CAPID s}

  (* whitespace *)
  | comment             {Lexing.new_line lexbuf; token lexbuf}
  | whitespace          {token lexbuf}
  | new_line            {Lexing.new_line lexbuf; token lexbuf}
  | eof                 {EOF}
