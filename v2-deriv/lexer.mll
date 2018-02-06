{
  open Parser

  let stringfold f init s =
    let n = String.length s in
    let r = ref init in
    for i = 0 to n-1 do r := f s.[i] (!r) done;
    !r

  let count_newlines s =
    stringfold (fun c n -> if c = '\n' then n+1 else n) 0 s

  let repeat n thunk = for i = 0 to n-1 do thunk() done
}
let comment = "//" [^'\n']* "\n"
let digit  = ['0'-'9']
let number = '-'? digit+ ('.' digit*)?
let lident = ['a' - 'z']['a'-'z' 'A'-'Z' '0'-'9' '_' ]*
let uident = ['A' - 'Z']['a'-'z' 'A'-'Z' '0'-'9' '_' ]*
let whitespace = ['\t' ' ']+
let new_line = '\n' | '\r' | '\r' '\n'
let string_literal = ([^'\\' '\"' '\n'] | "\\n" | "\\t" | "\\\\" |"\\\"" )*

rule token = parse
  | "of"                {OF}
  | "."                 {DOT}
  | "("                 {LPAREN}
  | ")"                 {RPAREN}
  | "{"                 {LBRACE}
  | "}"                 {RBRACE}
  | "["                 {LBRACK}
  | "]"                 {RBRACK}
  | ","                 {COMMA}
  | "fun"               {FUN}
  | "λ"                 {FUN}
  | "int"               {INT}
  | "set"               {SET}
  | "□"                 {BOX}
  | "box"               {BOX}
  | "->"                {TO}
  | "→"                 {TO}
  | "+"                 {PLUS}
  | "-"                 {MINUS}
  | "<"                 {LT}
  | "<="                {LEQ}
  | ">="                {GEQ}
  | ">"                 {GT}
  | "*"                 {AST}
  | "⊗"                 {AST}
  | "&"                 {AND}
  | "×"                 {AND}
  | "&&"                {ANDAND}
  | "||"                {OR}
  | "let"               {LET}
  | ":"                 {COLON}
  | "="                 {EQUAL}
  | "in"                {IN}
  | "fix"               {FIX}
  | "true"              {TRUE}
  | "false"             {FALSE}
  | "if"                {IF}
  | "then"              {THEN}
  | "else"              {ELSE}
  | "val"               {VAL}
  | "rec"               {REC}
  | "match"             {MATCH}
  | "with"              {WITH}
  | "|"                 {BAR}
  | "_"                 {UNDERSCORE}
  | number as n         {NUM(float_of_string n)}
  | '\"' (string_literal as s) '\"'
    {repeat (count_newlines s) (fun () -> Lexing.new_line lexbuf); STRINGLITERAL s}
  | "bool"              {BOOL}
  | "string"            {STRING}
  | "unit"              {UNIT}
  | "begin"             {BEGIN}
  | "end"               {END}
  | lident as s         {IDENT s}
  | uident as s         {CONID s}
  | comment             {Lexing.new_line lexbuf; token lexbuf}
  | whitespace          {token lexbuf}
  | new_line            {Lexing.new_line lexbuf; token lexbuf}
  | eof                 {EOF}
