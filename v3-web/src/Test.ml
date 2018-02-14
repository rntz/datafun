include Util
include Ast
module Parse = DatafunParser
module Lex = DatafunLexer

type 'a test = ('a -> string) * (Lexing.lexbuf -> 'a)

let pat = Pat.show, Parse.test_pat Lex.token
let decls: expr decl list test =
  (fun ds -> List.map (Decl.show Exp.show) ds |> String.concat " "),
  Parse.test_decls Lex.token
let tp = Type.show, Parse.test_tp Lex.token
let exp: expr test = Exp.show, Parse.test_exp Lex.token

let parse ((show,parse): 'a test) (input: string): 'a =
  let x = parse (Lexing.from_string input) in
  print_endline (show x); x
