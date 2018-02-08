open Util

include Ast
module Parse = DatafunParser
module Lex = DatafunLexer

type 'a parse = Lexing.lexbuf -> 'a

let pat = Parse.test_pat Lex.token
let decls = Parse.test_decls Lex.token
let tp = Parse.test_tp Lex.token
let exp = Parse.test_exp Lex.token

let parse : 'a parse -> string -> 'a =
  fun p s -> p (Lexing.from_string s)
