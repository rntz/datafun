open Util open Passes open Printf

module Simple = Simplify(ToHaskell)
module Zero = ZeroChange(Simple)
module Semi = Seminaive(Zero)
module Surf = Surface(Semi)
module Parse = Parser.Make(Surf)

let compile_from buf =
  let _tp, (phi, _delta) = Parse.term_eof Lexer.token buf Cx.empty None in
  phi |> Zero.finish |> Simple.finish |> StringBuilder.finish

let compile (): int =
  try print_endline (compile_from (Lexing.from_channel stdin)); 0
  with Parse.Error -> eprintf "parse error\n"; 1
     | Failure x when x = "lexing: empty token" -> eprintf "lexing error\n"; 1
     | TypeError msg -> eprintf "Type error: %s\n" msg; 1
