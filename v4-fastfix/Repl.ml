open Util

exception Quit

let perform = function
  | `Cmd "quit" -> raise Quit
  | `Cmd cmd -> print_endline ("Unrecognized command: " ^ cmd)
  | `Type _tp -> print_endline "TODO: implement type printer"
  | `Expr e ->
     let _tp, phi, delta = Backend.phiDeltaExpr e in
     (* TODO: pretty-printer for types *)
     print_endline ("phi:   " ^ phi);
     print_endline ("delta: " ^ delta)

let readEvalPrint buf =
  print_string "> "; flush stdout;
  try perform (Parser.replcmd Lexer.token buf)
    with Parser.Error -> print_endline "Sorry, I can't parse that."
       | TypeError msg -> print_endline ("Type error: " ^ msg)
       | Failure x when x = "lexing: empty token" ->
          print_endline "I can't lex that."

(* We create a new lexer every time because it helps recover from lex & parse
   errors better. I suspect this only works because of line-buffering. *)
let repl () =
  let rec loop () = readEvalPrint (Lexing.from_channel stdin); loop() in
  try loop () with Quit -> print_endline "Bye!"
