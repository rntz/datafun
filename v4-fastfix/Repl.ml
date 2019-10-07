open Util
open Backend
module Parse = Parser.Make(Backend)

exception Quit

let pretty (x: Zeroed.term): Format.formatter -> unit =
  x |> Zeroed.finish |> Simplified.finish |> Renamed.finish
  |> snd |> Pretty.finish

let perform = function
  | `Cmd "quit" -> raise Quit
  | `Cmd cmd -> print_endline ("Unrecognized command: " ^ cmd)
  | `Type tp -> Printf.printf " type: %s\n" Type.(to_string tp);
  | `Expr e ->
     let tp, (phi, delta) = infer e Cx.empty in
     Format.printf "@[<v>@[<hov 2>type:@ %s@]@,@[<hov 2>phi:  @ @[%t@]@]@,@[<hov 2>delta:@ @[%t@]@]@]@."
       Type.(to_string tp) (pretty phi) (pretty delta)

let readEvalPrint buf =
  if Unix.isatty Unix.stdin then (print_string "> "; flush stdout);
  try perform (Parse.replcmd Lexer.token buf)
    with Parse.Error -> print_endline "Sorry, I can't parse that."
       | TypeError msg -> print_endline ("Type error: " ^ msg)
       | Failure x when x = "lexing: empty token" ->
          print_endline "I can't lex that."

(* We create a new lexer every time because it helps recover from lex & parse
   errors better. I suspect this only works because of line-buffering. *)
let repl () =
  let rec loop () = readEvalPrint (Lexing.from_channel stdin); loop() in
  try loop () with Quit -> print_endline "Bye!"
