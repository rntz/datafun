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
let cmd: Repl.cmd test = Repl.Cmd.show, Parse.replcmd Lex.token

let parse ((show,parse): 'a test) (input: string): 'a =
  let x = parse (Lexing.from_string input) in
  Printf.printf "parsed: %s\n" (show x);
  x

let elab (expr: expr): IL.exp =
  let open Elab in
  let (tp, e) = elabExp emptyCx None expr in
  Printf.printf "  type: %s\n" (Type.show tp);
  e

let run (expr: IL.exp): Interp.value =
  let open Interp in
  let value = eval emptyEnv expr in
  Printf.printf " value: %s\n" (Value.show value);
  value

(* (read |> eval |> print) a string *)
let replstr input =
  ignore (parse exp input |> elab |> run)

let top = Repl.make ()
let repl ?repl:(repl=top) () =
  let buf = Lexing.from_channel stdin in
  let read () = Parse.replcmd Lex.token buf in
  let rec loop () =
    Printf.printf "> %!";
    (* TODO: catch parse errors and display them usefully. *)
    let cmd = read () in
    let continue = try Repl.perform repl cmd; true
                   with Repl.Quit -> false
    in if continue then loop() else ()
  in loop ()
