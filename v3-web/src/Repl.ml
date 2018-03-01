open Util
open Ast

exception Quit

type repl = { mutable cx: Elab.cx
            ; mutable env: Interp.env }

type cmd = [ `Expr of expr
           | `Decls of expr decl list
           | `Cmd of string ]

module Cmd = struct
  let show: cmd -> string = function
    | `Expr e -> Exp.show e
    | `Decls ds -> Decl.show_list Exp.show ds
    | `Cmd s -> "%" ^ s
end

let make () = { cx = Elab.emptyCx; env = Interp.emptyEnv }
let reset repl = repl.cx <- Elab.emptyCx; repl.env <- Interp.emptyEnv

let tryPerform repl: cmd -> unit = function
  | `Expr expr ->
     let (tp, ilexpr) = Elab.elabExp repl.cx None expr in
     let value = Interp.eval repl.env ilexpr in
     Printf.printf "%s : %s\n%!" (Interp.Value.show value) (Type.show tp)

  | `Decls decls ->
     let cx = ref repl.cx in
     let patexps = Elab.elabDecls dummy_loc cx `Iso decls in
     let new_env = Interp.evalDecls repl.env patexps in
     (* TODO: It would be nice to print a list of the vars bound
      * & their types. unfortunately, "shadow" complicates this.
      * if we used an update/writer monad, this would be easy. argh.
      *)
     (* swap in the changes atomically; if elaboration succeeds but
      * evaluation errors, we shouldn't update the context. *)
     repl.cx <- !cx; repl.env <- new_env

  | `Cmd "quit" -> raise Quit
  | `Cmd _ -> print_endline "Sorry, I don't understand that command."

let perform repl cmd =
  try tryPerform repl cmd
  (* What errors can occur?
   * - Util.TODO
   * - Util.Bug of string
   * - Elab.TypeError of loc * string
   * - Interp.Stuck of string
   * - Interp.NoMatch (Interp should catch & rethrow as Stuck, but just in case)
   *)
  with
  | TODO -> print_endline "Uh-oh, that hit an unimplemented case in the compiler. Please report this!"
  | Bug msg ->
     Printf.printf
       "Congratulations, you found a bug! Please report this!\nError: %s\n%!"
       msg
  | Elab.TypeError (_loc, msg) ->
     (* TODO: use location information *)
     Printf.printf "Sorry, I can't type-check that!\nReason: %s\n%!" msg
  | Interp.Stuck msg ->
     Printf.printf "Uh-oh, that caused an error during evaluation.\nError: %s\n%!" msg
  | Interp.NoMatch ->
     print_endline "Uh-oh, that caused an error (Interp.NoMatch) that should be impossible. Please report this!"
