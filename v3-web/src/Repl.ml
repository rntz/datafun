open Util
open Ast

type repl = { mutable cx: Elab.cx
            ; mutable env: Interp.env }

type cmd = Expr of expr
         | Decls of expr decl list

let tryPerform repl = function
  | Expr expr ->
     let (tp, ilexpr) = Elab.elabExp repl.cx None expr in
     Printf.printf "%s\n" (Type.show tp);
     let value = Interp.eval repl.env ilexpr in
     Printf.printf "%s\n" (Interp.Value.show value)

  | Decls decls ->
     let cx = ref repl.cx in
     let patexps = Elab.elabDecls dummy_loc cx `Iso decls in
     let new_env = Interp.evalDecls repl.env patexps in
     (* swap in the changes atomically; if elaboration succeeds but
      * evaluation errors, we shouldn't update the context. *)
     repl.cx <- !cx; repl.env <- new_env

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
       "Congratulations, you found a bug! Please report this!\nError: %s\n"
       msg
  | Elab.TypeError (_loc, msg) ->
     (* TODO: use location information *)
     Printf.printf "Sorry, I can't type-check that!\nReason: %s\n" msg
  | Interp.Stuck msg ->
     Printf.printf "Uh-oh, that caused an error during evaluation.\nError: %s\n" msg
  | Interp.NoMatch ->
     print_endline "Uh-oh, that caused an error (Interp.NoMatch) that should be impossible. Please report this!"
