(* open Util
 * open Ast
 * 
 * module type JSEXP = sig
 *   type block
 *   type exp
 * 
 *   (\* exp constructors *\)
 *   val var: string -> exp
 *   val lit: lit -> exp
 *   val array: exp list -> exp
 *   val fn: (string * block) -> exp
 *   val throw: exp -> exp
 *   val block: block -> exp
 * 
 *   (\* block constructors *\)
 *   val exp: exp -> block
 *   val const: string -> exp -> block -> block
 * end
 * 
 * module Compile(JS: JSEXP) = struct
 *   open Backend
 * 
 *   (\* I'm gonna need to generate temporary variables, aren't I?
 *    * ugh.
 *    *\)
 *   let nextInt: int ref = ref 0
 * 
 *   (\* shit. argh. need a context to handle deBruijn indices. *\)
 *   let rec compile (exp: exp): JS.block = match exp with
 *     | #lit as l -> todo()
 *     | `Stuck msg -> JS.exp (JS.throw (JS.lit (`Str msg)))
 *     | `Var v -> JS.exp (JS.var v)
 *     | `Let (n, e, body) -> todo()
 *     | `Lub (how,xs) -> todo()
 *     | `Eq (how,x,y) -> todo()
 *     | `Fix (init, x, step) -> todo()
 *     | `Lam (x, e) -> todo()
 *     | `Tuple xs -> todo()
 *     | `Tag (n,x) -> todo()
 *     | `MkSet xs -> todo()
 *     | `App (x,y) -> todo()
 *     | `IfThenElse (x,y,z) -> todo()
 *     | `For (how, sete, (v, body)) -> todo()
 *     | `Case (subj, arms) -> todo()
 * end *)
