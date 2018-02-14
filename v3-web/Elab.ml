open Sigs
open Util
open Ast
open Backend

module Vars = Map.Make(String)
type 'a vars = 'a Vars.t

type tones = tone vars
type cx = { depth: int; vars: (int * tp) vars }

module Tones = struct
  type t = tones
  let empty: tones = Vars.empty
  let append = Vars.union (fun _ x y -> Some (Tone.meet x y))
end

(* A monad for type inference:
 * 1. we read a context, `cx`
 * 2. we write variable->tone annotations, `tones`
 *)
module Infer = struct
  include Monad(struct
    open Tones
    type 'a t = cx -> tones * 'a
    let pure x cx = (empty, x)
    let map f k cx = let (tones, x) = k cx in (tones, f x)
    let concat k cx = let (tones1, next) = k cx in
                      let (tones2, result) = next cx in
                      (Tones.append tones1 tones2, result)
  end)
  (* TODO: do I need this? *)
  (* let ask (f: cx -> 'a t): 'a t = fun cx -> f cx cx *)
end
open Infer
module ExpInf = Exp.Seq(Infer)  (* TODO: do I need this? *)

type result = tp * Backend.exp
type 'a infer = 'a Infer.t

let use (v: var): result infer = fun cx ->
  let (depth,tp) = Vars.find v cx.vars in
  Vars.singleton v `Id, (tp, `Var (cx.depth - depth))

(* user-visible errors *)
exception TypeError of string

(* internal error format *)
type why = AppNonFunction
         | InferredSum
         | InferredTuple
         | TagNotFound
         | TupleWrongLength
         | Because of string
exception Nope of why

let nope why = raise (Nope why)
(* TODO: good error messages
 * this function probably needs more arguments/information
 *)
let explain: why -> string = function
  | AppNonFunction -> "applying non-function"
  | InferredTuple -> "tuples must have tuple type"
  | InferredSum -> "tag must have sum type"
  | TagNotFound -> "tag not in type"
  | TupleWrongLength -> "tuples have incompatible sizes"
  | Because msg -> msg


(* ---------- TYPE INFERENCE ---------- *)
type expect = tp option
type alg = expect -> result infer

let elabExp (e: alg expF) (expect: expect): result infer =
  (* checks a synthesized type against expect *)
  let got(x:tp):tp = raise TODO in
  let synth e = e None in
  let check e tp = e (Some tp) in
  match e with
  | #lit as l -> pure (Lit.typeOf l, l)
  | `Var v -> use v
  | `The (tp,e) -> check e tp => fun (_,exp) -> (got tp, exp)
  | `Prim p -> raise TODO
  (* for now, only support synthesizing `Lub expressions. *)
  (* todo: helper for "can only check, cannot infer" expressions *)
  | `Lub es -> raise TODO
  | `Fix (pat, body) -> raise TODO
  | `Let (ds, body) -> raise TODO
  (* introductions *)
  | `Box e -> raise TODO
  | `Lam (pats, body) -> raise TODO (* checking only! *)
  | `Tuple es ->
     map (List.split @> fun (tps,es) -> `Tuple tps, `Tuple es)
       (match expect with
        | None -> forEach es synth
        | Some (`Tuple ts) ->
           list (try List.map2 check es ts
                 with Invalid_argument _ -> nope TupleWrongLength)
        | Some _ -> nope InferredTuple)
  | `Tag (n,e) ->
     let get_type = function
       | `Sum nts -> (try List.assoc n nts with Not_found -> nope TagNotFound)
       | _ -> nope InferredSum
     in e (Option.map get_type expect) >>= fun (tp,exp) ->
     pure (Option.default (`Sum [n,tp]) expect, `Tag (n,exp))
  | `Set [] -> (match expect with
                | Some (`Set es) -> raise TODO
                | Some _ -> nope (raise TODO)
                | None -> nope (raise TODO))
  | `Set es -> raise TODO
  (* eliminations *)
  | `Unbox e -> raise TODO
  | `App (e1,e2) -> e1 None >>= fun (ftp, fexp) ->
                    let (a,b) = match ftp with `Arrow x -> x
                      | _ -> nope AppNonFunction
                    in e2 (Some a) => fun (_,aexp) -> (got b, `App (fexp,aexp))
  | `For (comps, body) -> raise TODO
  | `Case (subject, arms) -> raise TODO

let rec infer ((ann,e): expr) (expect: tp option): result infer = fun cx ->
  (* TODO: add line number information, etc! *)
  let e': alg expF = Exp.map infer e in
  try elabExp e' expect cx
  with Nope why -> raise (TypeError (explain why))
