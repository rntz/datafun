open Sigs
open Util
open Ast

module Vars = Map.Make(String)
module Types = Vars
type 'a vars = 'a Vars.t

type tones = tone vars
(* need typing name context as well! *)
type cx = { depth: int          (* expression variable binding depth *)
          ; types: tp Types.t
          ; vars: (int * tp) vars }

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
  let getContext: cx t = fun cx -> (Tones.empty, cx)
  let withContext cx (k: 'a t): 'a t = fun _ -> k cx
end
module ExpInf = Exp.Seq(Infer)  (* TODO: do I need this? *)

type result = tp * Backend.exp
type 'a infer = 'a Infer.t

let use (v: var): result infer = fun cx ->
  let (depth,tp) = Vars.find v cx.vars in
  Vars.singleton v `Id, (tp, `Var (cx.depth - depth))

let withVarAs (v: var) (tp: tp) (tone: tone) (k: 'a infer): 'a infer = todo()
let withVar v tp = withVarAs v tp `Id


(* ---------- Checking pattern types & exhaustiveness ---------- *)
module InferPat = struct
  include Monad(struct
    type 'a t = (cx * 'a) infer
    let pure x = Infer.(getContext ** pure x)
    let map f = Infer.map (fun (cx,x) -> (cx,f x))
    let concat a = Infer.(a >>= fun (cx,b) -> withContext cx b)
  end)
end

exception IncompatiblePattern of pat * tp

(* An idea that didn't work out but might be useful in future:
 * type-checking patterns as computing type difference!
 *
 *  elabPat tp pat ==> (diff, backendPat)
 *
 * diff: roughly, tp minus pat's type.
 * backendPat: the Backend.pat implementing pat.
 *
 * this gives us exhaustiveness checking and refinement for free!
 * exhaustiveness: at the end, the type must be empty.
 *
 * problem: what is (elabPat A (`Var x))?
 * this is exhaustive, but what type do we return as difference?
 * various solutions here.
 * - add a bottom/empty type.
 * - return a (tp option). does this work?
 * - use this only for exhaustiveness checking, not for refinement;
 *   check each pattern against the subject's unaltered type.
 *
 * Decided against doing this. Should work out the theory in future.
 *)

(* TODO: shouldn't tone here be simply [ `Id | `Iso ]?
 * maybe [ `Id | `Op | `Iso ] in future?
 * but we never need to bind variables at `Path, do we?
 * (though we may infer that they are used at `Path!) *)
let rec elabPat: pat -> tp -> tone -> (Backend.pat -> 'a infer) -> 'a infer =
  fun pat tp tone k ->
  let fail() = raise (IncompatiblePattern (pat, tp)) in
  match pat, tp with
  (* need tone composition! *)
  (* Explicit box unwrapping. *)
  | `Box p, `Box a -> elabPat pat a Tone.(tone * `Iso) k
  | `Box _, _ -> fail()
  (* Box auto-unwrapping. Must try this case before others. *)
  (* need tone composition! *)
  | pat, `Box a -> elabPat pat a Tone.(tone * `Iso) k
  | #lit as l, tp -> if tp <> Lit.typeOf l then fail()
                     else k (`Eq (Lit.typeOf l, l))
  | `Wild, tp -> k `Wild
  (* TODO: check whether tp is discrete. if so, bind discretely! *)
  | `Var v, tp -> withVarAs v tp tone (k (`Var (Some v)))
  (* argh, this is wrong. want IDIOM.list here. *)
  | `Tuple ps, `Tuple tps -> todo()
  (* | `Tuple [], `Tuple [] -> k (`Tuple [])
   * | `Tuple (p::ps), `Tuple (tp::tps) -> todo() *)
  | `Tuple _, _ -> todo()
  | `Tag(n,p), `Sum tps ->
     let tp = try List.assoc n tps with Not_found -> fail() in
     elabPat p tp tone (fun p -> k (`Tag(n,p)))
  | `Tag _, _ -> fail()

(* Alternatively, and more reusably, I could have
 *
 * elabPat: pat -> tp -> tone -> ((var * tp * tone) list * Backend.pat) infer
 *
 * and I could probably simplify this by using a Writer monad to generate
 * the ((var * tp * tone) list).
 *)


(* ---------- Error handling ---------- *)
exception TypeError of string

(* internal error format *)
type why = AppNonFunction
         | InferredSum
         | InferredTuple
         | TagNotFound of tag
         | TupleWrongLength
         | Inferred of tp
         | NotSemilattice of tp
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
  | TagNotFound t -> "tag " ^ t ^ " is not in type"
  | TupleWrongLength -> "tuples have incompatible sizes"
  | Inferred inferred -> "inferred type: " ^ Type.show inferred
  | Because msg -> msg
  | _ -> raise TODO


(* ---------- Type inference ---------- *)
type expect = tp option
type alg = expect -> result infer

let elabExp (e: alg expF) (expect: expect): result infer =
  let open Infer in
  getContext >>= fun cx ->
  let unroll tpname = Types.find tpname cx.types in
  (* checks an inferred type against expect *)
  let got (inferred: tp): tp = match expect with
    | None -> inferred
    | Some wanted when Type.subtype unroll inferred wanted -> wanted
    | _ -> nope (Inferred inferred) in
  let synth e = e None in
  let check tp e = e (Some tp) in
  let semilattice tp =
    try Backend.semilattice unroll tp
    with Backend.NotSemilattice -> nope (NotSemilattice tp) in
  let checkOnly (f: tp -> Backend.exp infer): result infer =
    raise TODO
  in
  let patName: pat -> Backend.name = function | `Var v -> Some v | _ -> None in
  match e with
  | #lit as l -> pure (Lit.typeOf l, l)
  | `Var v -> use v
  | `The (tp,e) -> check tp e => fun (_,exp) -> (got tp, exp)
  | `Prim p -> raise TODO
  (* for now, only support checking `Lub expressions. *)
  | `Lub es -> checkOnly @@ fun tp ->
               forEach es (check tp) => List.split
               => fun (_,es) -> `Lub (semilattice tp, es)
  | `Fix (pat, body) ->
     checkOnly @@ fun tp ->
     (* need the pattern to be irrefutable!
      * hm, how will exhaustiveness work? *)
     (* TODO: munge environment! check synthesized tones! *)
     pure (`Fix (Backend.zeroExp (semilattice tp), patName pat,
                 (* need to case-analyse! *)
                 raise TODO))
  | `Let (ds, body) -> raise TODO
  (* introductions *)
  | `Box e -> raise TODO
  | `Lam (pats, body) -> raise TODO (* checking only! *)
  | `Tuple es ->
     map (List.split @> fun (tps,es) -> `Tuple tps, `Tuple es)
       (match expect with
        | None -> forEach es synth
        | Some (`Tuple ts) ->
           list (try List.map2 check ts es
                 with Invalid_argument _ -> nope TupleWrongLength)
        | Some _ -> nope InferredTuple)
  | `Tag (n,e) ->
     let get_type = function
       | `Sum nts -> (try List.assoc n nts
                      with Not_found -> nope (TagNotFound n))
       | _ -> nope InferredSum
     in e (Option.map get_type expect) >>= fun (tp,exp) ->
     pure (Option.default (`Sum [n,tp]) expect, `Tag (n,exp))
  | `Set [] -> (match expect with
                | Some (`Set es) -> raise TODO
                | Some _ -> nope (raise TODO)
                | None -> nope (raise TODO))
  | `Set es -> raise TODO
  (* eliminations *)
  | `Unbox e -> raise TODO      (* need to consult my notes for this one *)
  | `App (e1,e2) -> e1 None >>= fun (ftp, fexp) ->
                    let (a,b) = match ftp with `Arrow x -> x
                                             | _ -> nope AppNonFunction
                    in e2 (Some a) => fun (_,aexp) -> (got b, `App (fexp,aexp))
  | `For (comps, body) -> raise TODO
  | `Case (subject, arms) -> raise TODO

let rec infer ((ann,e): expr) (expect: tp option): result infer = fun cx ->
  let e': alg expF = Exp.map infer e in
  try elabExp e' expect cx
  (* TODO: give:
   * - line/column information
   * - the expected type, or "could not infer type"
   *)
  with Nope why -> raise (TypeError (explain why))
