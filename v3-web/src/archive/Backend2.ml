open Sigs
open Util
open Ast

module Vars = Map.Make(String)
module Types = Vars
type 'a vars = 'a Vars.t

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
         | CanOnlyCheck
         | ToneProblem of {bound: tone; used: tone}
         | LamNonFunction
         | Because of string
exception Nope of why

let nope why = raise (Nope why)
(* TODO: good error messages
 * this function probably needs more arguments/information
 *)
let explain: why -> string = function
  | LamNonFunction -> "lambda must have function type"
  | AppNonFunction -> "applying non-function"
  | InferredTuple -> "tuples must have tuple type"
  | InferredSum -> "tag must have sum type"
  | TagNotFound t -> "tag " ^ t ^ " is not in type"
  | TupleWrongLength -> "tuples have incompatible sizes"
  | Inferred inferred -> "inferred type: " ^ Type.show inferred
  | Because msg -> msg
  | _ -> raise TODO


(* ---------- Monadic infrastructure ---------- *)
type tones = tone vars
(* need typing name context as well! *)
type cx = { types: tp Types.t; vars: tp vars }

module Tones = struct
  type t = tones
  let empty: tones = Vars.empty
  let append = Vars.union (fun _ x y -> Some (Tone.meet x y))
end

(* A monad for type inference:
 * 1. we read a context, `cx`
 * 2. we write variable->tone annotations, `tones`
 *)
type 'a infer = cx -> tones * 'a
module Infer = struct
  include Monad(struct
    open Tones
    type 'a t = 'a infer
    let pure x cx = (empty, x)
    let (>>=) k f cx = let (tones1, temp) = k cx in
                       let (tones2, result) = f temp cx in
                       (Tones.append tones1 tones2, result)
  end)
  let getContext: cx t = fun cx -> (Tones.empty, cx)
  let withContext cx (k: 'a t): 'a t = fun _ -> k cx
  let locally (f: cx -> cx) (k: 'a t): 'a t = fun cx -> k (f cx)
end
(* module ExpInf = Exp.Seq(Infer) *)  (* TODO: do I need this? *)

let withVarAs (tone:tone) (var:var) (tp:tp) (k: 'a infer): 'a infer =
  fun cx ->
  let cx = {cx with vars = Vars.add var tp cx.vars} in
  let (tones, result) = k cx in
  (* the tone var is bound at must be <= the tone it's used at.
   * this is like subtyping! *)
  if try Tone.(tone <= Vars.find var tones)
     with Not_found -> true     (* not using a var is always OK *)
  then (Vars.remove var tones, result)
  else nope (ToneProblem {bound = tone; used = Vars.find var tones})

let withVars (vars: (tone * var * tp) list): 'a infer -> 'a infer =
  List.fold_right (fun (tone,var,tp) -> withVarAs tone var tp) vars

let withVar v = withVarAs `Id v


(* ---------- Checking pattern types & exhaustiveness ---------- *)
type 'a inferPat = ((tone * var * tp) list * 'a) infer
module InferPat = struct
  include Monad(struct
    type 'a t = 'a inferPat
    let pure x = Infer.(pure ([], x))
    let (>>=) a f =
      Infer.(a >>= fun (l1,b) -> f b => fun (l2,x) -> (l1 @ l2, x))
  end)
  let tell xs: unit t = Infer.pure (xs, ())
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
let rec elabPat: tone -> pat -> tp -> Backend.pat InferPat.t =
  fun tone pat tp ->
  let open InferPat in
  let fail() = raise (IncompatiblePattern (pat, tp)) in
  match pat, tp with
  (* need tone composition! *)
  (* Explicit box unwrapping. *)
  | `Box p, `Box a -> elabPat Tone.(tone * `Iso) pat a
  | `Box _, _ -> fail()
  (* Box auto-unwrapping. Must try this case before others. *)
  (* need tone composition! *)
  | pat, `Box a -> elabPat Tone.(tone * `Iso) pat a
  | #lit as l, tp -> if tp <> Lit.typeOf l then fail()
                     else pure (`Eq (Lit.typeOf l, l))
  | `Wild, tp -> pure `Wild
  | `Var v, tp ->
     (* TODO?: check whether tp is discrete & if so, bind discretely! *)
     tell [tone,v,tp]
     >> withVarAs tone v tp (pure (`Var (Some v)))
  | `Tuple ps, `Tuple tps ->
     list (try List.map2 (elabPat tone) ps tps
           with Invalid_argument _ -> fail())
     => fun ps -> `Tuple ps
  | `Tuple _, _ -> fail()
  | `Tag(n,p), `Sum tps ->
     let tp = try List.assoc n tps with Not_found -> fail() in
     elabPat tone p tp => fun p -> `Tag(n,p)
  | `Tag _, _ -> fail()


(* ---------- Type inference ---------- *)
type expect = tp option
type expInfer = tp exp infer
type alg = expect -> expInfer

let use (v: var): expInfer = fun cx ->
  let tp = Vars.find v cx.vars in
  Vars.singleton v `Id, (tp, `Var v)

let elabExp: (expect -> expInfer) expAlgebra = fun e expect ->
  let open Infer in
  getContext >>= fun cx ->
  let unroll tpname = Types.find tpname cx.types in
  (* checks an inferred type against expect *)
  let got (inferred: tp): tp = match expect with
    | None -> inferred
    | Some wanted when Type.subtype unroll inferred wanted -> wanted
    | _ -> nope (Inferred inferred) in
  let _synth e = e None in
  let check tp e = e (Some tp) in
  let semilattice tp =
    try Backend.semilattice unroll tp
    with Backend.NotSemilattice -> nope (NotSemilattice tp) in
  let checkOnly (f: tp -> tp exp expF infer): expInfer = match expect with
    | Some tp -> pure tp ** f tp
    | None -> nope CanOnlyCheck in
  let patName: pat -> Backend.name = function | `Var v -> Some v | _ -> None in

  match e with
  | #lit as l -> pure (Lit.typeOf l, l)
  | `Var v -> use v
  | `The (tp,e) -> check tp e => fun (_,exp) -> (got tp, exp)
  | `Prim p -> raise TODO
  (* for now, only support checking `Lub expressions. *)
  | `Lub es -> checkOnly (check @> forEach es
                          @> map (fun x -> `Lub x))
  | `Fix (pat, body) ->
     checkOnly **> fun tp ->
     let _mkFix x = `Fix (Backend.zeroExp (semilattice tp), patName pat, x) in
     (* TODO: check pattern is irrefutable *)
     todo()
     (* map mkFix begin
      *   elabPat `Id pat tp >>= fun (vars, backendPat) ->
      *   withVars vars (check tp body) => fun (_, bodyExp) ->
      *   `Case (`Var 0, [backendPat, bodyExp])
      * end *)
  | `Let (ds, body) -> raise TODO
  (* introductions *)
  | `Box e -> raise TODO
  | `Lam (pats, body) ->
     (* TODO: refactor this & `Fix; they have much in common. *)
     (* TODO: frickin' TESTING!!!! *)
     let rec loop pats (tp:tp) = match pats, tp with
       | [], tp -> (check tp body => snd)
       | pat::pats, `Fn(tp_in, tp_out) ->
          todo()
          (* map (fun x -> `Lam (patName pat, x)) begin
           *   elabPat `Id pat tp_in >>= fun (vars, backendPat) ->
           *   map (fun exp -> `Case (`Var 0, [backendPat, exp]))
           *     (withVars vars (loop pats tp_out))
           * end *)
       | (_::_), _ -> nope LamNonFunction
     in checkOnly (loop pats)
  (* | `Lam (pats, body) -> raise TODO (\* checking only! *\) *)
  | `Tuple es -> todo()
     (* map (List.split @> fun (tps,es) -> `Tuple tps, `Tuple es)
      *   (match expect with
      *    | None -> forEach es synth
      *    | Some (`Tuple ts) ->
      *       list (try List.map2 check ts es
      *             with Invalid_argument _ -> nope TupleWrongLength)
      *    | Some _ -> nope InferredTuple) *)
  | `Tag (n,e) ->
     let _get_type = function
       | `Sum nts -> (try List.assoc n nts
                      with Not_found -> nope (TagNotFound n))
       | _ -> nope InferredSum
     in todo()
     (*      e (Option.map get_type expect) >>= fun (tp,exp) ->
      * pure (Option.default (`Sum [n,tp]) expect, `Tag (n,exp)) *)
  | `Set [] -> (match expect with
                | Some (`Set es) -> raise TODO
                | Some _ -> nope (raise TODO)
                | None -> nope (raise TODO))
  | `Set es -> raise TODO
  (* eliminations *)
  | `Unbox e -> raise TODO      (* need to consult my notes for this one *)
  | `App (e1,e2) -> todo()
                    (* e1 None >>= fun (ftp, fexp) ->
                     * let (a,b) = match ftp with `Fn x -> x
                     *                          | _ -> nope AppNonFunction
                     * in e2 (Some a) => fun (_,aexp) -> (got b, `App (fexp,aexp)) *)
  | `For (comps, body) -> raise TODO
  (* TODO: exhaustiveness checking *)
  | `Case (subject, arms) -> raise TODO

let rec infer ((ann,e): expr) (expect: expect): expInfer =
  fun cx ->
  let e': alg expF = Exp.map infer e in
  try elabExp e' expect cx
  (* TODO: give:
   * - line/column information
   * - the expected type, or "could not infer type"
   *)
  with Nope why -> raise (TypeError (explain why))
