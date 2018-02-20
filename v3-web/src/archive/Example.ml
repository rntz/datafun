(* A typechecker/interpreter for a simply typed lambda calculus.
 *
 * A place to play with & demonstrate some of the techniques used in
 * the Datafun typechecker/interpreter/compiler.
 *)
open Sigs
open Util

type loc = Lexing.position * Lexing.position
type var = string

type tp =
  [ `Base
  | `Fn of tp * tp
  | `Tuple of tp list ]

type pat =
  [ `Wild
  | `Var of var
  | `Tuple of pat list ]

type 'a expF =
  [ `Var of var
  | `The of tp * 'a
  (* TODO: `Lam of pat list * 'a *)
  | `Lam of var * 'a
  | `App of 'a * 'a
  | `Tuple of 'a list
  | `Case of 'a * (pat * 'a) list ]

(* Annotated expressions. *)
type 'a exp = 'a * 'a exp expF
type expr = loc exp


(* Subtyping *)
let rec subtype (a: tp) (b: tp): bool = match a,b with
  | `Base, `Base -> true
  | `Fn(a1,b1), `Fn(a2,b2) -> subtype a2 a1 && subtype b1 b2
  | `Tuple xs, `Tuple ys ->
     (try List.for_all2 subtype xs ys
      with Invalid_argument _ -> false)
  | `Base, _ | `Fn _, _ | `Tuple _, _ -> false


(* Expressions: building & traversing *)
module Exp = struct
  include Traverse(struct
    type 'a t = 'a expF
    module Seq(M: IDIOM) = struct
      open M
      let traverse(f: 'a -> 'b M.t): 'a expF -> 'b expF M.t = function
        | `Var x -> pure (`Var x)
        | `The(t,e) -> Tag.the t $ f e
        | `Lam(x,e) -> Tag.lam x $ f e
        | `App(e1,e2) -> Tag.app $ f e1 ** f e2
        | `Tuple es -> Tag.tuple $ forEach es f
        | `Case (e,arms) -> Tag.case $ f e ** forEach arms (onSnd f)
    end
  end)

  type ('a,'b) arr =
    { var: var -> 'b
    ; the: tp -> 'a -> 'b
    ; lam: var -> 'a -> 'b
    ; app: 'a * 'a -> 'b
    ; tuple: 'a list -> 'b
    ; case: 'a * (pat * 'a) list -> 'b }

  (* let flub: 'a expF *)

  (* Pure folds over annotated expressions. *)
  type ('r,'a) fold = 'a * 'r expF -> 'r
  let rec fold: ('r,'a) fold -> 'a exp -> 'r =
    fun f (ann,exp) -> f (ann, map (fold f) exp)
end


(* The typechecker monad *)
type cx = (var * tp) list
type 'a fail = Ok of 'a | Fail of (loc * string) list
type 'a infer = cx -> 'a fail

module Infer = struct
  let (>>=) k f cx = match k cx with Ok x -> f x cx | Fail msgs -> Fail msgs
  let concat k = k >>= id

  include Idiom(struct
    type 'a t = 'a infer
    let pure x cx = Ok x
    let map f k = k >>= f @> pure
    let ( ** ) g h cx = match g cx, h cx with
      | Ok x, Ok y -> Ok (x,y)
      | Fail xs, Fail ys -> Fail (xs @ ys)
      | Fail msgs, Ok _ | Ok _, Fail msgs -> Fail msgs
  end)

  let getContext cx = Ok cx
  let locally f k cx = k (f cx)
  let withContext cx = locally (fun _ -> cx)

  let fail locmsg cx = Fail [locmsg]

  let withVar (var, tp) (k: 'a infer): 'a infer = fun cx -> k ((var,tp)::cx)
end

(* Typechecking *)
type expect = tp option
type 'a inferExp = expect -> (tp * 'a) infer
(* A backend is a "type-annotated expression algebra". *)
type 'a backend = ('a, tp) Exp.fold

module ThisParameterIsRigidDammit(X: sig type t end) = struct
  let elabPat: tp -> pat -> 'a =
    todo()

  let elab: X.t backend -> (X.t inferExp, loc) Exp.fold =
    fun backend (loc, exp) expect ->
    let open Infer in
    let fail msg = Infer.fail (loc,msg) in
    let synth x = x None in
    let check tp x = x (Some tp) in
    let synthed ((tp, exp): tp * X.t expF): (tp * X.t expF) infer = match expect with
      | None -> pure (tp, exp)
      | Some expected ->
         if subtype tp expected then pure (tp, exp)
         else fail "not a subtype" in
    let checkOnly f = match expect with
      | Some tp -> pure tp ** f tp
      | None -> fail "cannot infer type for this kind of expression" in
    getContext >>= fun cx ->
    begin match exp with
    | `Var v -> (try synthed (List.assoc v cx, `Var v)
                 with Not_found -> fail "unbound variable")
    | `The(tp,x) -> check tp x >>= fun (tp, e) -> synthed (tp, `The(tp,e))
    | `Lam(v,x) -> checkOnly **> begin function
       | `Fn(a,b) -> withVar (v,a) (check b x => snd => Tag.lam v)
       | _ -> fail "lambdas are functions"
       end
    | `App(x,y) ->
       synth x >>= (function `Fn(a,b), xe -> pure (a,b,xe)
                           | _ -> fail "applying non-function")
       >>= fun (a,b,xe) -> check a y
       >>= fun (_, ye) -> synthed (b, `App(xe,ye))
    | `Tuple xs ->
       map (List.split @> fun (tps,es) -> `Tuple tps, `Tuple es)
           (match expect with
            | None -> forEach xs synth
            | Some (`Tuple ts) ->
               (try list (List.map2 check ts xs)
                with Invalid_argument _ -> fail "tuple of wrong length")
            | Some _ -> fail "not a tuple")
    | `Case(subj,arms) ->
       synth subj >>= fun (subjt, subje) ->
       (* TODO: check every pattern against subjt. *)
       todo()
    end
    => fun (tp,e) -> (tp, backend (tp,e))
end
