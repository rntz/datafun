(* A typechecker/interpreter for a simply typed lambda calculus.
 *
 * A place to play with & demonstrate some of the techniques used in
 * the Datafun typechecker/interpreter/compiler.
 *)
open Sigs
open Util

type loc = Lexing.position * Lexing.position
type var = string
type tag = string

type tp =
  [ `Base
  | `Fn of tp * tp
  | `Sum of (string * tp) list ]

type pat =
  [ `Var of var
  | `Tag of string * pat ]

type 'a expF =
  [ `Var of var
  | `The of tp * 'a
  (* TODO: `Lam of pat list * 'a *)
  | `Lam of pat * 'a
  | `App of 'a * 'a
  (* | `Tuple of 'a list *)
  | `Tag of tag * 'a
  | `Case of 'a * (pat * 'a) list ]

type 'a exp = 'a * 'a exp expF
type expr = loc exp

module Type = struct
  exception Incompatible of tp * tp
  let join (a: tp) (b: tp): tp = if a = b then a else todo()
  let meet (a: tp) (b: tp): tp = if a = b then a else todo()
  let rec subtype (a: tp) (b: tp): bool = a = b || todo()
end


(* Intermediate language, after type checking. *)
module IL = struct
  type equal = [ `Base | `Sum of (tag * equal) list ]

  exception NoEquality of tp
  let rec equal: tp -> equal = function
    | `Base -> `Base
    | `Sum pts -> `Sum (List.map (fun (n,t) -> (n,equal t)) pts)
    | `Fn _ as t -> raise (NoEquality t)

  type pat =
    [ `Var of var
    | `Tag of tag * pat
    | `Eq of equal * exp ]
  and exp =
    [ `Var of var
    | `Lam of pat * exp
    | `Tag of tag * exp
    | `App of exp * exp
    | `Case of exp * (pat * exp) list ]
end


(* The typechecker monad *)
type cx = (var * tp) list
type 'a fail = Ok of 'a | Fail of (expr * string) list
(* Maybe don't use a monad at all?
 * threading context through isn't hard
 * failure can use exceptions
 * what about writing tones?
 * can pass & thread through a hashtable.
 *
 * TODO: investigate this.
 *)
type 'a infer = cx -> 'a fail

module Infer = struct
  let (>>=) a f cx = match a cx with Ok x -> f x cx | Fail msgs -> Fail msgs
  let concat a = a >>= id

  include Idiom(struct
    type 'a t = 'a infer
    let pure x cx = Ok x
    let map f a = a >>= f @> pure
    let ( ** ) a b cx = match a cx, b cx with
      | Ok x, Ok y -> Ok (x,y)
      | Fail xs, Fail ys -> Fail (xs @ ys)
      | Fail msgs, Ok _ | Ok _, Fail msgs -> Fail msgs
  end)

  let getContext cx = Ok cx
  let withContext cx a _ = a cx
  let fail locmsg cx = Fail [locmsg]
  let withVar (var, tp) a cx = a ((var,tp)::cx)
end

(* pattern inference raises exceptions on failure. *)
type 'a patInfer = cx -> cx * 'a
module PatInfer = struct
  include Monad(struct
    type 'a t = 'a patInfer
    let pure x cx = (cx, x)
    let map f a cx = let (cx,x) = a cx in (cx, f x)
    let (>>=) a f cx = let (cx,x) = a cx in f x cx
  end)
end


(* Typechecking *)
type expect = tp option

(* hold on, which exceptions can this generate?
 * - Type.Incompatible
 * - IL.NoEquality
 *
 * argh, and WHEN does it generate them?
 * answer: either after (elabPat pat tp) or after (elabPat pat tp cx).
 *)
let rec elabPat: pat -> tp -> IL.pat patInfer = fun pat tp ->
  let open PatInfer in
  match pat, tp with
  | `Var x, tp ->
     (fun cx -> match List.assoc_opt x cx with
                | None -> ((x,tp)::cx, `Var x)
                (* We can compare x:A with y:B if (A ⊔ B) has equality.
                 * I think heterogenous equality, which would work if (A ⊓ B)
                 * supports equality, is possible. However, it complicates the
                 * type of (=).
                 *
                 * Ideally we'd like to issue an error here if (A ⊓ B) is empty.
                 * For now we omit this.
                 *)
                | Some xtp -> (cx, `Eq (IL.equal (Type.join tp xtp), `Var x)))

  | `Tag(n,p), `Sum nts ->
     let tp = try List.assoc n nts
              with Not_found -> todo() in
     elabPat p tp => C.tag n
  (* TODO: exception *)
  | `Tag(n,p), _ -> raise (todo())

let rec elab: expr -> expect -> (tp * IL.exp) infer =
  fun (loc,expr) expect ->
  let open Infer in
  let fail x = fail ((loc,expr), x) in
  let check tp e = elab e (Some tp) => snd in
  let inferPat p tp =
    getContext >>= fun cx ->
    try pure (elabPat p tp cx)
    with Type.Incompatible _ -> fail "incompatible types"
       | IL.NoEquality _ -> fail "comparing at non-equality type" in

  let withPat p tp body =
    inferPat p tp >>= fun (cx, p) -> withContext cx (body p) in

  let checkOnly (f: tp -> IL.exp infer): (tp * IL.exp) infer =
    match expect with
    | Some tp -> pure tp ** f tp
    | None -> fail "cannot infer type" in
  let synthed (tp, exp) = match expect with
    | None -> pure (tp, exp)
    | Some expected ->
       if Type.subtype tp expected then pure (expected, exp)
       else fail "not a subtype" in

  getContext >>= fun cx ->
  match expr with
  | `Var v -> (try pure (List.assoc v cx, `Var v)
               with Not_found -> fail "unbound variable")
              >>= synthed

  | `The (tp,e) -> elab e (Some tp) >>= synthed

  | `Lam (p,e) ->
     checkOnly
     **> fun tp -> (match tp with `Fn x -> pure x
                                | _ -> fail "lambdas have function type")
     >>= fun (a,b) -> withPat p a (fun p -> C.lam p $ check b e)

  | `App (e1,e2) ->
     elab e1 None >>= (function `Fn(a,b), e1e -> pure (a,b,e1e)
                              | _ -> fail "applying non-function")
     >>= fun (a, b, e1e) -> check a e2
     >>= fun e2e -> synthed (b, `App(e1e,e2e))

  | `Tag (n,e) ->
     let get_type = function
       | `Sum nts -> (try pure (List.assoc n nts)
                      with Not_found -> fail "tag not found")
       | _ -> fail "not a sum type" in
     Infer.option Option.(map get_type expect)
     >>= fun e_expect -> elab e e_expect
     => fun (tp, exp) -> (Option.default (`Sum [n,tp]) expect, `Tag (n,exp))

  | `Case (subj, arms) -> checkOnly **> fun tp ->
     (* for now, we only can _check_ case expressions *)
     elab subj None >>= fun (subjt, subje) ->
     map (fun arms -> `Case(subje, arms))
     **> forEach arms
     **> fun (pat,exp) -> withPat pat subjt (fun p -> pure p ** check tp exp)
