open Sigs
open Util

type loc = Lexing.position * Lexing.position
type var = string
type tag = string

type tp = Base | Fn of tp * tp | Sum of (tag * tp) list

module Type = struct
  let rec join (a: tp) (b: tp): tp = if a = b then a else todo()
  let rec meet (a: tp) (b: tp): tp = if a = b then a else todo()
  let rec subtype (a: tp) (b: tp): bool = a = b || todo()

  exception NoEquality of tp
  exception Incompatible of tp * tp
  type equal = [`Base | `Sum of (tag * equal) list]
  let rec equal: tp -> equal = function
    | Base -> `Base
    | Sum pts -> `Sum (List.map (fun (n,t) -> (n,equal t)) pts)
    | Fn _ as t -> raise (NoEquality t)
end

module type FRONT = sig
  type pat
  type exp

  module Pat: sig
    val var: var -> pat
    val tag: tag -> pat -> pat
  end

  module Exp: sig
    val ann: loc -> exp -> exp
    val var: var -> exp
    val the: tp -> exp -> exp
    val lam: pat -> exp -> exp
    val app: exp -> exp -> exp
    val tag: tag -> exp -> exp
    val case: exp -> (pat * exp) list -> exp
  end
end

module type MIDDLE = sig
  type pat
  type exp

  module Pat: sig
    val var: var -> pat
    val tag: tag -> pat -> pat
    val eq: Type.equal -> exp -> pat
  end

  module Exp: sig
    val var: var -> exp
    val lam: pat -> exp -> exp
    val tag: tag -> exp -> exp
    val app: exp -> exp -> exp
    val case: exp -> (pat * exp) list -> exp
  end
end


(* Frontend functor - does typechecking/elaboration *)
module Front(Mid: MIDDLE) = struct
  (* types are syntactic *)
  type cx = (var * tp) list

  (* patterns & expressions are semantic *)
  type 'a fail = Ok of 'a | Fail of (loc * string) list
  type 'a expM = cx -> loc -> 'a fail
  type 'a patM = cx -> loc -> (cx * 'a) fail

  type pat = tp -> Mid.pat patM
  type exp = tp option -> (tp * Mid.exp) expM

  let fail msg loc = Fail [loc, msg]

  module Pat = struct
    module M = Monad(struct
      type 'a t = 'a patM
      let pure x cx loc = Ok (cx, x)
      let (>>=) a f cx loc = match a cx loc with
        | Ok (cx,x) -> f x cx loc
        | Fail errs -> Fail errs
    end)
    open M
    let getContext cx loc = Ok (cx,cx)

    module P = Mid.Pat
    let var v cx loc tp =
      match List.assoc_opt v cx with
      | None -> Ok ((v,tp)::cx, P.var v)
      | Some vtp ->
         try Ok (cx, P.eq Type.(equal (join tp vtp)) (Mid.Exp.var v))
         with Type.Incompatible _ -> fail "incompatible types" loc
            | Type.NoEquality _ -> fail "type does not support equality tests" loc

    let tag (n:tag) (p:pat) = todo()
  end

  module Exp = struct
    module E = Mid.Exp

    let ann (loc:loc) (e:exp) = todo()

    let var v = todo()

    let the (tp:tp) (e:exp) = todo()

    let lam (p:pat) (e:exp) = todo()

    let app (x:exp) (y:exp) = todo()

    let tag (n: tag) (e: exp) = todo()

    (* for now, we can only check case expressions *)
    let case (subj:exp) (arms:(pat*exp)list) = todo()
  end
end
