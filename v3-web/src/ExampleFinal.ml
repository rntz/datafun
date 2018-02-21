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
  type pat = cx -> tp -> cx * Mid.pat
  type exp = cx -> tp option -> tp * Mid.exp

  exception Fail of string
  exception FailAt of loc * string
  let fail msg = raise (Fail msg)

  module Pat = struct
    module P = Mid.Pat
    let var v cx tp = match List.assoc_opt v cx with
      | None -> ((v,tp)::cx, P.var v)
      (* We can compare x:A with y:B if (A ⊔ B) has equality. I think
       * heterogenous equality, which would work if (A ⊓ B) supports equality,
       * is possible. However, it complicates the type of (=).
       *
       * Ideally we'd like to issue an error here if (A ⊓ B) is empty.
       * For now we omit this.
       *)
      | Some xtp ->
         try (cx, P.eq Type.(equal (join tp xtp)) (Mid.Exp.var v))
         with Type.Incompatible _ -> fail "incompatible types"
            | Type.NoEquality _ -> fail "type does not support equality tests"

    let tag (n:tag) (p:pat) (cx:cx) (tp:tp) = match tp with
      | Sum nts ->
         let (cx, p) = (try p cx (List.assoc n nts)
                        with Not_found -> fail "tag not in sum type")
         in (cx, P.tag n p)
      | _ -> fail "tag pattern must have sum type"
  end

  module Exp = struct
    module E = Mid.Exp

    let synthOnly ((got, exp): (tp * Mid.exp)) (expect: tp option): tp * Mid.exp =
      match expect with
      | None -> (got, exp)
      | Some want -> if Type.subtype got want
                     then (want, exp)
                     else fail "type mismatch"

    let checkOnly (a: tp -> Mid.exp) (expect: tp option): tp * Mid.exp =
      match expect with
      | None -> fail "cannot infer"
      | Some want -> (want, a want)

    let ann loc e cx expect =
      try e cx expect
      with Fail why -> raise (FailAt (loc,why))

    let var v cx = synthOnly
      (try (List.assoc v cx, E.var v)
       with Not_found -> fail "unbound variable")

    let the tp e cx = synthOnly (e cx (Some tp))

    let lam (p:pat) (e:exp) cx = checkOnly **> function
      | Fn(a,b) -> let (cx, p) = p cx a in
                   let (_, e) = e cx (Some b) in
                   E.lam p e
      | _ -> fail "lambdas are functions"

    let app x y cx = synthOnly **>
      let (a,b,xe) = match x cx None with
        | Fn(a,b), exp -> (a,b,exp)
        | _ -> fail "applying non-function" in
      let (_,ye) = y cx (Some a) in
      (b, E.app xe ye)

    let tag (n: tag) (e: exp) cx (expect: tp option) =
      let get_type = function
        | Sum nts -> (try List.assoc n nts
                      with Not_found -> fail "tag not found")
        | _ -> fail "not a sum type" in
      let (tp,e) = e cx Option.(expect => get_type) in
      (Option.default (Sum [n,tp]) expect, E.tag n e)

    (* for now, we can only check case expressions *)
    let case (subj:exp) arms cx = checkOnly **> fun tp ->
      let (subjt, subje) = subj cx None in
      let doArm (pat, exp) =
        let (cx,pat) = pat cx subjt in
        let (_,exp) = exp cx (Some tp) in
        (pat,exp) in
      E.case subje (List.map doArm arms)
  end
end
