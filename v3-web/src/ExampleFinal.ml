(* open Sigs
 * open Util
 * 
 * type loc = Lexing.position * Lexing.position
 * type var = string
 * type tag = string
 * 
 * 
 * (\* ----- Tones ----- *\)
 * type tone = Id | Op | Iso | Path
 * module Tone = struct
 *   let compose (a: tone) (b: tone): tone = match a,b with
 *     | x, Id | Id, x -> x
 *     | Op, Op -> Id
 *     | _, Iso | _, Path -> b   (\* hi priority, must come first *\)
 *     | Iso, _ | Path, _ -> a   (\* lo priority, comes later *\)
 *   let ( * ) = compose
 * 
 *   let meet (a: tone) (b: tone): tone = match a, b with
 *     | Iso, _ | _, Iso | Id, Op | Op, Id -> Iso
 *     | x, Path | Path, x -> x
 *     | Id, Id | Op, Op -> a
 * 
 *   let (<=) (a: tone) (b: tone): bool = match a,b with
 *     | Iso, _ | _, Path -> true
 *     | Id, Id | Op, Op -> true
 *     | _, Iso | Path, _ | Op, Id | Id, Op -> false
 * end
 * 
 * module type TONES = sig
 *   type t
 *   val mkEmpty: unit -> t
 *   val use: t -> var -> tone -> unit
 *   (\* push binds a variable *\)
 *   val push: t -> var -> unit
 *   (\* pop unbinds a variable, returning its tone of use *\)
 *   val pop: t -> var -> tone
 * end
 * 
 * module Tones: TONES = struct
 *   open Hashtbl
 *   type t = (var, tone) Hashtbl.t
 *   let mkEmpty () = create ~random:true 10
 *   let use tbl v how = find tbl v |> Tone.meet how |> replace tbl v
 *   let push tbl v = add tbl v Path
 *   let pop tbl v = let tone = find tbl v in remove tbl v; tone
 * end
 * 
 * 
 * (\* ----- Types ----- *\)
 * type tp = Base | Fn of tp * tp | Sum of (tag * tp) list
 * module Type = struct
 *   let rec join (a: tp) (b: tp): tp = if a = b then a else todo()
 *   let rec meet (a: tp) (b: tp): tp = if a = b then a else todo()
 *   let rec (<=) (a: tp) (b: tp): bool = a = b || todo()
 * 
 *   exception NoEquality of tp
 *   exception Incompatible of tp * tp
 *   type equal = [`Base | `Sum of (tag * equal) list]
 *   let rec equal: tp -> equal = function
 *     | Base -> `Base
 *     | Sum pts -> `Sum (List.map (fun (n,t) -> (n,equal t)) pts)
 *     | Fn _ as t -> raise (NoEquality t)
 * end
 * 
 * 
 * (\* ----- Signatures ----- *\)
 * module type FRONT = sig
 *   type pat
 *   type exp
 * 
 *   module Pat: sig
 *     (\* problem: automatic unboxing. argh!
 *      * wants to be type-directed! *\)
 *     val var: var -> pat
 *     val tag: tag -> pat -> pat
 *     (\* TODO: *\)
 *     (\* val box: pat -> pat *\)
 *   end
 * 
 *   module Exp: sig
 *     val ann: loc -> exp -> exp
 *     val var: var -> exp
 *     val the: tp -> exp -> exp
 *     val lam: pat -> exp -> exp
 *     val app: exp -> exp -> exp
 *     val tag: tag -> exp -> exp
 *     val case: exp -> (pat * exp) list -> exp
 *   end
 * end
 * 
 * module type MIDDLE = sig
 *   type pat
 *   type exp
 * 
 *   module Pat: sig
 *     val var: var -> pat
 *     val tag: tag -> pat -> pat
 *     val eq: Type.equal -> exp -> pat
 *   end
 * 
 *   module Exp: sig
 *     val var: var -> exp
 *     val lam: pat -> exp -> exp
 *     val tag: tag -> exp -> exp
 *     val app: exp -> exp -> exp
 *     val case: exp -> (pat * exp) list -> exp
 *   end
 * end
 * 
 * 
 * (\* ----- Typechecking/elaboration ----- *\)
 * module Front(Mid: MIDDLE) = struct
 *   exception Fail of string
 *   exception FailAt of loc * string
 *   let fail msg = raise (Fail msg)
 * 
 *   (\* pattern & expression semantics *\)
 *   type cx = (var * tp) list
 *   type tones = Tones.t
 *   (\* bugger. *\)
 *   (\* type pat = <run: 'a.
 *    *                  cx -> tones -> tp ->
 *    *                  (\\* continuation-passing! *\\)
 *    *                  (cx -> tones -> 'a) -> 'a > *\)
 *   (\* won't this work? *\)
 *   type pat = cx -> tones -> tp -> Mid.pat * (var * tone) list * cx
 * 
 *   type exp = cx -> tones -> tp option -> tp * Mid.exp
 * 
 *   module Pat = struct
 *     module P = Mid.Pat
 *     let var v cx tones tp = match List.assoc_opt v cx with
 *       (\* PROBLEM: need to BIND a variable in tones
 *        * - yet somehow communicate what tone it's bound at
 *        * to the outside!
 *        *
 *        * we really do want an update monad here, I think.
 *        * ok, so inline it.
 *        *\)
 *       | None -> (P.var v, [v,Id], (v,tp)::cx)
 *       (\* We can compare x:A with y:B if (A ⊔ B) has equality. I think
 *        * heterogenous equality, which would work if (A ⊓ B) supports equality,
 *        * is possible. However, it complicates the type of (=).
 *        *
 *        * Ideally we'd like to issue an error here if (A ⊓ B) is empty.
 *        * For now we omit this.
 *        *\)
 *       | Some vtp ->
 *          Tones.use tones v Iso;
 *          let equal =
 *            try Type.(equal (join tp vtp))
 *            with Type.NoEquality _ -> fail "type does not support equality tests"
 *               | Type.Incompatible _ -> fail "incompatible types" in
 *          (P.eq equal (Mid.Exp.var v), [], cx)
 * 
 *     let tag (n:tag) (p:pat) (cx:cx) tones (tp:tp) = match tp with
 *       | Sum nts ->
 *          let (p, binds, cx) = (try p cx tones (List.assoc n nts)
 *                                with Not_found -> fail "tag not in sum type")
 *          in (P.tag n p, binds, cx)
 *       | _ -> fail "tag pattern must have sum type"
 *   end
 * 
 *   module Exp = struct
 *     module E = Mid.Exp
 * 
 *     (\* type exp = cx -> tones -> tp option -> tp * Mid.exp *\)
 * 
 *     let infers ((got, exp): (tp * Mid.exp)) (expect: tp option): tp * Mid.exp =
 *       match expect with
 *       | None -> (got, exp)
 *       | Some want when Type.(got <= want) -> (want,exp)
 *       | Some want -> fail "type mismatch"
 * 
 *     let checks (a: tp -> Mid.exp) (expect: tp option): tp * Mid.exp =
 *       match expect with
 *       | None -> fail "cannot infer"
 *       | Some want -> (want, a want)
 * 
 *     let ann (loc:loc) (e:exp) cx tones expect =
 *       try e cx tones expect
 *       with Fail why -> raise (FailAt (loc,why))
 * 
 *     let var v cx tones =
 *       let tp = try List.assoc v cx
 *                with Not_found -> fail "unbound variable" in
 *       Tones.use tones v Id;
 *       infers (tp, E.var v)
 * 
 *     let the tp e cx tones = infers (e cx tones (Some tp))
 * 
 *     (\* PROBLEM: need to bind a variable in tones! *\)
 *     let lam (p:pat) (e:exp) cx tones = checks **> function
 *       | Fn(a,b) -> let (cx, p) = p cx tones a in
 *                    let (_, e) = e cx (Some b) in
 *                    E.lam p e
 *       | _ -> fail "lambdas are functions"
 * 
 *     let app x y cx = infers **>
 *       let (a,b,xe) = match x cx None with
 *         | Fn(a,b), exp -> (a,b,exp)
 *         | _ -> fail "applying non-function" in
 *       let (_,ye) = y cx (Some a) in
 *       (b, E.app xe ye)
 * 
 *     let tag (n: tag) (e: exp) cx (expect: tp option) =
 *       let get_type = function
 *         | Sum nts -> (try List.assoc n nts
 *                       with Not_found -> fail "tag not found")
 *         | _ -> fail "not a sum type" in
 *       let (tp,e) = e cx Option.(expect => get_type) in
 *       (Option.default (Sum [n,tp]) expect, E.tag n e)
 * 
 *     (\* for now, we can only check case expressions *\)
 *     let case (subj:exp) arms cx = checks **> fun tp ->
 *       let (subjt, subje) = subj cx None in
 *       let doArm (pat, exp) =
 *         let (cx,pat) = pat cx subjt in
 *         let (_,exp) = exp cx (Some tp) in
 *         (pat,exp) in
 *       E.case subje (List.map doArm arms)
 *   end
 * end *)
