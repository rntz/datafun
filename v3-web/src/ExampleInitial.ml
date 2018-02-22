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

             
(* ----- Tones ----- *)
type tone = Id | Op | Iso | Path
module Tone = struct
  (* TODO: comment about order of composition *)
  let compose (a: tone) (b: tone): tone = match a,b with
    | x, Id | Id, x -> x
    | Op, Op -> Id
    | Iso, _ | Path, _ -> a   (* hi priority, must come first *)
    | _, Iso | _, Path -> b   (* lo priority, comes later *)
  let ( * ) = compose

  let meet (a: tone) (b: tone): tone = match a, b with
    | Iso, _ | _, Iso | Id, Op | Op, Id -> Iso
    | x, Path | Path, x -> x
    | Id, Id | Op, Op -> a

  let (<=) (a: tone) (b: tone): bool = match a,b with
    | Iso, _ | _, Path -> true
    | Id, Id | Op, Op -> true
    | _, Iso | Path, _ | Op, Id | Id, Op -> false
end

module type TONES = sig
  type t
  val mkEmpty: unit -> t
  val use: t -> var -> tone -> unit
  (* push binds a variable *)
  val push: t -> var -> unit
  (* pop unbinds a variable, returning its tone of use *)
  val pop: t -> var -> tone
end

module Tones: TONES = struct
  open Hashtbl
  type t = (var, tone) Hashtbl.t
  let mkEmpty () = create ~random:true 10
  let use tbl v how = find tbl v |> Tone.meet how |> replace tbl v
  let push tbl v = add tbl v Path
  let pop tbl v = let tone = find tbl v in remove tbl v; tone
end


(* ----- Types, patterns, expressions ----- *)
type tp =
  [ `Base
  | `Box of tp
  | `Fn of tp * tp
  | `Sum of (string * tp) list ]

type pat =
  [ `Var of var
  | `Box of pat
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

  exception NoEquality of tp
  type equal = [ `Base | `Sum of (tag * equal) list ]
  let rec equal: tp -> equal = function
    | `Base -> `Base
    | `Sum pts -> `Sum (List.map (fun (n,t) -> (n,equal t)) pts)
    | `Fn _ as t -> raise (NoEquality t)
    | `Box p -> equal p
end


(* Intermediate language, after type checking. *)
module IL = struct
  type pat =
    [ `Var of var
    | `Tag of tag * pat
    | `Eq of Type.equal * exp ]
  and exp =
    [ `Var of var
    | `Lam of pat * exp
    | `Tag of tag * exp
    | `App of exp * exp
    | `Case of exp * (pat * exp) list ]
end


(* ----- Typechecking ----- *)
type cx = (var * tp) list
type expect = tp option
type tones = Tones.t
exception Fail of loc * string

(* if I ever add disjunction/conjunction patterns, modifying cx
 * in place will cause me trouble; I'll need to rewrite this.
 *
 * do I really need to have both patTones & useTones???
 *)
let rec elabPat: loc -> cx ref -> tones -> tones -> tone -> tp -> pat
                 -> IL.pat =
  fun loc cx patTones useTones tone tp pat ->
  let recurAt = elabPat loc cx patTones useTones in
  let recur = recurAt tone in
  let fail msg = raise (Fail (loc,msg)) in
  match tp, pat with
  (* explicit/automatic unboxing *)
  | `Box a, `Box p | `Box a, p ->
  (* Path because elimination (Box a -> a) is Path-toned.
   * TODO: think about composition order here! *)
     recurAt Tone.(tone * Path) a p

  | _, `Box p -> fail "matching box pattern against non-box type"

  | tp, `Var v ->
     begin match List.assoc_opt v !cx with
     | None ->
        Tones.push useTones v;
        Tones.push patTones v; Tones.use patTones v tone;
        cx := (v,tp) :: !cx;
        `Var v
     | Some vtp ->
        Tones.use patTones v tone;
        Tones.use useTones v Iso;
        `Eq (Type.(equal (join tp vtp)), `Var v)
     end

  | `Sum nts, `Tag (n,p) ->
     let tp = try List.assoc n nts
              with Not_found -> fail "tag not in sum type" in
     `Tag(n, recur tp p)

  | _, `Tag _ -> fail "tag must have sum type"

let rec elab: cx -> tones -> expect -> expr -> tp * IL.exp =
  fun cx tones expect (loc,expr) ->
  let fail msg = raise (Fail (loc,msg)) in
  let synthesize (got, e) =
    match expect with
    | None -> (got, e)
    | Some want when Type.(got <= want) -> (want, e)
    | Some want -> fail "inferred type not a subtype of expected type" in
  let needType () = match expect with
    | None -> fail "I can't infer the type here; could you annotate it for me?"
    | Some tp -> tp in

  let checking f = let t = needType() in (t, f t) in

  let infer = elab cx tones None in
  let check tp = elab cx tones (Some tp) in

  match expr with
  | `Var v ->
     let tp = try List.assoc v cx with Not_found -> fail "unbound variable" in
     Tones.use tones v Id;
     synthesize (tp, `Var v)

  | `The(a,x) -> synthesize (check a x)

  | `Lam(p,x) -> todo()

  | `App(x,y) ->
     let (a,b,xe) = match infer x with
       | `Fn(a,b), xe -> a,b,xe
       | _ -> fail "applying non-function" in
     let (_, ye) = check a y in
     synthesize (b, `App(xe,ye))

  | `Tag(n,x) ->
     let get_type = function
       | `Sum nts -> (try List.assoc n nts
                      with Not_found -> fail "tag not found")
       | _ -> fail "not a sum type" in
     let (xt,xe) = elab cx tones Option.(expect => get_type) x in
     (Option.default (`Sum [n,xt]) expect, `Tag(n,xe))

  | `Case(subj, arms) ->
     (* for now, we can only check case expressions. *)
     checking **> fun tp ->
     (* we need to capture the way `subj` uses variables, and modify that
      * according to how the pattern & body use `subj`.
      * so we create an empty Tones.t to pass in. *)
     let subjTones = Tones.mkEmpty() in
     let (subjt, subje) = elab cx subjTones None subj in
     let doArm (pat, exp) =
       (* Likewise, we capture how `pat` & `exp` use variables. *)
       let useTones = Tones.mkEmpty () in
       (* patTones is the "mediating" tones. TODO: explain better. *)
       let (patTones, bodyCx, pat) = elabPat loc cx useTones Id subjt pat in
       let (_, exp) = elab bodyCx useTones (Some tp) exp in
       (* We pop all the variables that pat bound & pushed onto newTones.
        * This tells us how (pat => exp) uses them.
        * We compose these with patTones and take the meet, then compose
        * the result onto the remaining tones in newTones.
        *
        * This tells us how the overall case-expression uses the variables that
        * `subj` uses.
        *)
       todo()
     in
     (* this isn't gonna work, we need to extract some information, probably *)
     todo(); `Case (subje, List.map doArm arms)
                   

(* let rec elab: cx -> tones -> expect -> (tp * IL.exp) =
 *   fun cx tones expect (loc,expr) ->
 *   let fail msg = raise (Fail (loc, msg)) in
 *   let check tp e = elab e (Some tp) => snd in
 *   let inferPat p tp =
 *     getContext >>= fun cx ->
 *     try pure (elabPat p tp cx)
 *     with Type.Incompatible _ -> fail "incompatible types"
 *        | Type.NoEquality _ -> fail "comparing at non-equality type" in
 * 
 *   let withPat p tp body =
 *     inferPat p tp >>= fun (cx, p) -> withContext cx (body p) in
 * 
 *   let checkOnly (f: tp -> IL.exp infer): (tp * IL.exp) infer =
 *     match expect with
 *     | Some tp -> pure tp ** f tp
 *     | None -> fail "cannot infer type" in
 *   let synthed (tp, exp) = match expect with
 *     | None -> pure (tp, exp)
 *     | Some expected ->
 *        if Type.subtype tp expected then pure (expected, exp)
 *        else fail "not a subtype" in
 * 
 *   getContext >>= fun cx ->
 *   match expr with
 *   | `Var v -> (try pure (List.assoc v cx, `Var v)
 *                with Not_found -> fail "unbound variable")
 *               >>= synthed
 * 
 *   | `The (tp,e) -> elab e (Some tp) >>= synthed
 * 
 *   | `Lam (p,e) ->
 *      checkOnly
 *      **> fun tp -> (match tp with `Fn x -> pure x
 *                                 | _ -> fail "lambdas have function type")
 *      >>= fun (a,b) -> withPat p a (fun p -> C.lam p $ check b e)
 * 
 *   | `App (e1,e2) ->
 *      elab e1 None >>= (function `Fn(a,b), e1e -> pure (a,b,e1e)
 *                               | _ -> fail "applying non-function")
 *      >>= fun (a, b, e1e) -> check a e2
 *      >>= fun e2e -> synthed (b, `App(e1e,e2e))
 * 
 *   | `Tag (n,e) ->
 *      let get_type = function
 *        | `Sum nts -> (try pure (List.assoc n nts)
 *                       with Not_found -> fail "tag not found")
 *        | _ -> fail "not a sum type" in
 *      Infer.option Option.(map get_type expect)
 *      >>= fun e_expect -> elab e e_expect
 *      => fun (tp, exp) -> (Option.default (`Sum [n,tp]) expect, `Tag (n,exp))
 * 
 *   | `Case (subj, arms) -> checkOnly **> fun tp ->
 *      (\* for now, we only can _check_ case expressions *\)
 *      elab subj None >>= fun (subjt, subje) ->
 *      map (fun arms -> `Case(subje, arms))
 *      **> forEach arms
 *      **> fun (pat,exp) -> withPat pat subjt (fun p -> pure p ** check tp exp) *)
