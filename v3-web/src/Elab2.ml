open Sigs
open Util
open Ast

module Cx = Map.Make(String)

exception TypeError of loc * string

type cx = {types: tp Cx.t; vars: (tone * tp) Cx.t}
type expect = tp option

let withTone tone cx =
  (* ugh, is there a cleaner way to do this? *)
  let f s = match tone with
    | `Id -> s
    | `Op -> Tone.(s * `Op)
    | `Iso -> Tone.(s * `Path)
    | `Path -> raise (Bug "this should never happen")
  in {cx with vars = Cx.map (fun (tone,tp) -> (f tone, tp)) cx.vars}

let find_type cx name = Cx.find name cx.types

(* if I ever add disjunction/conjunction patterns, modifying cx
 * in place will cause me trouble; I'll need to rewrite this. *)
let rec elabPat: loc -> cx ref -> tone -> tp -> pat -> IL.pat =
  fun loc cx tone tp pat ->
  let fail () = raise (TypeError (loc, "bad type for pattern")) in
  let unroll name = try find_type !cx name
                    with Not_found -> fail() in
  match pat, tp with
  | #lit as l, tp -> if tp <> Lit.typeOf l then fail()
                     else `Eq (Lit.typeOf l, l)
  | `Wild, _ -> `Wild
  | `Var v, tp ->
     begin match Cx.find_opt v !cx.vars with
     | None -> cx := {!cx with vars = Cx.add v (tone, tp) !cx.vars}; `Var v
     | Some (`Iso,tp) ->
        (try `Eq (IL.equal unroll tp, `Var v)
         with IL.NoEquality a -> fail())
     | Some (_, tp) -> fail()
     end
  (* tuples *)
  | `Tuple ps, `Tuple tps ->
     `Tuple (try List.map2 (elabPat loc cx tone) tps ps
             with Invalid_argument _ -> fail())
  | `Tuple _, _ -> fail()
  (* sums *)
  | `Tag(n,p), `Sum tps ->
     let tp = try List.assoc n tps with Not_found -> fail() in
     `Tag(n, elabPat loc cx tone tp p)
  | `Tag _, _ -> fail()

let rec elabExp: cx -> expect -> expr -> tp * IL.exp =
  fun cx expect (loc, exp) ->
  let fail msg = raise (TypeError (loc, msg)) in
  let unroll tpname = try find_type cx tpname
                      with Not_found -> fail "type not defined" in
  let infer = elabExp cx None in
  let check tp = elabExp cx (Some tp) in
  let checkAt tp e = snd (check tp e) in
  let needType () = match expect with
    | None -> fail "I can't infer the type here; could you annotate it for me?"
    | Some tp -> tp in
  let checking f = let t = needType() in (t, f t) in
  let synthesize (got, e) = match expect with
    | None -> (got, e)
    | Some want when Type.(got <= want) -> (want, e)
    | Some want -> fail "inferred type not a subtype of expected type" in

  match exp with
  | #lit as l -> synthesize (Lit.typeOf l, l)
  | `Var v ->
     let (tone, tp) = try Cx.find v cx.vars
                      with Not_found -> fail "unbound variable" in
     if Tone.(tone <= `Id) then synthesize (tp, `Var v)
     else fail "I can't be sure that your use of this variable is safe"

  | `The (tp, e) -> synthesize (check tp e)

  | `Prim p -> todo()

  | `Lub es ->
     (* TODO: allow inferring lubs. *)
     let tp = needType() in
     (tp, `Lub (IL.semilattice unroll tp, List.map (checkAt tp) es))

  | `Fix (pat, body) ->
     let tp = needType() in
     let cx = ref cx in
     (* TODO: check exhaustiveness *)
     let pat = elabPat loc cx `Id tp pat in
     let _, body = elabExp !cx (Some tp) body in
     tp, `Fix (IL.fix unroll tp, pat, body)

  | `Let (decls, body) ->
     let cx = ref cx in
     let bindings = elabDecls `Id loc cx decls in
     let bind (p,e) body = `Let(p,e,body) in
     let (tp, body) = elabExp !cx expect body in
     (tp, List.fold_right bind bindings body)

  | `Lam(ps,body) ->
     (* TODO: check irrefutability *)
     let cx = ref cx in
     let rec lam ps tp = match ps, tp with
       | [], _ -> checkAt tp body
       | p::ps, `Fn(tone,a,b) -> let p = elabPat loc cx tone a p in
                                 `Lam(p, lam ps b)
       | p::ps, _ -> fail "too few arguments to lambda"
     in checking (lam ps)

  | `Tuple es ->
     let (tps,es) = List.split **> match expect with
       | None -> List.map infer es
       | Some (`Tuple tps) -> List.map2 check tps es
       | Some _ -> fail "tuple must have tuple type" in
     (`Tuple tps, `Tuple es)

  | `Tag (n,x) ->
     let get_type = function
       | `Sum nts -> (try List.assoc n nts
                      with Not_found -> fail "tag not present in type")
       | _ -> fail "tagged expression must have sum type" in
     let (xt,xe) = elabExp cx (Option.map get_type expect) x in
     (Option.default (`Sum [n,xt]) expect, `Tag(n,xe))

  | `Set es ->
     let f = function `Set a -> a
                    | _ -> fail "set literal must have set type" in
     let (tps, es) = List.split (List.map (elabExp cx Option.(expect => f)) es)
     in (match expect, tps with
         | Some tp, _ -> tp
         | None, [] -> fail "cannot infer type of empty set literal"
         | None, tp::tps -> `Set (List.fold_left (Type.join unroll) tp tps)),
        `Set es

  | `App (x,y) ->
     let (tone, a, b, xe) = match infer x with
       | `Fn(tone,a,b), xe -> (tone,a,b,xe)
       | _ -> fail "applying non-function" in
     let (_, ye) = elabExp (withTone tone cx) (Some a) y in
     synthesize (b, `App(xe,ye))

  | `For (comps, body) ->
     let cx, comps = elabComps loc cx comps in
     let (bodyt, bodye) = elabExp cx expect body in
     (try bodyt, `For (IL.semilattice unroll bodyt, comps, bodye)
      with IL.NotSemilattice _ -> fail "comprehension at non-semilattice type")

  (* NB. only discrete `Case is allowed for now. *)
  | `Case (subj, arms) ->
     (* TODO: exhaustiveness checking *)
     let (subjt, subje) = elabExp (withTone `Iso cx) None subj in
     (* TODO: allow inferring `Case expressions *)
     let tp = needType() in
     let doArm (pat,exp) =
       let cx = ref cx in
       let pat = elabPat loc cx `Iso subjt pat in
       (pat, snd (elabExp !cx (Some tp) exp))
     in tp, `Case (subje, List.map doArm arms)

and elabComps (loc: loc) (cx: cx) (comps: expr comp list): cx * IL.comp list =
  let cx = ref cx in
  let comps = List.map (elabComp loc cx) comps in
  !cx, comps

and elabComp: loc -> cx ref -> expr comp -> IL.comp =
  fun loc cx comp ->
  let fail msg = raise (TypeError (loc, msg)) in
  match comp with
  | When x -> let (_, e) = elabExp !cx (Some `Bool) x in `When e
  | In (p, x) ->
     let (elemt, xe) = match elabExp !cx None x with
       | `Set a, xe -> a,xe
       | _, _ -> fail "for-loop over something that isn't a set" in
     (* TODO: check irrefutability. *)
     let p = elabPat loc cx `Iso elemt p in
     `In (p, xe)

and elabDecls: tone -> loc -> cx ref -> expr decl list -> (IL.pat * IL.exp) list =
  fun defaultTone loc cx decls ->
  Lists.(decls >>= elabDecl defaultTone loc cx)

and elabDecl: tone -> loc -> cx ref -> expr decl -> (IL.pat * IL.exp) list =
  fun defaultTone loc cx decl ->
  match decl with
  (* TODO: check well-formedness of type! *)
  | Type (name, tp) ->
     cx := {!cx with types = Cx.add name tp !cx.types};
     []

  | Def (pat, tone, tp, exp) ->
     let (tp, exp) = elabExp !cx tp exp in
     let pat = elabPat loc cx (Option.default defaultTone tone) tp pat in
     [pat,exp]