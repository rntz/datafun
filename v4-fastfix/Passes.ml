(* The speedup φ and derivative δ transformations. *)
open Util open Type open Lang

(* A simple pass-through that ignores zero annotations. *)
module DummyZero(S: SIMPLE)
       : ZERO with type tp = S.tp and type term = S.term
= struct
  include S
  let zero _ term = term
end


(* Bidirectional type checking/inference *)
module Surface(Imp: MODAL): sig
  include SURFACE
          with type term = modalcx -> modaltp option -> modaltp * Imp.term
  type cx = modalcx
  val check: term -> cx -> tp -> Imp.term
  val infer: term -> cx -> Imp.tp * Imp.term
end
= struct
  type tp = modaltp
  type cx = modalcx
  type term = cx -> tp option -> tp * Imp.term

  let subtype (a: tp) (b: tp) = a = b

  let scrub: cx -> cx =
    Cx.map (function Box, tp -> Box, tp
                   | (Id|Hidden), tp -> Hidden, tp)

  let complain msg tp = typeError (Printf.sprintf "%s: %s" msg (Type.to_string tp))

  let infer term cx = term cx None
  let check (term: term) (cx: cx) (tp: tp): Imp.term = snd (term cx (Some tp))

  let synth (got: tp) : tp option -> tp = function
    | Some want when not (subtype got want) ->
       typeError (Printf.sprintf "
I need an expression of type %s
     but I found one of type %s" (to_string want) (to_string got))
    | _ -> got

  (* Transparent terms (can either check or synthesize) *)
  let letIn (x: sym) (expr: term) (body: term) (cx: cx) (expect: tp option): tp * Imp.term =
    let exprType, exprX = expr cx None in
    let bodyType, bodyX = body (Cx.add x (Id, exprType) cx) expect in
    bodyType, Imp.letIn exprType bodyType x exprX bodyX

  let letBox (x: sym) (expr: term) (body: term) (cx: cx) (expect: tp option): tp * Imp.term =
    match expr cx None with
    | `Box a, exprX ->
       let bodyTp, bodyX = body (Cx.add x (Box, a) cx) expect in
       bodyTp, Imp.letBox a bodyTp x exprX bodyX
    | a, _ -> complain "cannot unbox non-box type" a

  let letTuple (xs: sym list) (expr: term) (body: term) (cx: cx) (expect: tp option): tp * Imp.term =
    match expr cx None with
    | (`Tuple tps as tupleTp), exprX ->
       let tpxs = try List.map2 (fun tp x -> tp,x) tps xs
                  with Invalid_argument _ -> complain "wrong tuple length" tupleTp in
       let bindings = List.map (fun (tp,x) -> x, (Box,tp)) tpxs in
       let bodyTp, bodyX = body (Cx.add_list bindings cx) expect in
       bodyTp, Imp.letTuple tpxs bodyTp exprX bodyX
    | a, _ -> complain "cannot detuple non-tuple" a

  let box (expr: term) (cx: cx) (expect: tp option): tp * Imp.term =
    let exprExpect = match expect with
      | None -> None
      | Some (`Box a) -> Some a
      | Some tp -> complain "box expression must have box type" tp in
    let tp, exprX = expr (scrub cx) exprExpect in
    `Box tp, Imp.box tp exprX

  let forIn (x: sym) (set: term) (body: term) (cx: cx) (expect: tp option): tp * Imp.term =
    let elemType, setX = match set cx None with
        | `Set a, setX -> a, setX
        | b, _ -> complain "cannot comprehend over non-set" b in
    let bodyType, bodyX = body (Cx.add x (Box, (elemType :> tp)) cx) expect in
    bodyType, Imp.forIn elemType (asLat bodyType) x setX bodyX

  let guard (cond: term) (body: term) (cx: cx) (expect: tp option): tp * Imp.term =
    let bodyType, bodyX = body cx expect in
    bodyType, Imp.guard (asLat bodyType) (check cond cx `Bool) bodyX

  (* Synthesizing terms *)
  let asc (ascribed: tp) (expr: term) (cx: cx) (expect: tp option): tp * Imp.term =
    let tp, impl = expr cx (Some ascribed) in synth tp expect, impl

  let var (x: sym) (cx: cx) (expect: tp option): tp * Imp.term =
    let oops msg = typeError (Printf.sprintf "variable %s is %s" (Sym.to_string x) msg) in
    match (try Cx.find x cx with Not_found -> oops "unbound") with
    | Box, tp -> synth tp expect, Imp.discvar tp x
    | Id, tp -> synth tp expect, Imp.var tp x
    | Hidden, _ -> oops "hidden"

  let app (fnc: term) (arg: term) (cx: cx) (expect: tp option): tp * Imp.term =
    match infer fnc cx with
    | `Fn(a,b), fncX -> synth b expect, Imp.app a b fncX (check arg cx a)
    | a, _ -> complain "cannot apply non-function" a

  let proj (i:int) (e:term) (cx: cx) (expect: tp option): tp * Imp.term =
    match infer e cx with
    | (`Tuple tps as tp), eX ->
       (try synth (List.nth tps i) expect, Imp.proj tps i eX
        with Invalid_argument _ -> complain "tuple too short" tp)
    | a, _ -> complain "cannot project from non-tuple" a

  let equals (e1: term) (e2: term) (cx: cx) (expect: tp option): tp * Imp.term =
    let e1tp, e1x = e1 cx None in
    match firstOrder e1tp with
    | None -> complain "cannot compare at non-equality type" e1tp
    | Some tp -> synth `Bool expect, Imp.equals tp e1x (check e2 cx e1tp)

  let binop (op: binop) (e1: term) (e2: term) (cx: cx) (expect: tp option): tp * Imp.term = match op with
    | `Plus -> synth `Nat expect, Imp.binop op (check e1 cx `Nat) (check e2 cx `Nat)

  let bool (b: bool) (_cx: cx) (expect: tp option): tp * Imp.term =
    synth `Bool expect, Imp.bool b
  let string (s: string) (_cx: cx) (expect: tp option) = synth `String expect, Imp.string s
  let nat (i: int) (_cx: cx) (expect: tp option) = synth `Nat expect, Imp.nat i

  (* Checking terms *)
  let lam (x: sym) (body: term) (cx: cx): tp option -> tp * Imp.term = function
    | Some (`Fn (a,b) as tp) -> tp, Imp.lam a b x (check body (Cx.add x (Id,a) cx) b)
    | Some a -> complain "lambda must have function type" a
    | None -> typeError "cannot infer type for lambda"

  let tuple (terms: term list) (cx: cx): tp option -> tp * Imp.term = function
    | None ->
       let tpterms = List.map (fun term -> term cx None) terms in
       `Tuple List.(map fst tpterms), Imp.tuple tpterms
    | Some (`Tuple tps as tp) ->
       (try tp, Imp.tuple (List.map2 (fun tp term -> term cx (Some tp)) tps terms)
        with Invalid_argument _ -> complain "wrong length tuple" tp)
    | Some a -> complain "tuple must have tuple type" a

  let set (terms: term list) (cx: cx): tp option -> tp * Imp.term = function
    | Some (`Set elemtp as tp) ->
       let f term = check term (scrub cx) (elemtp :> tp) in
       tp, Imp.set elemtp (List.map f terms)
    | Some tp -> complain "set literal must have set type" tp
    | None ->
       match terms with
       | [] -> typeError "cannot infer type for empty set"
       | m::ms ->
          let mtp, mx = infer m (scrub cx) in
          match firstOrder mtp with
          | Some elemtp ->
             let elems = mx :: List.map (fun n -> check n (scrub cx) mtp) ms in
             `Set elemtp, Imp.set elemtp elems
          | None -> complain "set elements must have equality type" mtp

  let union (terms: term list) (cx: cx): tp option -> tp * Imp.term = function
    | None -> typeError "cannot infer type of union"
    | Some tp ->
       tp, Imp.union (asLat tp) (List.map (fun m -> check m cx tp) terms)

  let fix (x: sym) (body: term) (cx: cx): tp option -> tp * Imp.term = function
    | None -> typeError "cannot infer type of fix expression"
    | Some tp ->
       match firstOrder tp with
       | None -> complain "cannot take fixed point at higher-order type" tp
       | Some eqtp ->
          tp,
          check body (scrub cx |> Cx.add x (Id, tp)) tp
          |> Imp.lam tp tp x |> Imp.box (`Fn (tp, tp)) |> Imp.fix (asLat eqtp)
end


(* Dummy pass-through transforms. *)
module DropZeros(Imp: SIMPLE): ZERO with type term = Imp.term
= struct
  include Imp
  let zero _ term = term
end

module DropBoxes(Imp: SIMPLE): MODAL with type term = Imp.term
= struct
  type tp = modaltp
  type term = Imp.term
  let var a = Imp.var (debox a)
  let discvar = var
  let letIn a b = Imp.letIn (debox a) (debox b)
  let lam a b = Imp.lam (debox a) (debox b)
  let app a b = Imp.app (debox a) (debox b)
  let tuple tpterms = Imp.tuple List.(map (fun (a,m) -> debox a, m) tpterms)
  let proj tps = Imp.proj (List.map debox tps)
  let letTuple axs b = Imp.letTuple List.(map (fun (a,x) -> debox a,x) axs) (debox b)
  let string = Imp.string let bool = Imp.bool let nat = Imp.nat
  let ifThenElse a = Imp.ifThenElse (debox a)
  let guard a = Imp.guard (deboxLat a)
  let set a = Imp.set a
  let union a = Imp.union (deboxLat a)
  let forIn a b = Imp.forIn a (deboxLat b)
  let fix = Imp.fix
  let equals = Imp.equals
  let binop = Imp.binop
  let box _a m = m
  let letBox a b = Imp.letIn (debox a) (debox b)
end


module Seminaive(Imp: ZERO): MODAL
       with type term = Imp.term * Imp.term
= struct
  type tp = modaltp
  type term = Imp.term * Imp.term (* φM, δM *)

  (* This may only be used at base types. It almost ignores its argument;
   * however, at sum types, it does depend on the tag. If sum types are not
   * involved, `makeZero` produces a constant expression. In particular, at
   * first-order semilattice types, it produces a bottom expression, which the
   * simplifier will recognize. This aids optimization.
   *)
  let rec makeZero (tp: eqtp) (term: Imp.term): Imp.term = match tp with
    | `Bool -> Imp.bool false
    | `Nat -> Imp.nat 0
    | `String -> Imp.tuple []
    | `Set a -> Imp.set a []
    | `Tuple tps ->
       let dtps = List.map delta (tps :> modaltp list) in
       List.mapi (fun i a -> List.nth dtps i, makeZero a (Imp.proj dtps i term)) tps
       |> Imp.tuple

  (* Wraps makeZero to let the optimizer know we've generated a zero change.
   *
   * TODO: there's redundant work going on here. The zero-change analysis will
   * notice if this is at first-order lattice type and turn it into "empty", which
   * means the effort of makeZero is wasted.
   *)
  let zero (tp: eqtp) (term: Imp.term): Imp.term =
    Imp.zero (tp :> rawtp) (makeZero tp term)

  (* φx = x                 δx = dx *)
  let var (a: tp) (x: sym): term = Imp.var (phi a) x, Imp.var (delta a) (Sym.d x)

  (* If the variable is discrete, we know its derivative is a zero change; so if
   * it's first-order, we can inline zero applied to it. *)
  let discvar (a: tp) (x: sym): term =
    let phix = Imp.var (phi a) x in
    (* phix, match firstOrder a with
     *       | Some eqa -> zero eqa phix
     *       | None -> let da = delta a in
     *                 Imp.zero da (Imp.var da (Sym.d x)) *)
    phix, let da = delta a in Imp.zero da (Imp.var da (Sym.d x))

  (* φ(box M) = φM, δM      δ(box M) = ⟨⟩ *)
  let box (a: tp) (fTerm, dTerm: term): term =
    let fa, da = phiDelta a in
    Imp.tuple [fa, fTerm; da, dTerm],
    Imp.zero (`Tuple []) (Imp.tuple [])

  (* φ(let box x = M in N) = let x,dx = φM in φN
   * δ(let box x = M in N) = let x,dx = φM in δN *)
  let letBox (a: tp) (b: tp) (x: sym) (fExpr, _dExpr: term) (fBody, dBody: term): term =
    let fa,da = phiDelta a and fb,db = phiDelta b and dx = Sym.d x in
    (* let (x,dx) = φM in ... *)
    let binder bodyTp body = Imp.letTuple [fa,x;da,dx] bodyTp fExpr body
    in binder fb fBody, binder db dBody

  (* φ(let x = M in N) = let x = φM in φN
   * δ(let x = M in N) = let x = φM and dx = δM in δN *)
  let letIn (a: tp) (b: tp) (x: sym) (fExpr, dExpr: term) (fBody, dBody: term): term =
    let fA,dA = phiDelta a and fB, dB = phiDelta b and dx = Sym.d x in
    Imp.letIn fA fB x fExpr fBody,
    Imp.letIn fA dB x fExpr (Imp.letIn dA dB dx dExpr dBody)

  (* φ(λx.M) = λx.φM        δ(λx.M) = λx dx. δM *)
  let lam (a: tp) (b: tp) (x: sym) (fBody, dBody: term): term =
    let fA,dA = phiDelta a and fB,dB = phiDelta b in
    Imp.lam fA fB x fBody,
    Imp.lam fA (`Fn (dA, dB)) x (Imp.lam dA dB (Sym.d x) dBody)

  (* φ(M N) = φM φN         δ(M N) = δM φN δN *)
  let app (a: tp) (b: tp) (fFnc, dFnc: term) (fArg, dArg: term): term =
    let fA,dA = phiDelta a and fB,dB = phiDelta b in
    Imp.app fA fB fFnc fArg,
    Imp.app dA dB (Imp.app fA (`Fn (dA, dB)) dFnc fArg) dArg

  (* φ(M,N) = φM,φN         δ(M,N) = δM,δN *)
  let tuple (elts: (tp * term) list) =
    Imp.tuple (List.map (fun (a, (fE,_)) -> phi a, fE) elts),
    Imp.tuple (List.map (fun (a, (_,dE)) -> delta a, dE) elts)

  (* φ(πᵢ M) = πᵢ φM        δ(πᵢ M) = πᵢ δM *)
  let proj (tps: tp list) (i: int) (fTerm, dTerm: term) =
    let ftps, dtps = List.(map phiDelta tps |> split) in
    Imp.proj ftps i fTerm, Imp.proj dtps i dTerm

  (* φ(let (x,y) = M in N) = let (x,y) = φM in φN
   * δ(let (x,y) = M in N) = let (x,y) = φM and (dx,dy) = δM in δN *)
  let letTuple (tpxs: (tp * sym) list) (bodyTp: tp)
               (fTuple, dTuple: term) (fBody, dBody: term): term =
    let fBodyTp, dBodyTp = phiDelta bodyTp in
    let f (a,x) = let (fa,da) = phiDelta a in (fa, x), (da, Sym.d x) in
    let ftpxs, dtpxs = List.(map f tpxs |> split) in
    Imp.letTuple ftpxs fBodyTp fTuple fBody,
    Imp.letTuple ftpxs dBodyTp fTuple (Imp.letTuple dtpxs dBodyTp dTuple dBody)

  (* φ(s: string) = s   δ(s: string) = () *)
  let string (s: string): term = Imp.string s, Imp.zero (`Tuple []) (Imp.tuple [])

  (* φ(n: nat) = n      δ(n: nat) = 0 *)
  let nat (i: int): term = Imp.nat i, Imp.zero `Nat (Imp.nat 0)

  (* φ(b: bool) = b     δ(b: bool) = false *)
  let bool (b: bool): term = Imp.bool b, Imp.zero `Bool (Imp.bool false)

  (* φ(if M then N else O) = if φM then φN else φO
   * δ(if M then N else O) = if φM then δN else δO  -- condition can't change! *)
  let ifThenElse (a: tp) (fCond,_dCond: term) (fThn,dThn: term) (fEls,dEls: term): term =
    let fA,dA = phiDelta a in
    Imp.ifThenElse fA fCond fThn fEls, Imp.ifThenElse dA fCond dThn dEls

  (* Most semilattice operations (except fix) are implementable at higher-order
   * types. However, their φ/δ translations are different. For first-order
   * semilattice types A, φA = ΔA and ⊕ = ∨. At higher-order types, this is not
   * true, and the correct approach is to eta-expand until it is true. However,
   * I don't expect to be using semilattice operations at functional types in
   * any example programs, so to simplify the implementation I error on higher-
   * order semilattice types.
   *
   * For more info, See seminaive/seminaive.pdf.
   *)
  let phiEqLat (a: tp semilat): Imp.tp semilat =
    match firstOrderLat a with
    | Some eqa -> (eqa :> Imp.tp semilat)
    | None -> todo "semilattice operations only implemented for first-order data"

  (* φ(when (M) N) = when (φM) φN
   * δ(when (M) N) = if φM then δN else when (δM) φN ∨ δN
   *
   * The latter assumes φA = ΔA and ⊕ = ∨. (See phiFirstOrderLat.) *)
  let guard (a: tp semilat) (fCond,dCond: term) (fBody,dBody: term): term =
    let fA = phiEqLat a in
    Imp.guard fA fCond fBody,
    Imp.ifThenElse (fA :> rawtp) fCond dBody
      (Imp.guard fA dCond (Imp.union fA [fBody; dBody]))

  (* φ({M}) = {φM}          δ({M}) = ∅ *)
  let set (a: eqtp) (elts: term list) =
    Imp.set a (List.map fst elts),
    Imp.zero (`Set a) (Imp.set a [])

  (* φ(M ∨ N) = φM ∨ φN     δ(M ∨ N) = δM ∨ δN *)
  let union (a: tp semilat) (terms: term list) =
    Imp.union (phiLat a) (List.map fst terms),
    Imp.union (deltaLat a) (List.map snd terms)

  let forIn (a: eqtp) (b: tp semilat) (x: sym) (fExpr, dExpr: term) (fBody, dBody: term) =
    let fb = phiEqLat b in
    let da = delta (a :> tp) in
    let dx = Sym.d x in
    let phix = Imp.var (phi (a :> tp)) x in (* NB (phi a = a) b/c eqtype *)
    let fBody' = Imp.letIn da (fb :> rawtp) dx (zero a phix) fBody in
    let dBody' = Imp.letIn da (fb :> rawtp) dx (zero a phix) dBody in
    (* φ(for (x in M) N) = for (x in φM) φN {dx ↦ 0 x}
     * dx ↦ 0 x will be inlined by discvar. *)
    Imp.forIn a fb x fExpr fBody,
    (* Assuming φB = ΔB and ⊕ = ∨ (see phiFirstOrderLat),
     *
     * δ(for (x in φM) φN)
     * =  (for (x in δM)      φN {dx ↦ 0 x})
     *   ∨ for (x in φM ∪ δM) δN {dx ↦ 0 x}
     *
     * dx ↦ 0 x will be inlined by discvar.
     *)
    Imp.union fb
      [ Imp.forIn a fb x dExpr fBody'
      ; Imp.forIn a fb x (Imp.union (`Set a) [fExpr;dExpr]) dBody' ]

  (* φ(fix M) = semifix φM
   * δ(fix M) = zero ⊥ = ⊥ *)
  let fix (a: eqtp semilat) (fFunc, _dFunc: term) =
    Imp.semifix a fFunc,
    Imp.zero (a :> rawtp) (Imp.union (a :> rawtp semilat) [])

  (* φ(M == N) = φM == φN       δ(M == N) = false *)
  let equals (a: eqtp) (fM, _dM: term) (fN, _dN: term): term =
    Imp.equals a fM fN,
    Imp.zero `Bool (Imp.bool false)

  (* φ(M + N) = φM + φN         δ(M + N) = φM + φN
   *
   * The δ-translation is inefficient. I don't think it can be more efficient
   * in general, but it might be able to handle some special-cases.
   *)
  let binop (op: binop) (fM, _dM: term) (fN, _dN: term): term = match op with
    | `Plus -> Imp.binop `Plus fM fN, Imp.binop `Plus fM fN
end


(* Zero-change rewriting.
 *
 * Replaces zero changes at lattice type with bottom.
 * TODO: should this also replace zero changes at first-order non-lattice type,
 * to aid simplifier? a la makeZero from Seminaive()?
 *
 * Recognizes zero changes in various ways. Currently, it recognizes:
 *
 * - zero changes indicated by the previous layer, which should be all
 *   derivatives of "obviously discrete" things like discrete variables,
 *   set literals, boolean literals, ⊥, box, etc. FIXME implement this.
 *
 * - zero changes applied to other zero changes, like (dr x dx) when r & x were
 *   both discrete variables in the source program.
 *
 * - letIn bindings where the body is a zero-change.
 *
 * - variables bound by letIn to zero-changes it recognizes.
 *
 * It does not recognize:
 *
 * - letTuple bindings where the body is a zero-change.
 * - Variables bound by letTuple to zero-changes it recognizes.
 * - Tupling zero-changes.
 * - Projecting from zero-changes.
 * - Unions of zero-changes.
 * - if-then-elses or guards which always return zero changes.
 * - Anything to do with binops.
 *
 * or anything else. I should figure out if there are reasonable examples where
 * this matters, add those as tests, and implement them; or else comment that I
 * could find no reasonable examples.
 *)
module ZeroChange(Imp: SIMPLE): sig
  type state = Zero | AppliedZero
  include ZERO with type term = state cx -> state option * Imp.term
  val finish: term -> Imp.term
end = struct
  type tp = rawtp
  type state = Zero | AppliedZero
  type value = state option * Imp.term
  type term = state cx -> value

  let finish (term: term): Imp.term = snd (term Cx.empty)
  let roll (a: tp) (ann, term: value): value =
    (* NB. we can only turn FIRST-ORDER zero changes into bottom.
     * higher-order changes have more structure. *)
    ann, (match ann, isLat a, firstOrder (a :> modaltp) with
          | Some Zero, Some sl, Some _ -> Imp.union sl []
          | _ -> term)

  let notZero (term: Imp.term): value = None, term
  let is (a: tp) (s: state) (term: Imp.term): value = roll a (Some s, term)

  let zero a term cx = is a Zero (term cx |> snd)

  let var a x cx = roll a (Cx.find_opt x cx, Imp.var a x)

  let letIn a b x (expr: term) (body: term) (cx: state cx) =
    let (exprAnn, exprTerm) = expr cx in
    let (bodyAnn, bodyTerm) = body (Cx.add_opt x exprAnn cx) in
    roll b (bodyAnn, Imp.letIn a b x exprTerm bodyTerm)

  let lam a b x (body: term) (cx: state cx): value =
    notZero (Imp.lam a b x (snd (body cx)))

  let app a b (fnc: term) (arg: term) (cx: state cx): value =
    let fncS, fncT = fnc cx and argS, argT = arg cx in
    roll b
      ((match fncS, argS with Some AppliedZero, Some Zero -> Some Zero
                            | Some Zero, _ -> Some AppliedZero
                            | _ -> None),
       Imp.app a b fncT argT)

  let tuple (tpterms: (tp * term) list) cx =
    tpterms
    |> List.map (fun (tp,term) -> tp, snd (term cx))
    |> Imp.tuple |> notZero

  let proj tps i (term: term) cx =
    notZero (Imp.proj tps i (snd (term cx)))

  let letTuple tpxs bodyTp expr body cx =
    Imp.letTuple tpxs bodyTp (expr cx |> snd) (body cx |> snd)
    |> notZero

  let string s _cx = notZero (Imp.string s)
  (* TODO: wait, why isn't this zero if x is false? *)
  let bool x _cx = notZero (Imp.bool x)
  let nat i _cx = notZero (Imp.nat i)

  let ifThenElse a cnd thn els cx =
    notZero (Imp.ifThenElse a (snd (cnd cx)) (snd (thn cx)) (snd (els cx)))

  let guard a cnd body cx =
    notZero (Imp.guard a (cnd cx |> snd) (body cx |> snd))

  let set a terms cx =
    notZero (Imp.set a (List.map (fun term -> snd (term cx)) terms))

  let union a terms cx =
    notZero (Imp.union a (List.map (fun term -> snd (term cx)) terms))

  let forIn a b x set body cx =
    Imp.forIn a b x (snd (set cx)) (snd (body cx)) |> notZero

  let fix (a: eqtp semilat) fnc cx = Imp.fix a (fnc cx |> snd) |> notZero
  let semifix (a: eqtp semilat) fncderiv cx =
    Imp.semifix a (fncderiv cx |> snd) |> notZero
  let equals a tm1 tm2 cx =
    notZero (Imp.equals a (tm1 cx |> snd) (tm2 cx |> snd))
  let binop op tm1 tm2 cx =
    notZero (Imp.binop op (tm1 cx |> snd) (tm2 cx |> snd))
end


(* Optimization/simplification. Currently just bottom-propagation. *)
module Simplify(Imp: SIMPLE): sig
  include SIMPLE
  val finish: term -> Imp.term
end = struct
  type tp = rawtp
  type isEmpty = tp semilat
  (* Invariant: in any value of the form (x, Some a), x = Imp.union a []. *)
  type value = Imp.term * isEmpty option
  (* TODO: Is this (isEmpty cx) parameter doing any useful work?
   * Find some test cases that exercise it, or else remove it. *)
  type term = isEmpty cx -> value

  let finish (term: term): Imp.term = fst (term Cx.empty)

  let empty (a: tp semilat): value = Imp.union a [], Some a
  let full (term: Imp.term): value = term, None
  let propagate (term: Imp.term): isEmpty option -> value =
    function None -> full term | Some a -> empty a

  let var a x cx = propagate (Imp.var a x) (Cx.find_opt x cx)

  let letIn a b x (expr:term) (body:term) (cx: isEmpty cx): value =
    let exprX, exprE = expr cx in
    let bodyX, bodyE = body (Cx.add_opt x exprE cx) in
    propagate (Imp.letIn a b x exprX bodyX) bodyE

  let lam a b x body cx = match body cx with
    | _, Some b -> empty (`Fn(a,b))
    | bodyX, _ -> full (Imp.lam a b x bodyX)

  let app a b fnc arg cx = match fnc cx with
    | _, Some `Fn(_,y) -> empty y
    | fncX, _ -> full (Imp.app a b fncX (fst (arg cx)))

  let tuple (tpterms: (tp * term) list) cx: value =
    let f (a,m) = let mX,mE = m cx in (a,mX), mE in
    let tptms, empties = List.(map f tpterms |> split) in
    propagate (Imp.tuple tptms) Option.(all empties |> map (fun x -> `Tuple x))

  let proj tps i (term: term) cx: value = match term cx with
    | _termX, Some `Tuple lats -> empty (List.nth lats i)
    | termX, _ -> full (Imp.proj tps i termX)

  let letTuple tpxs bodyTp expr body cx =
    let exprX, exprE = expr cx in
    let knowns = match exprE with
      | Some `Tuple lats -> List.map2 (fun (_,x) lat -> x,lat) tpxs lats
      | Some _ -> impossible "invalid let-tuple"
      | None -> [] in
    let bodyX, bodyE = body (Cx.add_list knowns cx) in
    propagate (Imp.letTuple tpxs bodyTp exprX bodyX) bodyE

  let string s _cx = Imp.string s, None
  let bool x _cx = Imp.bool x, if x then None else Some `Bool
  let nat x _cx = Imp.nat x, if x = 0 then Some `Nat else None

  let ifThenElse a cnd thn els cx =
    match cnd cx, thn cx, els cx with
    (* If condition is false, give back els. *)
    | (_, Some _), _, els -> els
    (* If both branches are always empty, return empty. *)
    | _, (_, Some lat), (_, Some _) -> empty lat
    (* Otherwise, default. *)
    | (cndX, _), (thnX,_), (elsX,_) -> full (Imp.ifThenElse a cndX thnX elsX)

  let guard a cnd body cx =
    match cnd cx, body cx with
    | (_, Some _), _ | _, (_, Some _)-> empty a
    | (cndX,_), (bodyX, None) -> full (Imp.guard a cndX bodyX)

  let set a terms cx = match List.map (fun tm -> fst (tm cx)) terms with
    | [] -> empty (`Set a)
    | terms -> full (Imp.set a terms)

  let union a terms cx =
    let f tm = match tm cx with _tmX, Some _ -> [] | tmX, None -> [tmX] in
    match List.(concat (map f terms)) with
    | [] -> empty a
    | [b] -> full b
    | elems -> full (Imp.union a elems)

  let forIn a b x set body cx =
    match set cx, body cx with
    | (setX, None), (bodyX, None) -> full (Imp.forIn a b x setX bodyX)
    | _ -> empty b
  let fix (a: eqtp semilat) fnc cx = match fnc cx with
    | _, Some _ -> empty (a :> tp semilat)
    | fncX, None -> full (Imp.fix a fncX)
  let semifix (a: eqtp semilat) fncderiv cx = match fncderiv cx with
    | _, Some _ -> empty (a :> tp semilat)
    | fdX, None -> full (Imp.semifix a fdX)
  let equals a tm1 tm2 cx = full (Imp.equals a (fst (tm1 cx)) (fst (tm2 cx)))
  let binop op e f cx = full (Imp.binop op (fst (e cx)) (fst (f cx)))
end


(* Gives distinct variables distinct and human-readable names.
 * I'm not happy with this. It's too complicated.
 *
 * TODO: find example programs where this transformation is actually needed
 * to make variable names unique! it should be possible, by naming
 * source variables "dx" etc.
 *
 * TODO: I really need to test this but I haven't. also the parser won't
 * generate the most interesting edge-cases.
 *)
module PrettyName(Imp: SIMPLE) : sig
  include SIMPLE
  val finish: term -> sym Cx.t * Imp.term
end = struct
  (* We pass along:
   *
   * 1. A hash table mapping symbols to the names assigned them.
   *
   * 2. A set of the variable names we've used so far.
   *
   * TODO describe algorithm in more detail.
   *)
  type cx = { vars: (sym, sym) Hashtbl.t
            ; used: (string, unit) Hashtbl.t }

  type tp = rawtp
  type term = cx -> Imp.term

  (* Yields a map from free variables to their renamed versions, and
   * the generated term. *)
  let finish (term: term): sym Cx.t * Imp.term =
    let cx = { vars = Hashtbl.create 5; used = Hashtbl.create 5 } in
    let impl = term cx in
    Hashtbl.fold Cx.add cx.vars Cx.empty, impl

  (* This function must be total, pure, and injective on `i`, but not
   * necessarily injective on `name`! *)
  let rename (name: string): int -> string = function
    | 0 -> name
    | i -> name ^ string_of_int i

  let make_var (cx: cx) (oldsym: sym): sym =
    (* Generate an unused name for the variable. *)
    let base = Sym.name oldsym in
    let rec fresh i = let name = rename base i in
                     if Hashtbl.mem cx.used name then fresh (i+1) else name in
    let name = fresh 0 in
    let newsym = Sym.fresh name in
    Hashtbl.add cx.used name ();
    Hashtbl.add cx.vars oldsym newsym;
    newsym

  (* Binds a variable within `body`. Really need tests & test coverage here. *)
  let bind (x: sym) (cx: cx) (body: cx -> 'a): sym * 'a =
    (* Remember what x is currently bound to; we'll need it later. *)
    let prior = Hashtbl.find_opt cx.vars x in
    (* Visit the body. This might find uses of the variable `x` and generate
     * a new name for it, which will be recorded in `cx`. *)
    let body_result = body cx in
    (* Figure out what variable to replace x by. *)
    let newx = match prior, Hashtbl.find_opt cx.vars x with
      (* If x wasn't bound and still isn't, we didn't use it. Make a dummy var.
       * FIXME: relies on actual variables never having the name "_"! *)
      | None, None -> Sym.fresh "_"
      (* If x wasn't bound but now is, pop the binding and use it.
       * Also remove the used variable name.
       * Wait, is this right? *)
      | None, Some y -> Hashtbl.remove cx.vars x;
                        (* NB. requires Sym.(name (fresh s)) = s. *)
                        Hashtbl.remove cx.used (Sym.name y);
                        y
      (* If x was bound, it should still be bound to the same thing. *)
      | Some _, None -> impossible "used variable was destroyed?!"
      | Some a, Some b when a <> b -> impossible "variable mutated?!"
      | Some _, Some b -> b
    in newx, body_result

  let var (a: tp) (x: sym) (cx: cx): Imp.term =
    Imp.var a (try Hashtbl.find cx.vars x with Not_found -> make_var cx x)

  let letIn a b x expr body cx =
    let expr = expr cx in
    let x, body = bind x cx body in
    Imp.letIn a b x expr body

  (* some mind-melting code right here *)
  let letTuple tpxs a expr body cx =
    let expr = expr cx in
    let f (tp,x) body cx = let x, (tpxs,body) = bind x cx body in (tp,x)::tpxs, body in
    let tpxs, body = List.fold_right f tpxs (fun cx -> [], body cx) cx in
    Imp.letTuple tpxs a expr body

  let lam a b x body cx = let x, body = bind x cx body in Imp.lam a b x body
  (* Order of visitation unspecified but who cares? *)
  let app a b fnc arg cx = Imp.app a b (fnc cx) (arg cx)
  let tuple tpterms cx =
    Imp.tuple (List.map (fun (tp, term) -> tp, term cx) tpterms)
  let proj tps i term cx = Imp.proj tps i (term cx)
  let string s _cx = Imp.string s
  let bool b _cx = Imp.bool b
  let nat i _cx = Imp.nat i
  let ifThenElse a cnd thn els cx = Imp.ifThenElse a (cnd cx) (thn cx) (els cx)
  let guard lat cnd thn cx = Imp.guard lat (cnd cx) (thn cx)
  let set elemtp terms cx = Imp.set elemtp (List.map (fun x -> x cx) terms)
  let union lat terms cx = Imp.union lat (List.map (fun x -> x cx) terms)
  let forIn elemtp lat x expr body cx =
    let expr = expr cx in
    let x, body = bind x cx body in
    Imp.forIn elemtp lat x expr body
  let fix tp body cx = Imp.fix tp (body cx)
  let equals tp e1 e2 cx = Imp.equals tp (e1 cx) (e2 cx)
  let binop op e1 e2 cx = Imp.binop op (e1 cx) (e2 cx)
  let semifix tp body cx = Imp.semifix tp (body cx)
end
