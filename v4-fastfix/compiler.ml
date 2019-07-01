(*
===== TODO =====

- Asymptotic speedup benchmarks!
- More tests!
- A pass-through transform from MODAL to SIMPLE, to compare against Seminaive.

POST DEADLINE:
- A parser.
- Sum types.
- Produce cleaner, more human-readable Haskell
  OR
- A pretty-printer.

===== DESIGN as of February 2019 =====

All tagless-final. Compiler flowchart:

    BIDIR: Bidirectional Datafun
      |
      | typecheck
      V
    MODAL: Explicit modal Datafun
      |
      | φ/δ seminaive magic
      V
    SIMPLE: Non-monotone λ-calculus with fix & fast-fix
      |
      | simplify
      V
    SIMPLE: Non-monotone λ-calculus with fix & fast-fix, with
      |     some simplifications/optimizations applied.
      |
      | compile to Haskell
      V
    Haskell code

===== OPTIMIZATION =====

The simplifier performs the following optimizations:

- Eliminating/propagating bottoms (eg. empty sets and false).
- Eliminating "if"s & "when"s whose conditions are constantly false.

Is that all I need? TODO: Consider the derivatives of the following:

- relation intersection
- relation composition (see icfp19/examples.org)
- transitive closure

TODO: I'd also like to avoid binding unused discrete zero-change variables, eg.
in φ and δ for "for". Approaches:

1. Ignore it.

2. Substitute in the zero-change where needed. This lets the simplifier
   eliminate it if possible. This is also what we do in the paper. This is more or
   less what we currently do, a bit hackishly.

3. Analyse whether the variable is used when φ/δing the interior expression and
   use this to decide whether to bind it.

===== KNOWN BUGS/DESIGN FLAWS =====

FIXME: Currently we don't ban putting functions inside sets; however, the
Haskell type-checker will probably catch this because it won't be able to derive
Ord.

We inherit variable shadowing behavior from our target language (currently
Haskell).

It's not clear how best to deal with n-tuples. We currently compile them to
Haskell tuples of the same length. This makes tuple & letTuple easy. However, it
makes proj hard, because Haskell has no "get the nth field" syntax. Also Haskell
has no way to generically derive Preord or Semilat for tuples of all sizes. An
alternative would be encoding n-tuples for n > 2 into nested pairs. This
complicates tuple & letTuple.

===== GRIPES =====

This design involves passing types explicitly everywhere, which would be fine if
we weren't also computing with those types. But we are computing with them;
we're applying phi and delta to them. And this means we'll end up doing a
superlinear amount of work because we'll recompute the adjusted phi/delta types
at each node in the syntax tree. If we instead worked bidirectionally the whole
way through, I believe we could avoid this. But, this would require more
involved plumbing boilerpate.

However, I suspect the total amount of type computation will be negligible
anyway, and compilation speed isn't the point here anyway; this is just a proof
of concept.

*)

exception TODO of string
exception Impossible of string
exception TypeError of string

let todo msg = raise (TODO msg)
let impossible msg = raise (Impossible msg)
let typeError msg = raise (TypeError msg)


(* Utility modules *)
module Option = struct
  type 'a t = 'a option
  let map f = function None -> None | Some x -> Some (f x)
  let all (l: 'a option list): 'a list option =
    let rec loop acc = function
      | [] -> Some (List.rev acc)
      | None :: xs -> None
      | Some x :: xs -> loop (x::acc) xs
    in loop [] l
end

(* A module for building large strings efficiently.
 * I could probably use Buffer, but it has an imperative interface. *)
module StringBuilder: sig
  type t
  val finish: t -> string
  val string: string -> t
  val int: int -> t
  val (^): t -> t -> t
  val concat: t -> t list -> t
end = struct
  type t = string list -> string list
  (* this assumes String.concat is efficient; if not, rewrite using Buffer. *)
  let finish t = String.concat "" (t [])
  let string s rest = s :: rest
  let int i = string (string_of_int i)
  let (^) x y rest = x (y rest)
  let concat sep: t list -> t = function
    | [] -> fun s -> s
    | [t] -> t
    | t::ts -> fun rest ->
               t (List.fold_right (fun t rest -> sep (t rest)) ts rest)
end


(* Strings with a unique identifier and a derivative degree. The "derivative
   degree" makes it easy, given a variable, to make up a variable standing for
   its derivative. This is kind of a hack, but the alternatives are:

   1. Passing contexts mapping variables to their derivative variables; or
   2. weak hashtable magic; or
   3. functorizing everything over the type of symbols/variables.

   All of which seem like more trouble than they're worth.
 *)
type sym = {name: string; id: int; degree: int}
module Sym = struct
  type t = sym
  let compare = Pervasives.compare
  let next_id = ref 0
  let nextId () = let x = !next_id in next_id := x + 1; x
  let gen name = {name = name; id = nextId(); degree = 0}
  (* it is important that the `d` function be deterministic *)
  let d x = {name = x.name; id = x.id; degree = 1+x.degree}

  (* to_uid is injective over syms generated through the Sym interface, although
   * not over all possible syms. In particular, it relies on the invariant that
   * x.id = y.id implies x.name = y.name, (although not x.degree = y.degree).
   *
   * In principle I could use the module system to enforce this interface,
   * but for ease of debugging I do not. *)
  let to_uid x =
    let d = match x.degree with
      | 0 -> "" | 1 -> "d" | d -> "d" ^ string_of_int d
    in Printf.sprintf "%s%s_%i" d x.name x.id

  (* Yields a hopefully human-friendly name. For now just use to_uid. *)
  let to_string = to_uid
end

(* Contexts mapping variables to stuff. *)
module Cx = struct
  include Map.Make(Sym)
  (* Prefers later bindings to earlier ones. *)
  let from_list l = List.fold_left (fun cx (k,v) -> add k v cx) empty l
  let add_list l cx = union (fun k x y -> Some x) (from_list l) cx
  let add_opt k vopt cx = match vopt with None -> cx | Some v -> add k v cx
end
type 'a cx = 'a Cx.t

(* Oh god types. *)
type ('a,'b) weird = [ `Bool | `String | `Set of 'a | `Tuple of 'b list ]
type eqtp = (eqtp, eqtp) weird
type firstorder = [ `Bool | `String | `Set of eqtp ]
type 'a maketypes = [ (eqtp, 'a) weird | `Fn of 'a * 'a ]

(* Frontend, modal types. *)
type modaltp = [ modaltp maketypes | `Box of modaltp ]
(* Backend, non-modal types. *)
type rawtp = rawtp maketypes
(* Semilattices, parameterized by underlying types *)
type 'a semilat =
  [ `Bool
  | `Set of eqtp
  | `Tuple of 'a semilat list
  | `Fn of 'a * 'a semilat ]

let rec firstOrder: modaltp -> eqtp option = function
  | #firstorder as a -> Some a
  | `Fn _ | `Box _ -> None
  | `Tuple tps ->
     Option.(List.map firstOrder tps |> all |> map (fun x -> `Tuple x))

let rec debox: modaltp -> rawtp = function
  | #firstorder as a -> a
  | `Box a -> debox a
  | `Fn (a,b) -> `Fn (debox a , debox b)
  | `Tuple tps -> `Tuple List.(map debox tps)

(* phi corresponds to Φ, except it drops □. *)
let rec phi: modaltp -> rawtp = function
  | #firstorder as a -> a
  | `Tuple tps -> `Tuple (List.map phi tps)
  | `Box a -> (`Tuple [phi a; delta a])
  | `Fn (a,b) -> `Fn (phi a, phi b)

(* delta corresponds to ΔΦ (_not_ to Δ alone), except it drops □. *)
and delta: modaltp -> rawtp = function
  | (`Bool | `Set _) as a -> a
  | `String | `Box _ -> `Tuple []        (* discrete types don't change *)
  | `Tuple tps -> `Tuple List.(map delta tps)
  | `Fn (a,b) -> `Fn(phi a, `Fn(delta a, delta b))

let phiDelta x = phi x, delta x

(* Convince OCaml's type system of various refinement properties. *)
let firstOrderLat: modaltp semilat -> eqtp semilat option = Obj.magic firstOrder
let deboxLat: modaltp semilat -> rawtp semilat = Obj.magic debox
let deltaEq: eqtp -> eqtp = Obj.magic delta
let phiLat: modaltp semilat -> rawtp semilat = Obj.magic phi
let deltaLat: modaltp semilat -> rawtp semilat = Obj.magic delta
let phiDeltaLat: modaltp semilat -> rawtp semilat * rawtp semilat =
  Obj.magic phiDelta


(* ===== THE LANGUAGE, more or less =====
 *
 * M,N ::= x | λx.M | M N
 *       | (M0,...,Mn) | πᵢ M | let (x0,...,xn) = M in N
 *       | true | false | if M then N else O
 *       | ⊥ | M ∨ N | {M} | for (x in M) N | when (M) N
 *       | [M] | let [x] = M in N
 *       | M = N
 *)

(* For now, no typing contexts or variable usage/freeness information. *)
module type BASE = sig
  type tp
  type term
  val var: tp -> sym -> term
  val letIn: tp -> tp -> sym -> term -> term -> term
  val lam: tp -> tp -> sym -> term -> term
  val app: tp -> tp -> term -> term -> term
  val tuple: (tp * term) list -> term
  val proj: tp list -> int -> term -> term
  val letTuple: (tp * sym) list -> tp -> term -> term -> term
  val string: string -> term
  val bool: bool -> term
  val ifThenElse: tp -> term -> term -> term -> term
  val guard: tp semilat -> term -> term -> term
  (* set A [M0;...;Mn] = {M0,...,Mn} : {A} *)
  val set: eqtp -> term list -> term
  (* union A [M0;...;Mn] = M0 ∨ ... ∨ Mn : A *)
  val union: tp semilat -> term list -> term
  (* forIn A B x M N = for (x : A in M) do N : B *)
  val forIn: eqtp -> tp semilat -> sym -> term -> term -> term
  val fix: eqtp semilat -> term -> term
  val equals: eqtp -> term -> term -> term
end

module type MODAL = sig
  include BASE with type tp = modaltp
  (* var is now for monotone variables only *)
  val discvar: tp -> sym -> term (* for discrete variables *)
  val box: tp -> term -> term
  val letBox: tp -> tp -> sym -> term -> term -> term
end

module type SIMPLE = sig
  include BASE with type tp = rawtp
  val semifix: eqtp semilat -> term -> term
end

module type BIDIR = sig
  type tp = modaltp
  type term
  type expr

  (* inferring exprs *)
  val asc: tp -> term -> expr
  val var: sym -> expr
  val app: expr -> term -> expr
  val proj: int -> expr -> expr
  val equals: expr -> expr -> expr

  (* checking terms *)
  val expr: expr -> term
  val letIn: sym -> expr -> term -> term
  val string: string -> term
  val bool: bool -> term
  val ifThenElse: term -> term -> term -> term
  val guard: term -> term -> term
  val lam: sym -> term -> term
  val tuple: term list -> term
  val letTuple: sym list -> expr -> term -> term
  val set: term list -> term
  val union: term list -> term
  val forIn: sym -> expr -> term -> term
  val box: term -> term
  val letBox: sym -> expr -> term -> term
  val fix: sym -> term -> term
end


(* Bidirectional type checking/inference *)
type mode = Id | Box | Hidden
type modalcx = (mode * modaltp) Cx.t

module Typecheck(Imp: MODAL): BIDIR
     with type term = modalcx -> modaltp -> Imp.term
     with type expr = modalcx -> modaltp * Imp.term
= struct
  type tp = modaltp
  type cx = modalcx
  type term = cx -> tp -> Imp.term
  type expr = cx -> tp * Imp.term

  let subtype (a: tp) (b: tp) = a = b

  let scrub: cx -> cx =
    Cx.map (function Box, tp -> Box, tp
                   | (Id|Hidden), tp -> Hidden, tp)

  let rec asLat: 'a -> 'a semilat = function
    | `Bool -> `Bool
    | `Set a -> `Set a
    | `Fn (a,b) -> `Fn (a, asLat b)
    | `Tuple tps -> `Tuple (List.map asLat tps)
    | `String | `Box _ -> typeError "not a semilattice type"

  (* checking terms *)
  let expr (expr: expr) (cx: cx) (tp: tp): Imp.term =
    let exprType, exprX = expr cx in
    if subtype exprType tp then exprX
    else typeError "inferred type does not match annotation"

  let letIn (x: sym) (expr: expr) (body: term) (cx: cx) (tp: tp): Imp.term =
    let exprType, exprX = expr cx in
    Imp.letIn exprType tp x exprX (body (Cx.add x (Id,exprType) cx) tp)

  let string (s: string) (cx: cx) = function
    | `String -> Imp.string s
    | _ -> typeError "strings must have string type"

  let bool (b: bool) (cx: cx) = function
    | `Bool -> Imp.bool b
    | _ -> typeError "booleans must have boolean type"

  let ifThenElse (cond: term) (thn: term) (els: term) (cx: cx) (tp: tp) =
    (* NB. We scrub cond's context b/c we are discrete wrt it. *)
    Imp.ifThenElse tp (cond (scrub cx) `Bool) (thn cx tp) (els cx tp)

  let guard (cond: term) (body: term) (cx: cx) (tp: tp) =
    Imp.guard (asLat tp) (cond cx `Bool) (body cx tp)

  let lam (x: sym) (body: term) (cx: cx): tp -> Imp.term = function
    | `Fn(a,b) -> Imp.lam a b x (body (Cx.add x (Id,a) cx) b)
    | _ -> typeError "lambda must have function type"

  let tuple (terms: term list) (cx: cx): tp -> Imp.term = function
    | `Tuple tps ->
       if List.(length terms <> length tps)
       then typeError "tuple has wrong length"
       else Imp.tuple (List.map2 (fun tp term -> tp, term cx tp) tps terms)
    | _ -> typeError "tuples must have tuple type"

  let letTuple (xs: sym list) (expr: expr) (body: term) (cx: cx) (tp: tp): Imp.term =
    match expr cx with
    | `Tuple tps, exprX ->
       if List.(length tps <> length xs)
       then typeError "tuple has wrong length"
       else
         let tpxs = List.combine tps xs in
         let bindings = List.map (fun (tp,x) -> x,(Id,tp)) tpxs in
         Imp.letTuple tpxs tp exprX (body (Cx.add_list bindings cx) tp)
    | _ -> typeError "destructuring non-tuple"

  let set (terms: term list) (cx: cx): tp -> Imp.term = function
    | `Set eltp -> terms
                   |> List.map (fun term -> term cx (eltp :> tp))
                   |> Imp.set eltp
    | _ -> typeError "set must have set type"

  let union (terms: term list) (cx: cx) (tp: tp): Imp.term =
    terms
    |> List.map (fun term -> term cx tp)
    |> Imp.union (asLat tp)

  let forIn (x: sym) (set: expr) (body: term) (cx: cx) (tp: tp): Imp.term =
    let eltype, setX = match set cx with
      | `Set eltype, setX -> eltype, setX
      | _ -> typeError "cannot comprehend over non-set" in
    Imp.forIn eltype (asLat tp) x setX
      (body (Cx.add x (Box, (eltype :> tp)) cx) tp)

  let box (term: term) (cx: cx): tp -> Imp.term = function
    | `Box a -> Imp.box a (term (scrub cx) a)
    | _ -> typeError "box must have box type"

  let letBox (x: sym) (expr: expr) (body: term) (cx: cx) (tp: tp): Imp.term =
    match expr cx with
    | `Box a, exprX -> Imp.letBox a tp x exprX (body (Cx.add x (Box,a) cx) tp)
    | _ -> typeError "cannot unbox non-box type"

  let fix (x: sym) (body: term) (cx: cx) (tp: tp): Imp.term =
    (* Needs to be a semilattice type and also first order.
     * We're not doing termination checking for now. *)
    match firstOrder tp with
    | None -> typeError "fixed point at higher-order type"
    | Some eqtp ->
      (* We scrub the context then add a monotone variable; de facto,
       * fix: □(A → A) → A *)
      body (scrub cx |> Cx.add x (Id, tp)) tp
      |> Imp.lam tp tp x
      |> Imp.box (`Fn (tp, tp))
      |> Imp.fix (asLat eqtp)

  (* inferring exprs *)
  let asc (tp: tp) (term: term) (cx: cx): tp * Imp.term = tp, term cx tp

  let var (x: sym) (cx: cx): tp * Imp.term =
    match Cx.find x cx with
    | Box, tp -> tp, Imp.discvar tp x
    | Id, tp -> tp, Imp.var tp x
    | Hidden, _ -> typeError (Printf.sprintf "variable %s is hidden" (Sym.to_string x))

  let app (fnc: expr) (arg: term) (cx: cx): tp * Imp.term =
    match fnc cx with
    | `Fn(a,b), fncX -> b, Imp.app a b fncX (arg cx a)
    | _ -> typeError "applying non-function"

  let proj (i: int) (expr: expr) (cx: cx): tp * Imp.term =
    match expr cx with
    | `Tuple tps, exprX -> List.nth tps i, Imp.proj tps i exprX
    | _ -> typeError "projection from non-tuple"

  let equals (m: expr) (n: expr) (cx: cx): tp * Imp.term =
    let tp, mX = m (scrub cx) in
    match firstOrder tp with
    | None -> typeError "comparing at non-equality type"
    | Some eqtp -> `Bool, Imp.equals eqtp mX (expr n (scrub cx) tp)
end


(* Dummy transform to compare against Seminaive. *)
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
  let string = Imp.string
  let bool = Imp.bool
  let ifThenElse a = Imp.ifThenElse (debox a)
  let guard a = Imp.guard (deboxLat a)
  let set a = Imp.set a
  let union a = Imp.union (deboxLat a)
  let forIn a b = Imp.forIn a (deboxLat b)
  let fix = Imp.fix
  let equals = Imp.equals
  let box a m = m
  let letBox a b = Imp.letIn (debox a) (debox b)
end


(* The speedup φ and derivative δ transformations. *)
module Seminaive(Imp: SIMPLE): MODAL
       with type term = Imp.term * Imp.term
= struct
  type tp = modaltp
  type term = Imp.term * Imp.term (* φM, δM *)

  (* This may only be used at base types. It almost ignores its argument;
   * however, at sum types, it does depend on the tag. If sum types are not
   * involved, `zero` produces a constant expression. In particular, at
   * first-order semilattice types, it produces a bottom expression, which the
   * simplifier will recognize. This aids optimization. *)
  let rec zero (tp: eqtp) (term: Imp.term): Imp.term = match tp with
    | `Bool -> Imp.bool false
    | `String -> Imp.tuple []
    | `Set a -> Imp.set a []
    | `Tuple tps ->
       let dtps = List.map delta (tps :> modaltp list) in
       List.mapi (fun i a -> List.nth dtps i, zero a (Imp.proj dtps i term)) tps
       |> Imp.tuple

  (* φx = x                 δx = dx *)
  let var (a: tp) (x: sym) = Imp.var (phi a) x, Imp.var (delta a) (Sym.d x)

  (* If the variable is discrete, we know its derivative is a zero change; so if
   * it's first-order, we can inline zero applied to it. *)
  let discvar (a: tp) (x: sym) =
    match firstOrder a with
    | None -> var a x
    | Some eqa -> let phix = Imp.var (phi a) x in
                  phix, zero eqa phix

  (* φ(box M) = φM, δM      δ(box M) = δM *)
  let box (a: tp) (fTerm, dTerm: term): term =
    let fa, da = phiDelta a in
    Imp.tuple [fa, fTerm; da, dTerm], dTerm

  (* φ(let box x = M in N) = let x,dx = φM in φN
   * δ(let box x = M in N) = let x,dx = φM in δN *)
  let letBox (a: tp) (b: tp) (x: sym) (fExpr, dExpr: term) (fBody, dBody: term): term =
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
    let f (a,x) = let (fa,da) = phiDelta a in (fa,x),(da,x) in
    let ftpxs, dtpxs = List.(map f tpxs |> split) in
    Imp.letTuple ftpxs fBodyTp fTuple fBody,
    Imp.letTuple ftpxs dBodyTp fTuple (Imp.letTuple dtpxs dBodyTp dTuple dBody)

  (* φ(s: string) = s   δ(s: string) = () *)
  let string (s: string): term = Imp.string s, Imp.tuple []

  (* φ(b: bool) = b     δ(b: bool) = false *)
  let bool (b: bool): term = Imp.bool b, Imp.bool false

  (* φ(if M then N else O) = if φM then φN else φO
   * δ(if M then N else O) = if φM then δN else δO  -- condition can't change! *)
  let ifThenElse (a: tp) (fCond,dCond: term) (fThn,dThn: term) (fEls,dEls: term): term =
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
    Imp.set a (List.map fst elts), Imp.set a []

  (* φ(M ∨ N) = φM ∨ φN     δ(M ∨ N) = δM ∨ δN *)
  let union (a: tp semilat) (terms: term list) =
    Imp.union (phiLat a) (List.map fst terms),
    Imp.union (deltaLat a) (List.map snd terms)

  let forIn (a: eqtp) (b: tp semilat) (x: sym) (fExpr, dExpr: term) (fBody, dBody: term) =
    let fb = phiEqLat b in
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
      [ Imp.forIn a fb x dExpr fBody
      ; Imp.forIn a fb x (Imp.union (`Set a) [fExpr;dExpr]) dBody ]

  (* φ(fix M) = semifix φM
   * δ(fix M) = zero ⊥ = ⊥ *)
  let fix (a: eqtp semilat) (fFunc, dFunc: term) =
    Imp.semifix a fFunc, Imp.union (a :> Imp.tp semilat) []

  (* φ(M == N) = φM == φN       δ(M == N) = false *)
  let equals (a: eqtp) (fM, dM: term) (fN, dN: term): term =
    Imp.equals a fM fN, Imp.bool false
end


(* Optimization/simplification. This is ugly and hackish, but works. *)
(* module IsEmpty: SIMPLE with type term = rawtp semilat cx -> rawtp semilat option
 * = struct
 *   type tp = rawtp
 *   type isEmpty = rawtp semilat
 *   type term = isEmpty cx -> isEmpty option
 *   let var a x = (??)
 *   let letIn a b x m n = (??)
 *   let lam a b x m = (??)
 *   let app a b m n = (??)
 *   let tuple tpterms = (??)
 *   let proj tps i m = (??)
 *   let letTuple tpxs b m n = (??)
 *   let string x = (??)
 *   let bool x = (??)
 *   let ifThenElse a cnd thn els = (??)
 *   let guard a cnd body = (??)
 *   let set eltp elems = (??)
 *   let union a terms = (??)
 *   let forIn a b x m n = (??)
 *   let fix a m = (??)
 *   let equals a m n = (??)
 *   let semifix a m = (??)
 * end
 *
 * module Fuzz(Imp: SIMPLE) = struct
 *   type tp = rawtp
 *   type isEmpty = rawtp semilat
 *   type value = isEmpty option * Imp.term
 *   type term = isEmpty cx -> value
 *   let wat (isEmpty: IsEmpty.term) (imp: Imp.term): term =
 *     fun cx -> match isEmpty cx with
 *               | None -> None, imp
 *               | Some a -> Some a, Imp.union a []
 *   let var a x = wat (IsEmpty.var a x) (Imp.var a x)
 *   let app (a:tp) (b:tp) (m:term) (n:term) (cx:isEmpty cx): value =
 *     let mE,mX = m cx and nE,nX = n cx in
 *     wat (IsEmpty.app a b mE nE) (Imp.app a b mX nX) cx
 * end *)

module Simplify(Imp: SIMPLE): sig
  include SIMPLE
          with type term = rawtp semilat cx -> Imp.term * rawtp semilat option
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
    | termX, Some `Tuple lats -> empty (List.nth lats i)
    | termX, _ -> full (Imp.proj tps i termX)

  let letTuple tpxs bodyTp expr body cx =
    let exprX, exprE = expr cx in
    let knowns = match exprE with
      | Some `Tuple lats -> List.map2 (fun (_,x) lat -> x,lat) tpxs lats
      | _ -> [] in
    let bodyX, bodyE = body (Cx.add_list knowns cx) in
    propagate (Imp.letTuple tpxs bodyTp exprX bodyX) bodyE

  let string s cx = Imp.string s, None
  let bool x cx = Imp.bool x, if x then None else Some `Bool

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
    let f tm = match tm cx with tmX, Some _ -> [] | tmX, None -> [tmX] in
    match List.(concat (map f terms)) with
    | [] -> empty a | elems -> full (Imp.union a elems)

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
end


(* Compiling to Haskell. *)
module ToHaskell: SIMPLE with type term = StringBuilder.t = struct
  open StringBuilder
  type tp = rawtp
  type term = StringBuilder.t

  let sym x = string (Sym.to_uid x)
  let paren t = string "(" ^ t ^ string ")"
  let parenSpaces xs = paren (concat (string " ") xs)
  let commas = concat (string ", ")
  let listOf terms = string "[" ^ commas terms ^ string "]"
  let call name args = parenSpaces (string name :: args)
  let letBind pat expr body =
    parenSpaces [string "let"; pat; string "="; expr; string "in"; body]

  let var tp x = sym x
  let letIn a b x expr body = letBind (sym x) expr body
  let equals a m n = parenSpaces [m; string "=="; n]
  let lam a b x body = paren (string "\\" ^ sym x ^ string " -> " ^ body)
  let app a b fnc arg = parenSpaces [fnc; arg]

  let bool b = string (if b then "True" else "False")
  let ifThenElse tp cond thn els =
    parenSpaces [string "if"; cond; string "then"; thn; string "else"; els]
  let guard tp cond body = call "guard" [cond; body]

  let tuple = function
    | [] -> string "()"
    | [_,term] -> term (* singleton tuples turn into the contained type *)
    | terms -> paren (commas List.(map snd terms))
  let letTuple tpxs bodyTp tuple body =
    letBind (List.map (fun (tp,x) -> sym x) tpxs |> commas |> paren) tuple body
  let proj tps i term = match List.length tps, i with
    | x, y when y >= x -> impossible "out of bounds projection"
    | 1, 0 -> term     (* singleton tuples turn into the contained type *)
    | 2, 0 -> call "fst" [term]
    | 2, 1 -> call "snd" [term]
    | _, _ -> todo "projection from ternary or larger tuples unimplemented"

  (* NB. You'd think we could just generate "empty" here and let Haskell's
   * typeclasses do the work for us, but if Haskell can't infer the type of
   * such an expression it gets mad. So we make it explicit. *)
  let rec empty: tp semilat -> term = function
    | `Bool -> string "False"
    | `Set _ -> string "Set.empty"
    | `Tuple tps -> tuple (List.map (fun tp -> tp, empty tp) tps)
    | `Fn(a,b) -> lam a b (Sym.gen "_") (empty b)

  let set a terms = call "set" [listOf terms]
  let union tp = function
    | [] -> empty tp
    | [tm] -> tm
    | [tm1; tm2] -> call "union" [tm1; tm2]
    | terms -> call "unions" [listOf terms]

  let forIn a b x set body = call "forIn" [set; lam a b x body]
  let fix tp term = call "fix" [term]
  let semifix tp term = call "semifix" [term]

  (* This has to come at the end because we use string to mean
     StringBuilder.string earlier. *)
  let string s = StringBuilder.string (Printf.sprintf "%S" s)
end


(* Putting it all together. *)
module Examples(Modal: MODAL) = struct
  module Lang = Typecheck(Modal)
  open Lang

  let x = Sym.gen "x" let y = Sym.gen "y"
  let a = Sym.gen "a" let b = Sym.gen "b"
  let x1 = Sym.gen "x1" let x2 = Sym.gen "x2"
  let y1 = Sym.gen "y1" let y2 = Sym.gen "y2"
  let path = Sym.gen "path"
  let edge = Sym.gen "edge"

  type test = Modal.term
  let testIn (tp: tp) cx (ex: term): Modal.term =
    ex (cx |> List.map (fun (a,b,c) -> a,(b,c)) |> Cx.from_list) tp
  let test (tp: tp) (ex: term) = ex Cx.empty tp

  let shouldFail f = try ignore (f ()); impossible "shouldn't typecheck"
                     with TypeError _ -> ()
  let _ = shouldFail (fun _ -> testIn `Bool [x,Hidden,`Bool] (expr (var x)))

  (* TODO: more tests. *)
  let t0 = testIn `Bool [x,Id,`Bool] (expr (var x))
  let t1 = testIn `Bool [x,Box,`Bool] (expr (var x))
  (* t2 = λx.x *)
  let t2 = test (`Fn(`Bool,`Bool)) (lam x (expr (var x)))
  let t3 = testIn `Bool
             [x,Id,`Fn(`Bool,`Bool); y,Id,`Bool]
             (expr (app (var x) (expr (var y))))

  let t4 = test (`Box (`Fn(`Bool, `Bool)))
             (box (lam x (expr (var x))))

  let term5 = letBox x
                (asc (`Box (`Fn(`Bool, `Bool)))
                   (box (lam x (expr (var x)))))
                (expr (app (var x) (expr (var y))))
  let t5 = testIn `Bool [y,Id,`Bool] term5

  let t6 = test (`Tuple []) (fix x (expr (var x)))

  (* Relation composition *)
  let strel: tp = `Set (`Tuple [`String; `String])
  let t7 = testIn strel [a,Id,strel;b,Id,strel]
             (forIn x (var a)
                (forIn y (var b)
                   (guard (expr (equals (proj 1 (var x)) (proj 0 (var y))))
                      (set [tuple [expr (proj 0 (var x));
                                   expr (proj 1 (var y))]]))))

  (* Intersection *)
  let strset: tp = `Set `String
  let t8 = testIn strset [a,Id,strset; b,Id,strset]
             (forIn x (var a)
                (forIn y (var b)
                   (guard (expr (equals (var x) (var y)))
                      (set [expr (var x)]))))

  (* Test for letBox at first-order type.
   * Should optimize derivative to False. *)
  let t9 = testIn `Bool [x,Id,`Box `Bool]
             (letBox y (var x) (expr (var y)))

  (* Transitive closure *)
  let t10 = testIn strel [edge, Box, strel]
          (fix path (union [expr (var edge);
                            forIn a (var edge)
                              (forIn b (var path)
                                 (guard (expr (equals (proj 1 (var a)) (proj 0 (var b))))
                                    (set [tuple [expr (proj 0 (var a));
                                                 expr (proj 1 (var b))]])))]))

  let tests = [t0;t1;t2;t3;t4;t5;t6;t7;t8;t9;t10]
end

module Simplified = Simplify(ToHaskell)
module Seminaived = Seminaive(Simplified)
module Debug = Examples(Seminaived)

let runTest (i: int) (x,y: Debug.test) =
  Printf.printf "%d: %s\n%d: %s\n"
    i (StringBuilder.finish (Simplified.finish x))
    i (StringBuilder.finish (Simplified.finish y))
let runTests () = List.iteri runTest Debug.tests

module Naive = Examples(DropBoxes(ToHaskell))

let runNaiveTest (i: int) (x: Naive.test) =
  Printf.printf "%d: %s\n" i (StringBuilder.finish x)
let runNaiveTests () = List.iteri runNaiveTest Naive.tests

(* 2019-07-01 Faster version of transitive closure:

semifix
(\path.
  edge ∪
  forIn (a in edge) for (b in path) when (snd a == fst b)
    {(fst a, snd b)}),
(\path dpath.
  for (a in edge) for (b in dpath) when (snd a == fst b)
    {(fst a, snd b)})

Which is what we wanted!
*)
