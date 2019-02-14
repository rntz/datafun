(*
===== TODO =====

- Moar tests.
- A simplification/optimizer pass.

POST DEADLINE:
- a parser
- sum types

===== OPTIMIZATION =====

What optimizations will I need? I will need at least:

- Eliminating/propagating bottoms (esp. empty sets and false).

It's probably easy and useful to also:

- Eliminating "if"s & "when"s whose conditions are constant, or at least,
  constantly false.

Is that all? Consider optimizing the derivatives of the following:

- relation intersection
- relation composition (see icfp19/examples.org)
- transitive closure

===== NEW DESIGN as of January 2019 =====

All tagless-final. Compiler flowchart:

    BIDIR: Bidirectional Datafun
      |
      | typecheck
      V
    MODAL: Explicit modal Datafun
      |              |
      | φ/δ          | forget □
      V              V
    SIMPLE: Non-monotone λ-calculus with fix & fast-fix
      |
      | normalize
      V
    NORMAL: Normal non-monotone λ-calculus with fix & fast-fix
      |
      | compile to Haskell
      V
    Haskell code

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
      | Some x::xs -> loop (x::acc) xs
      | None::_ -> None
      | [] -> Some (List.rev acc)
    in loop [] l
  let is_some = function Some _ -> true | None -> false
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

(* Frontend, modal types. *)
type modaltp = [ `Bool | `String | `Set of modaltp | `Box of modaltp
               | `Tuple of modaltp list | `Fn of modaltp * modaltp ]
(* Backend, non-modal types. *)
type rawtp = [ `Bool | `String | `Set of rawtp
             | `Tuple of rawtp list | `Fn of rawtp * rawtp ]
(* Semilattices, parameterized by underlying types *)
type 'a semilat = [ `Bool | `Set of 'a | `Tuple of 'a semilat list | `Fn of 'a * 'a semilat ]

let rec firstOrder: modaltp -> bool = function
  | `Fn _ -> false
  | `Bool | `String -> true
  | `Box a | `Set a -> firstOrder a
  | `Tuple tps -> List.for_all firstOrder tps

let rec phiDelta: modaltp -> rawtp * rawtp = function
  | `Bool -> `Bool, `Bool
  | `String -> `String, `Tuple [] (* strings don't change *)
  | `Set a -> let fa = phi a in `Set fa, `Set fa
  | `Box a -> let fa, da = phiDelta a in `Tuple [fa;da], da
  | `Tuple tps -> let ftps, dtps = List.(map phiDelta tps |> split) in
                  `Tuple ftps, `Tuple dtps
  | `Fn (a,b) -> let fa,da = phiDelta a and fb,db = phiDelta b in
                 `Fn (fa, fb), `Fn (fa, `Fn (da, db))
and phi a = fst (phiDelta a)
and delta a = snd (phiDelta a)

(* phiDelta of a semilattice type produces a semilattice type; Obj.magic convinces
 * OCaml that this is so. *)
let phiDeltaLat: modaltp semilat -> rawtp semilat * rawtp semilat = Obj.magic phiDelta
let phiLat: modaltp semilat -> rawtp semilat = Obj.magic phi
let deltaLat: modaltp semilat -> rawtp semilat = Obj.magic delta


(* M,N ::= x | λx.M | M N
 *       | (M0,M1,...,Mn) | πᵢ M | let (x0,...,xn) = M in N
 *       | true | false | if M then N else O | when (M) N
 *       | ⊥ | M ∨ N | {M} | for (x in M) N
 *       | box M | let box x = M in N
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
  val set: tp -> term list -> term
  (* union A [M0;...;Mn] = M0 ∨ ... ∨ Mn : A *)
  val union: tp semilat -> term list -> term
  (* forIn A B x M N = for (x : A in M) do N : B *)
  val forIn: tp -> tp semilat -> sym -> term -> term -> term
  val fix: tp semilat -> term -> term
  val equals: tp -> term -> term -> term
end

module type MODAL = sig
  include BASE with type tp = modaltp
  val box: tp -> term -> term
  val letBox: tp -> tp -> sym -> term -> term -> term
end

module type SIMPLE = sig
  include BASE with type tp = rawtp
  val fastfix: tp semilat -> term -> term
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

  let rec asLat: tp -> tp semilat = function
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
                   |> List.map (fun term -> term cx eltp)
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
      (body (Cx.add x (Box,eltype) cx) tp)

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
    if not (firstOrder tp)
    then typeError "fixed point at higher-order type" else
      (* We scrub the context then add a monotone variable; de facto,
       * fix: □(A → A) → A *)
      body (scrub cx |> Cx.add x (Id,tp)) tp
      |> Imp.lam tp tp x
      |> Imp.box (`Fn (tp, tp))
      |> Imp.fix (asLat tp)

  (* inferring exprs *)
  let asc (tp: tp) (term: term) (cx: cx): tp * Imp.term = tp, term cx tp

  let var (x: sym) (cx: cx): tp * Imp.term =
    match Cx.find x cx with
    | (Box | Id), tp -> tp, Imp.var tp x
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
    `Bool, Imp.equals tp mX (expr n (scrub cx) tp)
end


(* Implementation of the go-faster transformation. *)
module Seminaive(Imp: SIMPLE): MODAL
       with type term = Imp.term * Imp.term
= struct
  type tp = modaltp
  type term = Imp.term * Imp.term (* φM, δM *)

  (* This should only ever be used at base types. It almost ignores its
   * argument; however, at sum types, it does depend on the tag. *)
  let rec zero (tp: tp) (term: Imp.term): Imp.term = match tp with
    | `Box a -> zero a term
    | `Bool -> Imp.bool false
    | `String -> Imp.tuple []
    | `Set a -> Imp.set (phi a) []
    | `Tuple tps ->
       let dtps = List.map delta tps in
       List.mapi (fun i a -> delta a, zero a (Imp.proj dtps i term)) tps
       |> Imp.tuple
    (* This case _should_ be dead code. *)
    | `Fn (a,b) -> impossible "cannot compute zero change at function type"

  (* Most semilattice operations (except fix) are implementable at higher-order
   * types. However, their φ/δ translations are different. For first-order
   * semilattice types A, φA = ΔA and ⊕ = ∨. At higher-order types, this is not
   * true, and the correct approach is to eta-expand until it is true. However,
   * I don't expect to be using semilattice operations at functional types in
   * any example programs, so to simplify the implementation I error on higher-
   * order semilattice types.
   * 
   * For more info, See seminaive/seminaive.pdf and seminaive/semantics.pdf.
   *)
  let phiFirstOrderLat (a: tp semilat) =
    let fA, dA = phiDeltaLat a in
    if not (firstOrder (a :> modaltp))
    then todo "semilattice operations only implemented for first-order data"
    else if not (fA = dA) then impossible "this shouldn't happen"
    else fA

  (* φx = x                 δx = dx *)
  let var (a: tp) (x: sym) = Imp.var (phi a) x, Imp.var (delta a) (Sym.d x)

  (* φ(box M) = φM, δM      δ(box M) = δM *)
  let box (a: tp) (fTerm, dTerm: term): term =
    let fa, da = phiDelta a in
    Imp.tuple [fa, fTerm; da, dTerm], dTerm

  (* TODO: this is a potential optimization point. we can examine the type `b`
   * and if it's first-order and contains no sums - for example, if it's a set type -
   * we know statically what the zero value will be and we can substitute it in
   * instead of unboxing it.
   *
   * so instead of:     φ(let [x] = M in N) = let [x,dx] = φM in φN
   * it becomes:        φ(let [x] = M in N) = let [x,_] = φM in let dx = 0_A in φN
   *)
  (* φ(let box x = M in N) = let x,dx = φM in φN
   * δ(let box x = M in N) = let x,dx = φM in δN *)
  let letBox (a: tp) (b: tp) (x: sym) (fExpr, dExpr: term) (fBody, dBody: term): term =
    let fa,da = phiDelta a and fb,db = phiDelta b and dx = Sym.d x in
    (* let (x,dx) = φM in ... *)
    let binder bodyTp body = Imp.letTuple [fa,x;da,dx] bodyTp fExpr body in
    binder fb fBody, binder db dBody

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

  (* φ(when (M) N) = when (φM) φN
   * δ(when (M) N) = if φM then δN else when (δM) φN ∨ δN
   *
   * The latter assumes φA = ΔA and ⊕ = ∨. (See phiFirstOrderLat.) *)
  let guard (a: tp semilat) (fCond,dCond: term) (fBody,dBody: term): term =
    let fA = phiFirstOrderLat a in
    Imp.guard fA fCond fBody,
    Imp.ifThenElse (fA :> rawtp) fCond dBody
      (Imp.guard fA dCond (Imp.union fA [fBody; dBody]))

  (* φ({M}) = {φM}          δ({M}) = ∅ *)
  let set (a: tp) (elts: term list) =
    Imp.set (phi a) (List.map fst elts), Imp.set (phi a) []

  (* φ(M ∨ N) = φM ∨ φN     δ(M ∨ N) = δM ∨ δN *)
  let union (a: tp semilat) (terms: term list) =
    Imp.union (phiLat a) (List.map fst terms),
    Imp.union (deltaLat a) (List.map snd terms)

  let forIn (a: tp) (b: tp semilat) (x: sym) (fExpr, dExpr: term) (fBody, dBody: term) =
    let fa,da = phiDelta a and fb = phiFirstOrderLat b in
    (* φ(for (x in M) N) = for (x in φM) let dx = 0 x in φN *)
    Imp.forIn fa fb x fExpr
      (Imp.letIn da (fb :> rawtp) (Sym.d x) (zero a (Imp.var fa x)) fBody),
    (* Assuming φB = ΔB and ⊕ = ∨ (see phiFirstOrderLat),
     *
     * δ(for (x in φM) φN)
     * =  (for (x in δM) let dx = 0 x in φN)
     *   ∨ for (x in φM ∪ δM) let dx = 0 x in δN *)
    let loopBody body =
      Imp.letIn da (fb :> rawtp) (Sym.d x) (zero a (Imp.var fa x)) body in
    Imp.union fb
      (* for (x in δM) let dx = 0 x in φN *)
      [ Imp.forIn fa fb x dExpr (loopBody fBody)
      (* for (x in M ∪ δM) let dx = 0 x in δN *)
      ; Imp.forIn fa fb x (Imp.union (`Set fa) [fExpr;dExpr]) (loopBody dBody) ]

  (* φ(fix M) = fastfix φM
   * δ(fix M) = zero ⊥ = ⊥ *)
  let fix (a: tp semilat) (fFunc, dFunc: term) =
    let fa = phiFirstOrderLat a in
    Imp.fastfix fa fFunc, Imp.union fa []

  (* φ(M == N) = φM == φN       δ(M == N) = false *)
  let equals (a: tp) (fM, dM: term) (fN, dN: term): term =
    Imp.equals (phi a) fM fN, Imp.bool false
end


(* Optimization/simplification.
 * Isn't this basically a product of the identity translation
 * and a simpler (isEmpty option) interpretation?
 *)
module Simplify(Imp: SIMPLE): sig
  include SIMPLE
  val finish: term -> Imp.term
end = struct
  type tp = rawtp
  type isEmpty = tp semilat
  type term = isEmpty cx -> Imp.term * isEmpty option

  let empty a = Imp.union a [], Some a

  let finish (term: term): Imp.term = match term Cx.empty with
    | _, Some tp -> Imp.union tp []
    | term, None -> term

  let var a x cx = Imp.var a x, Cx.find_opt x cx
  let letIn a b x expr body cx =
    let eTerm, eEmpty = expr cx in
    let bTerm, bEmpty = body (Cx.add_opt x eEmpty cx) in
    Imp.letIn a b x eTerm bTerm, bEmpty

  let lam a b x body cx =
    let bTerm, bEmpty = body cx in
    Imp.lam a b x bTerm, Option.map (fun b -> `Fn(a,b)) bEmpty

  let app a b (fnc: term) arg cx =
    let fncX, fncE = fnc cx and argX, argE = arg cx in
    Imp.app a b fncX argX, match fncE with Some `Fn(_,y) -> Some y | _ -> None

  let tuple tpterms cx =
    let f (a,m) = let mX,mE = m cx in (a,mX), mE in
    let tptms, empties = List.(map f tpterms |> split) in
    Imp.tuple tptms, Option.(all empties |> map (fun x -> `Tuple x))

  let proj tps i term cx =
    let termX, termE = term cx in
    Imp.proj tps i termX,
    match termE with Some `Tuple lats -> Some (List.nth lats i) | _ -> None

  let letTuple tpxs bodyTp expr body cx =
    let exprX, exprE = expr cx in
    let knowns = match exprE with
      | Some `Tuple lats -> List.map2 (fun (_,x) lat -> x,lat) tpxs lats
      | _ -> [] in
    let bodyX, bodyE = body (Cx.add_list knowns cx) in
    Imp.letTuple tpxs bodyTp exprX bodyX, bodyE

  let string s cx = Imp.string s, None
  let bool x cx = Imp.bool x, if x then None else Some `Bool

  let ifThenElse a cnd thn els cx =
    match cnd cx, thn cx, els cx with
    (* If condition is false, give back els. *)
    | (_, Some _), _, els -> els
    (* If both branches are always empty, return empty. *)
    | _, (_, Some lat), (_, Some _) -> empty lat
    (* Otherwise, default. *)
    | (cndX, _), (thnX,_), (elsX,_) -> Imp.ifThenElse a cndX thnX elsX, None

  let guard a cnd body cx =
    match cnd cx, body cx with
    | (_, Some _), _ -> empty a
    | (cndX,_), (bodyX, bodyE) -> Imp.guard a cndX bodyX, bodyE

  let set a terms cx = match List.map (fun tm -> fst (tm cx)) terms with
    | [] -> empty (`Set a)
    | terms -> Imp.set a terms, None
  let union a terms cx =
    let f tm = match tm cx with tmX, Some _ -> [] | tmX, None -> [tmX] in
    match List.(concat (map f terms)) with
    | [] -> empty a | elems -> Imp.union a elems, None
  let forIn a b x set body cx =
    match set cx, body cx with
    | (setX, None), (bodyX, None) -> Imp.forIn a b x setX bodyX, None
    | _ -> empty b
  let fix a fnc cx = match fnc cx with
    | _, Some _ -> empty a | fncX, None -> Imp.fix a fncX, None
  let fastfix a fncderiv cx = match fncderiv cx with
    | _, Some _ -> empty a | fdX, None -> Imp.fastfix a fdX, None
  let equals a tm1 tm2 cx = Imp.equals a (fst (tm1 cx)) (fst (tm2 cx)), None
end

module IsEmpty: SIMPLE with type term = rawtp semilat cx -> rawtp semilat option
= struct
  type tp = rawtp
  type isEmpty = rawtp semilat
  type term = isEmpty cx -> isEmpty option
  let var a = Cx.find_opt
  let letIn a b x expr body cx = body (Cx.add_opt x (expr cx) cx)
  let lam a b x body cx = Option.map (fun b -> `Fn(a,b)) (body cx)
  let app a b fnc arg cx = match fnc cx with Some `Fn(_,y) -> Some y | _ -> None
  let tuple (tpterms: (tp * term) list) cx =
    let empties = List.(map (fun (a,m) -> m cx) tpterms) in
    Option.(all empties |> map (fun x -> `Tuple x))
  let proj tps i term cx =
    match term cx with Some `Tuple lats -> Some (List.nth lats i) | _ -> None
  let letTuple tpxs bodyTp (expr: term) (body: term) cx =
    let knowns = match expr cx with
      | Some `Tuple lats -> List.map2 (fun (_,x) lat -> x,lat) tpxs lats
      | _ -> [] in
    body (Cx.add_list knowns cx)
  let string s cx = None
  let bool x cx = if x then None else Some `Bool
  let ifThenElse a (cnd: term) (thn: term) (els: term) cx =
    match cnd cx, thn cx, els cx with
    | Some _, _, els -> els           (* cnd is false -> return els *)
    | _, Some lat, Some _ -> Some lat (* both branches empty *)
    | _ -> None
  let guard a cnd body cx = match cnd cx, body cx with
    | Some _, _ -> Some a | _, bodyE -> bodyE
  let set a terms cx = match List.map (fun tm -> tm cx) terms with
    | [] -> Some (`Set a) | terms -> None
  let union a (terms: term list) cx =
    if List.for_all (fun tm -> Option.is_some (tm cx)) terms
    then Some a else None
  let forIn a b x set body cx = match set cx, body cx with
    | None, None -> None | _ -> Some b
  let fix a fnc cx = Option.map (fun _ -> a) (fnc cx)
  let fastfix a (fncderiv: term) cx = Option.map (fun _ -> a) (fncderiv cx)
  let equals a tm1 tm2 cx = None
end


(* (\* A simple and stupid debug printer.
 *  * Has precedence all wrong. *\)
 * module ToString: SIMPLE with type term = string = struct
 *   type tp = rawtp
 *   type term = string
 *
 *   let sym = Sym.to_string
 *   let commas = String.concat ", "
 *
 *   let var tp x = sym x
 *   let letIn a b x expr body = "let " ^ sym x ^ " = " ^ expr ^ " in " ^ body
 *   let lam a b x body = "fn " ^ sym x ^ " => " ^ body
 *   let app a b fnc arg = "(" ^ fnc ^ " " ^ arg ^ ")"
 *   let tuple = function
 *     | [_,term] -> "(" ^ term ^ ",)"
 *     | tpterms -> "(" ^ commas (List.map snd tpterms) ^ ")"
 *   let letTuple _ = todo "ToString.letTuple"
 *   let proj tps i term = "π" ^ string_of_int i ^ " " ^ term
 *   let set a terms = "{" ^ commas terms ^ "}"
 *   let union tp = function
 *     | [] -> "empty"
 *     | [term] -> "(or " ^ term ^ ")"
 *     | terms -> "(" ^ String.concat " or " terms ^ ")"
 *   let forIn a b x set body =
 *     "for (" ^ sym x ^ " in " ^ set ^ ") " ^ body
 *   let fix tp term = "fix " ^ term
 *   let fastfix tp term = "fastfix " ^ term
 * end *)


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
  let lambda x body = paren (string "\\" ^ sym x ^ string " -> " ^ body)
  let letBind pat expr body =
    parenSpaces [string "let"; pat; string "="; expr; string "in"; body]

  let var tp x = sym x
  let letIn a b x expr body = letBind (sym x) expr body
  let equals a m n = parenSpaces [m; string "=="; n]
  let lam a b x body = lambda x body
  let app a b fnc arg = parenSpaces [fnc; arg]

  let bool b = string (if b then "True" else "False")
  let ifThenElse tp cond thn els =
    parenSpaces [string "if"; cond; string "then"; thn; string "else"; els]
  let guard tp cond body = call "guard" [cond; body]

  let tuple = function
    | [] -> string "()"
    (* singleton tuples turn into the contained type *)
    | [_,term] -> term
    | [_,tm1;_,tm2] -> paren (commas [tm1;tm2])
    | _ -> todo "ternary or larger tuples unimplemented"
  let proj tps i term = match List.length tps, i with
    | x, y when y >= x -> impossible "out of bounds projection"
    | 1, 0 -> term
    | 2, 0 -> call "fst" [term]
    | 2, 1 -> call "snd" [term]
    | _, _ -> todo "ternary or larger tuples unimplemented"
  let letTuple tpxs bodyTp tuple body =
    letBind (List.map (fun (tp,x) -> sym x) tpxs |> commas |> paren) tuple body

  let set a terms = call "set" [listOf terms]
  let union tp = function
    | [] -> string "empty"
    | [tm] -> tm
    | [tm1; tm2] -> call "union" [tm1; tm2]
    | terms -> call "unions" [listOf terms]

  let forIn a b x set body = call "forIn" [set; lambda x body]
  let fix tp term = call "fix" [term]
  let fastfix tp term = call "fastfix" [term]

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

  let testIn cx (tp: tp) (ex: term) =
    ex (cx |> List.map (fun (a,b,c) -> a,(b,c)) |> Cx.from_list) tp
  let test (tp: tp) (ex: term) = ex Cx.empty tp

  let shouldFail f = try ignore (f ()); impossible "shouldn't typecheck"
                     with TypeError _ -> ()

  (* TODO: more tests. *)
  let t0 = testIn [x,Id,`Bool] `Bool (expr (var x))
  let t1 = testIn [x,Box,`Bool] `Bool (expr (var x))
  (* t2 = λx.x *)
  let t2 = test (`Fn(`Bool,`Bool)) (lam x (expr (var x)))
  let t3 = testIn
             [x,Id,`Fn(`Bool,`Bool); y,Id,`Bool]
             `Bool
             (expr (app (var x) (expr (var y))))

  let t4 = test (`Box (`Fn(`Bool, `Bool)))
             (box (lam x (expr (var x))))

  let term5 = letBox x
                (asc (`Box (`Fn(`Bool, `Bool)))
                   (box (lam x (expr (var x)))))
                (expr (app (var x) (expr (var y))))
  let t5 = testIn [y,Id,`Bool] `Bool term5

  let t6 = test (`Tuple []) (fix x (expr (var x)))

  (* Relation composition *)
  let strel: tp = `Set (`Tuple [`String; `String])
  let t7 = testIn [a,Box,strel;b,Box,strel] strel
         (forIn x (var a)
            (forIn y (var b)
               (guard (expr (equals (proj 1 (var x)) (proj 0 (var y))))
                  (set [tuple [expr (proj 0 (var x));
                               expr (proj 1 (var y))]]))))

  let _ = shouldFail (fun _ -> testIn [x,Hidden,`Bool] `Bool (expr (var x)))

  let tests = [t0;t1;t2;t3;t4;t5;t6;t7]
end

module Debug = Examples(Seminaive(ToHaskell))
let f0, d0 = Debug.t0
let f1, d1 = Debug.t1
let f2, d2 = Debug.t2
let f3, d3 = Debug.t3
let f4, d4 = Debug.t4
let f5, d5 = Debug.t5
let f6, d6 = Debug.t6

let runTest i (x,y) =
  Printf.printf "%d: %s\n%d: %s\n"
    i (StringBuilder.finish x)
    i (StringBuilder.finish y)
let runTests () = List.iteri runTest Debug.tests

(* Results of t7, tidied up:

7: (forIn a_2 (\x_0 ->
     let dx_0 = ((), ()) in
     forIn b_3 (\y_1 ->
      let dy_1 = ((), ()) in
      guard (snd x_0 == fst y_1)
        (set [((fst x_0), (snd y_1))]))))
7: union
    (forIn da_2 (\x_0 ->
      let dx_0 = ((), ()) in
      forIn b_3 (\y_1 ->
        let dy_1 = ((), ()) in
        guard (snd x_0 == fst y_1)
          (set [(fst x_0, snd y_1)]))))
    (forIn (union a_2 da_2) (\x_0 ->
      let dx_0 = ((), ()) in
      union
        (forIn db_3 (\y_1 ->
          let dy_1 = ((), ()) in
          guard (snd x_0 == fst y_1)
            (set [((fst x_0), (snd y_1))])))
        (forIn (union b_3 db_3) (\y_1 ->
          let dy_1 = ((), ()) in
          if (snd x_0 == fst y_1)
          then (set [])
          else (guard False (union (set [(fst x_0, snd y_1)]) (set [])))))))

*)
