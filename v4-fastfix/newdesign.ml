(* TODO:
 * - equality tests
 * - boolean intro/elim forms (true, false, if, when)
 * - some base type to compute with; naturals or strings.
 * - ToHaskell compilation step
 *
 * POST DEADLINE:
 * - a parser
 * - sum types
 *)

(*

NEW DESIGN as of January 2019
=============================

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
      | eval/compile
      V
    Generate Haskell or OCaml code (?)

GRIPES
======

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


(* A module for building large strings efficiently.
 * I could probably use Buffer, but it has an imperative interface. *)
module type STRING_BUILDER = sig
  type t
  val finish: t -> string
  val string: string -> t
  val int: int -> t
  val (^): t -> t -> t
  val concat: t -> t list -> t
end

module StringBuilder: STRING_BUILDER = struct
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
   * x.id == y.id implies x.name == y.name, (although not x.degree == y.degree).
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
end
type 'a cx = 'a Cx.t

(* Frontend, modal types. *)
type modaltp = [ `Bool | `Set of modaltp | `Box of modaltp
               | `Tuple of modaltp list | `Fn of modaltp * modaltp ]
(* Backend, non-modal types. *)
type rawtp = [ `Bool | `Set of rawtp | `Tuple of rawtp list | `Fn of rawtp * rawtp ]
(* Semilattices, parameterized by underlying types *)
type 'a semilat = [ `Bool | `Set of 'a | `Tuple of 'a semilat list | `Fn of 'a * 'a semilat ]

let rec firstOrder: modaltp -> bool = function
  | `Fn _ -> false
  | `Bool | `Set _ -> true
  | `Box a -> firstOrder a
  | `Tuple tps -> List.for_all firstOrder tps

let rec phiDelta: modaltp -> rawtp * rawtp = function
  | `Bool -> `Bool, `Bool
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


(* M,N ::= x | λx.M | M N | (M0,M1,...,Mn) | πᵢ M
 *       | ⊥ | M ∨ N | {M} | for (x in M) N
 *       | box M | let box x = M in N
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
  (* set A [M0;...;Mn] = {M0,...,Mn} : {A} *)
  val set: tp -> term list -> term
  (* union A [M0;...;Mn] = M0 ∨ ... ∨ Mn : A *)
  val union: tp semilat -> term list -> term
  (* forIn A B x M N = for (x : A in M) do N : B *)
  val forIn: tp -> tp semilat -> sym -> term -> term -> term
  val fix: tp semilat -> term -> term
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

  (* checking terms *)
  val expr: expr -> term
  val letIn: sym -> expr -> term -> term
  val lam: sym -> term -> term
  val tuple: term list -> term
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
    | `Box _ -> typeError "not a semilattice type"

  (* inferring exprs *)
  let asc (tp: tp) (term: term) (cx: cx): tp * Imp.term = tp, term cx tp

  let var (x: sym) (cx: cx): tp * Imp.term =
    match Cx.find x cx with
    | (Box | Id), tp -> tp, Imp.var tp x
    | Hidden, _ -> typeError "that variable is hidden"

  let app (fnc: expr) (arg: term) (cx: cx): tp * Imp.term =
    match fnc cx with
    | `Fn(a,b), fncX -> b, Imp.app a b fncX (arg cx a)
    | _ -> typeError "applying non-function"

  let proj (i: int) (expr: expr) (cx: cx): tp * Imp.term =
    match expr cx with
    | `Tuple tps, exprX -> List.nth tps i, Imp.proj tps i exprX
    | _ -> typeError "projection from non-tuple"

  (* checking terms *)
  let expr (expr: expr) (cx: cx) (tp: tp): Imp.term =
    let exprType, exprX = expr cx in
    if subtype exprType tp then exprX
    else typeError "inferred type does not match annotation"

  let letIn (x: sym) (expr: expr) (body: term) (cx: cx) (tp: tp): Imp.term =
    let exprType, exprX = expr cx in
    Imp.letIn exprType tp x exprX (body (Cx.add x (Id,exprType) cx) tp)

  let lam (x: sym) (body: term) (cx: cx): tp -> Imp.term = function
    | `Fn(a,b) -> Imp.lam a b x (body (Cx.add x (Id,a) cx) b)
    | _ -> typeError "lambda must have function type"

  let tuple (terms: term list) (cx: cx): tp -> Imp.term = function
    | `Tuple tps ->
       if List.(length terms <> length tps)
       then typeError "tuple has wrong length"
       else Imp.tuple (List.map2 (fun tp term -> tp, term cx tp) tps terms)
    | _ -> typeError "tuples must have tuple type"

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
end


(* Implementation of the go-faster transformation. *)
module Seminaive(Raw: SIMPLE): MODAL
       with type term = Raw.term * Raw.term
= struct
  type tp = modaltp
  type term = Raw.term * Raw.term (* φM, δM *)

  (* This should only ever be used at base types. It almost ignores its
   * argument; however, at sum types, it does depend on the tag. *)
  let rec zero (tp: tp) (term: Raw.term): Raw.term = match tp with
    | `Box a -> zero a term
    | `Bool -> todo "no boolean literals yet"
    | `Set a -> Raw.set (phi a) []
    | `Tuple tps ->
       let dtps = List.map delta tps in
       List.mapi (fun i a -> delta a, zero a (Raw.proj dtps i term)) tps
       |> Raw.tuple
    (* This case _should_ be dead code. *)
    | `Fn (a,b) -> impossible "cannot compute zero change at function type"

  (* φx = x                 δx = dx *)
  let var (a: tp) (x: sym) = Raw.var (phi a) x, Raw.var (delta a) (Sym.d x)

  (* φ(box M) = φM, δM      δ(box M) = δM *)
  let box (a: tp) (fTerm, dTerm: term): term =
    let fa, da = phiDelta a in
    Raw.tuple [fa, fTerm; da, dTerm], dTerm

  (* φ(let box x = M in N) = let x,dx = φM in φN
   * δ(let box x = M in N) = let x,dx = φM in δN *)

  (* TODO: this is a potential optimization point. we can examine the type `b`
   * and if it's first-order and contains no sums - for example, if it's a set type -
   * we know statically what the zero value will be and we can substitute it in
   * instead of unboxing it.
   *
   * so instead of:     φ(let [x] = M in N) = let [x,dx] = φM in φN
   * it becomes:        φ(let [x] = M in N) = let [x,_] = φM in let dx = 0_A in φN
   *)
  let letBox (a: tp) (b: tp) (x: sym) (fExpr, dExpr: term) (fBody, dBody: term): term =
    let fa,da = phiDelta a and fb,db = phiDelta b and dx = Sym.d x in
    let y = Sym.gen x.name and ytps = [fa;da] in
    let ytp = `Tuple ytps in
    let yproj i = Raw.proj ytps i (Raw.var ytp y) in
    let binder body =
      (* let y = φM in let x = fst y in let dx = snd y in ... *)
      Raw.letIn ytp fb y fExpr
        (Raw.letIn fa fb x (yproj 0) (Raw.letIn da fb dx (yproj 1) body))
    in binder fBody, binder dBody

  (* φ(let x = M in N) = let x = φM in φN
   * δ(let x = M in N) = let x = φM in δN *)
  let letIn (a: tp) (b: tp) (x: sym) (fExpr, dExpr: term) (fBody, dBody: term): term =
    let fA = phi a and fB, dB = phiDelta b in
    Raw.letIn fA fB x fExpr fBody, Raw.letIn fA dB x fExpr dBody

  (* φ(λx.M) = λx.φM        δ(λx.M) = λx dx. δM *)
  let lam (a: tp) (b: tp) (x: sym) (fBody, dBody: term): term =
    let fA,dA = phiDelta a and fB,dB = phiDelta b in
    Raw.lam fA fB x fBody,
    Raw.lam fA (`Fn (dA, dB)) x (Raw.lam dA dB (Sym.d x) dBody)

  (* φ(M N) = φM φN         δ(M N) = δM φN δN *)
  let app (a: tp) (b: tp) (fFnc, dFnc: term) (fArg, dArg: term): term =
    let fA,dA = phiDelta a and fB,dB = phiDelta b in
    Raw.app fA fB fFnc fArg,
    Raw.app dA dB (Raw.app fA (`Fn (dA, dB)) dFnc fArg) dArg

  (* φ(M,N) = φM,φN         δ(M,N) = δM,δN *)
  let tuple (elts: (tp * term) list) =
    Raw.tuple (List.map (fun (a, (fE,_)) -> phi a, fE) elts),
    Raw.tuple (List.map (fun (a, (_,dE)) -> delta a, dE) elts)

  (* φ(πᵢ M) = πᵢ φM        δ(πᵢ M) = πᵢ δM *)
  let proj (tps: tp list) (i: int) (fTerm, dTerm: term) =
    let ftps, dtps = List.(map phiDelta tps |> split) in
    Raw.proj ftps i fTerm, Raw.proj dtps i dTerm

  (* φ({M}) = {φM}          δ({M}) = ∅ *)
  let set (a: tp) (elts: term list) =
    Raw.set (phi a) (List.map fst elts), Raw.set (phi a) []

  (* φ(M ∨ N) = φM ∨ φN     δ(M ∨ N) = δM ∨ δN *)
  let union (a: tp semilat) (terms: term list) =
    Raw.union (phiLat a) (List.map fst terms),
    Raw.union (deltaLat a) (List.map snd terms)

  let forIn (a: tp) (b: tp semilat) (x: sym) (fExpr, dExpr: term) (fBody, dBody: term) =
    let fa,da = phiDelta a and fb,db = phiDeltaLat b in
    (* φ(for (x in M) N) = for (x in φM) let dx = 0 x in φN *)
    Raw.forIn fa fb x fExpr
      (Raw.letIn da fb (Sym.d x) (zero a (Raw.var fa x)) fBody),
    (* δ(for (x in φM) φN)
     * =  (for (x in δM) let dx = 0 x in φN)
     *   ∨ for (x in φM ∪ δM) let dx = 0 x in δN
     *
     * However, this assumes ΦB = ΔB and that ⊕ = ∨. This is false for
     * functional types. In that case the correct strategy is to eta-expand.
     * However, I don't expect to be using forIn at functional types in any real
     * programs, so I just fail if the type isn't first-order. *)
    if not (firstOrder (b :> modaltp))
    then todo "forIn only implemented for first-order data"
    else if not (fb = db) then impossible "this shouldn't happen"
    else
      let loopBody body = Raw.letIn da fb (Sym.d x) (zero a (Raw.var fa x)) body in
      Raw.union fb
        (* for (x in δM) let dx = 0 x in φN *)
        [ Raw.forIn fa fb x dExpr (loopBody fBody)
        (* for (x in M ∪ δM) let dx = 0 x in δN *)
        ; Raw.forIn fa fb x (Raw.union (`Set fa) [fExpr;dExpr]) (loopBody dBody) ]

  (* φ(fix M) = fastfix φM
   * δ(fix M) = zero ⊥ = ⊥ *)
  let fix (a: tp semilat) (fFunc, dFunc: term) =
    let fa,da = phiDeltaLat a in
    Raw.fastfix fa fFunc,
    Raw.union da [] 
end


(* A simple and stupid debug printer.
 * Has precedence all wrong. *)
module ToString: SIMPLE with type term = string = struct
  type tp = rawtp
  type term = string

  let sym = Sym.to_string
  let commas = String.concat ", "

  let var tp x = sym x
  let letIn a b x expr body = "let " ^ sym x ^ " = " ^ expr ^ " in " ^ body
  let lam a b x body = "fn " ^ sym x ^ " => " ^ body
  let app a b fnc arg = "(" ^ fnc ^ " " ^ arg ^ ")"
  let tuple = function
    | [_,term] -> "(" ^ term ^ ",)"
    | tpterms -> "(" ^ commas (List.map snd tpterms) ^ ")"
  let proj tps i term = "π" ^ string_of_int i ^ " " ^ term
  let set a terms = "{" ^ commas terms ^ "}"
  let union tp = function
    | [] -> "empty"
    | [term] -> "(or " ^ term ^ ")"
    | terms -> "(" ^ String.concat " or " terms ^ ")"
  let forIn a b x set body =
    "for (" ^ sym x ^ " in " ^ set ^ ") " ^ body
  let fix tp term = "fix " ^ term
  let fastfix tp term = "fastfix " ^ term
end


(* Compiling to Haskell. *)
module ToHaskell: SIMPLE with type term = StringBuilder.t = struct
  open StringBuilder
  type tp = rawtp
  type term = StringBuilder.t

  let sym x = string (Sym.to_uid x)
  let paren t = string "(" ^ t ^ string ")"
  let spaces = concat (string " ")
  let commas = concat (string ", ")
  let listOf terms = string "[" ^ commas terms ^ string "]"
  let call name args = paren (spaces (string name :: args))
  let lambda x body = paren (string "\\" ^ sym x ^ string " -> " ^ body)

  let var tp x = sym x
  let letIn a b x expr body =
    paren (spaces [string "let"; sym x; string "="; expr; string "in"; body])
  let lam a b x body = lambda x body
  let app a b fnc arg = paren (spaces [fnc; arg])

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

  let set a terms = call "set" [listOf terms]
  let union tp = function
    | [] -> string "empty"
    | [tm] -> tm
    | [tm1; tm2] -> call "union" [tm1; tm2]
    | terms -> call "unions" [listOf terms]

  let forIn a b x set body = call "forIn" [set; lambda x body]
  let fix tp term = call "fix" [term]
  let fastfix tp term = call "fastfix" [term]
end


(* Putting it all together. *)
module Examples(Modal: MODAL) = struct
  module Lang = Typecheck(Modal)
  open Lang

  let x = Sym.gen "x"
  let y = Sym.gen "y"

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

  let _ = shouldFail (fun _ -> testIn [x,Hidden,`Bool] `Bool (expr (var x)))

  let tests = [t0;t1;t2;t3;t4;t5;t6]
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
