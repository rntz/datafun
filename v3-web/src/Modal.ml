(* A quick note about preorders; skip this if you know about them.
 *
 * A preorder is a relation (a ≤ b) satisfying two rules:
 * 1. Reflexivity: a ≤ a.
 * 2. Transitivity: if a ≤ b and b ≤ c then a ≤ c.
 *
 * A good example of a preorder is "lists under containment":
 * let (X ≤ Y) if every element of the list X is also in Y.
 *
 * Preorders are like partial orders, but without requiring antisymmetry.
 * For example, under "containment" we have [0,1] ≤ [1,0] and [1,0] ≤ [0,1],
 * but [0,1] ≠ [1,0].
 *
 * If you're a category theorist, a preorder is a "thin" category, where between
 * any two objects there is at most one morphism. I believe much of the "tone
 * theory" in this file, ostensibly about maps between preorders, can be
 * extended to functors between categories.
 *)


(* ========== TONES ========== *)
(* Tones have two definitions:
 *
 * 1. Ways a function may respect the ordering on its argument.
 * 2. Transformations on the ordering of a preorder.
 *
 * Let's focus on the first definition for now.
 *)
type tone
  = Id    (* monotone/covariant; respects the ordering *)
  | Op    (* antitone/contravariant; respects the opposite order *)
  | Iso   (* invariant; respects only equivalence *)
  | Path  (* bivariant; respects both the order & its opposite *)

(* Consider an arbitrary preorder A. Let A^op be A, ordered oppositely.
 * Now, observe that
 *
 *               (f : A -> B) is antitone
 *
 *                    if and only if
 *
 *              (f : A^op -> B) is monotone
 *
 * So "antitone" is a special case of "monotone"!
 *
 * This observation generalizes; every tone is really monotonicity with a
 * transformation applied to the domain's ordering. Tones transform orderings.
 *)

(* We formalize this as follows, letting A^s be "A transformed by the tone s":
 *
 *          (f : A -> B) respects its arguments with tone s
 *
 *                          if and only if
 *
 *          (f : A^s -> B) is a monotone map from A^s to B
 *
 * Of course, we still need to define A^s:
 * 
 * 1. Id leaves the order unchanged.
 *
 * 2. Op inverts it: (a ≤ b at A^op) iff (b ≤ a at A).
 *
 * 3. Iso gives the induced equivalence:
 *    (a ≡ b at A^iso) iff (a ≤ b and b ≤ a at A).
 *
 * 4. Path gives the equivalence closure, the smallest equivalence such that
 *    (a ≤ b at A) implies (a ≡ b at A^path).
 *)


(* ---------- TONE COMPOSITION ---------- *)
(* Tone composition, (s ** t), corresponds to two things:
 *
 * 1. Composing functions with the given tones.
 *    Given f : A^s -> B and g : B^t -> C, their composition
 *    (f then g), in general, has tone (s ** t).
 *
 * 2. Composing the preorder transformations, postfix:
 *    A^(s ** t) = (A^s)^t.
 *)
let ( ** ) (a: tone) (b: tone): tone = match a,b with
  | x, Id | Id, x -> x
  | Op, Op -> Id
  | Iso, _ | Path, _ -> a   (* hi priority, must come first *)
  | _, Iso | _, Path -> b   (* lo priority, comes later *)

(* Tone composition is associative, with Id as identity. Further laws:
 *
 *      Op ** Op  = Id
 *      Path ** s = Path
 *      Iso  ** s = Iso
 *
 * Tone composition is NOT commutative. For example,
 * Path = Path ** Iso ≠ Iso ** Path = Iso.
 *)


(* ---------- THE TONE LATTICE ---------- *)
(* Tones themselves have a natural ordering: let (s ≤ t) iff
 * (∀A. A^s is a subpreorder of A^t). This looks like:
 *
 *    Path              greatest
 *    / \
 *  Id   Op
 *    \ /
 *    Iso               least
 *
 *)
let subtone (a: tone) (b: tone): bool = match a,b with
  | Iso, _ | _, Path | Id, Id | Op, Op -> true
  | _, Iso | Path, _ | Op, Id | Id, Op -> false

(* "meet" means "greatest lower bound"; we'll need this for subtyping. *)
let meet2 (a: tone) (b: tone): tone = match a, b with
  | Iso, _ | _, Iso | Id, Op | Op, Id -> Iso
  | x, Path | Path, x -> x
  | Id, Id | Op, Op -> a

let meet: tone list -> tone = List.fold_left meet2 Path


(* ========== TYPES ========== *)
(* Here is a simple fragment of Modal Datafun's type system.
 *
 * You can think of it as a type system for a simply typed lambda calculus,
 * but one where types are interpreted as /preorders/, not sets; and where
 * all functions are monotone.
 *)
type tag = string
type tp =
  [ `Base                       (* some arbitrary type *)
  | `Fn of tp * tp              (* functions *)
  | `Tuple of tp list           (* tuples *)
  | `Sum of (tag * tp) list     (* sums *)
  | `Set of tp                  (* finite sets *)
  | `Box of tp                  (* internalizes Iso / the discrete ordering *)
  | `Op of tp ]                 (* internalizes Op / the opposite ordering *)

(* Internalizing Id is trivial; it's the identity function on types.
 * Internalizing Path is... nontrivial.
 * If you know what Path's intro/elim/subtyping rules should be, email me.
 *)

(* ---------- SUBTYPING ---------- *)

(* Write (A <: B) for "A is a subpreorder of B", by which I mean:
 * 1. A is a subset of B
 * 2. (x <= y at A) implies (x <= y at B).
 *
 * Since our types represent preorders, we'd like our subtyping relation to
 * match this. However, for type inference purposes, it's convenient if we solve
 * a more general problem, namely:
 *
 *     Given types A, B, what is the greatest tone s such that A^s <: B?
 *     Or does no such tone exist?
 *
 * And that's what I /hope/ this code does. I have sketched cases of a proof
 * that, if (s = subtype A B), then (A^s <: B). I also have, for many of my
 * subtyping rules, counterexamples that show that their conclusions can't be
 * safely strengthened. However, that's as far as I've gotten, proof-wise.
 *)
exception Incompatible of tp * tp
let rec subtype (a: tp) (b: tp): tone =
  let fail () = raise (Incompatible (a,b)) in
  match a,b with
  (* I believe the order of these two Box rules doesn't matter.
   * But I haven't proven this. *)
  | x, `Box y -> subtype x y ** Iso
  | `Box x, y -> Path ** subtype x y

  | `Op x, y | x, `Op y -> Op ** subtype x y (* NB. Op ** s = s ** Op *)

  (* If we assumed Base was discrete, we could return Path here. *)
  | `Base, `Base -> Id

  (* (Set a <: Set b) iff (a is a subset of b); that's why we can safely ignore
   * the result of (subtype a b) here. *)
  | `Set a, `Set b -> ignore (subtype a b); Id

  | `Tuple xs, `Tuple ys ->
     meet (try List.map2 subtype xs ys
           with Invalid_argument _ -> fail())

  | `Sum tps1, `Sum tps2 ->
     let f (tag, tp1) = try subtype tp1 (List.assoc tag tps2)
                        with Not_found -> fail() in
     meet (List.map f tps1)

  | `Fn(a1,b1), `Fn(a2,b2) ->
     let t = subtype b1 b2 in
     begin match t, subtype a2 a1 with
     | Iso, Path | Id, (Id|Path) | Op, (Op|Path) | Path, (Id|Op|Path) -> t
     (* TODO: failure messages should mention the tones as the issue. *)
     | Iso, _    | Id, _         | Op, _         | Path, _            -> fail()
     end

  (* Incongruous cases. *)
  | (`Base|`Tuple _|`Sum _|`Fn _|`Set _),
    (`Base|`Tuple _|`Sum _|`Fn _|`Set _) -> fail()


(* ========== TERMS, TYPE CHECKING, and TONE INFERENCE ========== *)
module Cx = Map.Make(String)
type var = string
type 'a cx = 'a Cx.t

(* Our typechecker is written for clarity rather than for good error messages;
 * it can throw many exceptions when it fails, not just TypeError. *)
exception TypeError of string
let error msg = raise (TypeError msg)

(* Checking forms. *)
type ('check, 'synth) checkF =
  [ `Fn of var * 'check
  | `Tuple of 'check list | `Tag of tag * 'check | `Set of 'check list
  | `Box of 'check | `Op of 'check
  (* Large eliminations.
   * TODO: case-elimination for sums. *)
  (* `For (x, M, N) means: union for (x in M) of N *)
  | `Case of 'synth * (tag * var * 'check) list
  | `For of var * 'synth * 'check ]

(* Synthesis forms. *)
type ('check, 'synth) synthF
  = [ `Check of tp * 'check
    | `Var of var
    (* Small eliminations. *)
    | `App of 'synth * 'check | `Proj of 'synth * int
    | `Unbox of 'synth | `Unop of 'synth ]

type tm = [ (tm, synthTm) synthF | (tm, synthTm) checkF ]
and synthTm = (tm, synthTm) synthF

let (&): tone cx -> tone cx -> tone cx = Cx.union (fun _ s t -> Some (s ** t))
let cxMeet: tone cx list -> tone cx = List.fold_left (&) Cx.empty
let useAt (tone: tone): tone cx -> tone cx = Cx.map (fun s -> s ** tone)

let rec check (cx: tp cx) (tp: tp) (tm: tm): tone cx = match tp, tm with
  | want, (#synthF as tm) ->
     let (got, tones) = synth cx tm in
     useAt (subtype got want) tones

  | `Fn(a,b), `Fn(x,body) ->
     let tones = check (Cx.add x a cx) b body in
     begin match Cx.find_opt x tones with
     | Some s when not (subtone s Id) -> error "non-monotone function"
     | _ -> Cx.remove x tones
     end

  | `Tuple tps, `Tuple tms -> List.map2 (check cx) tps tms |> cxMeet
  | `Sum tagtps, `Tag (n, tm) -> check cx (List.assoc n tagtps) tm
  | `Set tp, `Set tms -> List.map (check cx tp) tms |> cxMeet |> useAt Iso
  | `Box tp, `Box tm -> check cx tp tm |> useAt Iso
  | `Op tp, `Op tm -> check cx tp tm |> useAt Op

  | `Set _, `For (x, setTm, bodyTm) ->
     let (elemtp, tones1) = match synth cx setTm with
       | `Set tp, tones -> tp, tones
       | _ -> error "looping over non-set" in
     tones1 & Cx.remove x (check (Cx.add x elemtp cx) tp bodyTm)

  | _tp, `Case (_subj, _arms) -> Util.todo()

  (* Incongruous cases. *)
  | _, (`Fn _|`Tuple _|`Tag _|`Set _|`Box _|`Op _|`For _) ->
     error "cannot give that type to that term"

and synth (cx: tp cx) (tm: synthTm): tp * tone cx = match tm with
  | `Check (tp, tm) -> (tp, check cx tp tm)
  | `Var x -> (Cx.find x cx, Cx.singleton x Id)
  | `App (func, arg) ->
     begin match synth cx func with
     | `Fn(a,b), tones1 -> (b, tones1 & check cx a arg)
     | _ -> error "expected a function"
     end

  | `Proj (tm, i) ->
     begin match synth cx tm with
     | `Tuple tps, tones -> List.nth tps i, tones
     | _ -> error "projecting from a non-tuple"
     end

  | `Unbox tm ->
     begin match synth cx tm with
     | `Box tp, tones -> tp, useAt Path tones
     | _ -> error "unboxing a non-box"
     end

  | `Unop tm ->
     begin match synth cx tm with
     | `Op tp, tones -> tp, useAt Op tones
     | _ -> error "unopping a non-op"
     end


(* TODO: Type checker tests! *)
       

(* ========== EVALUATION ========== *)
module rec Values: Set.S with type elt = Value.t = Set.Make(Value)
and Value: sig
  type t = Base of int | Set of Values.t | Tuple of t list
         | Tag of tag * t | Fn of (t -> t)
  val compare: t -> t -> int
end = struct
  type t = Base of int
         | Set of Values.t
         | Tuple of t list
         | Tag of tag * t
         | Fn of (t -> t)

  let rec compare x y = match x,y with
    | Base x, Base y -> Pervasives.compare x y
    | Set x, Set y -> Values.compare x y
    | Tuple [], Tuple [] -> 0
    | Tuple (x::xs), Tuple (y::ys) ->
       let c = compare x y in
       if c <> 0 then c else compare (Tuple xs) (Tuple ys)
    | Tag(n,x), Tag(m,y) ->
       let c = Pervasives.compare n m in
       if c <> 0 then c else compare x y
    | (Base _|Set _|Tuple _|Tag _|Fn _), _ -> failwith "runtime type error"
end

open Value
type value = Value.t
type env = value Cx.t

let deFn = function Fn f -> f | _ -> failwith "runtime type error"
let deSet = function Set s -> s | _ -> failwith "runtime type error"
let deTuple = function Tuple xs -> xs | _ -> failwith "runtime type error"

let rec eval (env: env): tm -> value = function
  | `Var v -> Cx.find v env
  (* introductions *)
  | `Fn(v,body) -> Fn (fun arg -> eval (Cx.add v arg env) body)
  | `Tuple xs -> Tuple (List.map (eval env) xs)
  | `Tag(n,x) -> Tag (n, eval env x)
  | `Set xs -> Set (Values.of_list (List.map (eval env) xs))
  (* eliminations *)
  | `Proj(x,i) -> List.nth (deTuple (evalS env x)) i
  | `App(func, arg) -> deFn (evalS env func) (eval env arg)
  | `For(v, set, body) ->
     let elems = deSet (evalS env set) in
     let union elem = Values.union (deSet (eval (Cx.add v elem env) body)) in
     Set (Values.fold union elems Values.empty)
  | `Case(_subj, _arms) -> Util.todo()
  (* type erasure *)
  | `Check (_, x) -> eval env x
  (* modal erasure *)
  | `Box x | `Op x -> eval env x
  | `Unbox x | `Unop x -> eval env (x :> tm)

and evalS (env: env) (tm: synthTm): value = eval env (tm :> tm)


(* TODO: evaluator tests *)
