(* A quick note about preorders; skip this if you know about them.
 *
 * A preorder is a relation (a ≤ b) satisfying two rules:
 * 1. Reflexivity: a ≤ a.
 * 2. Transitivity: if a ≤ b and b ≤ c then a ≤ c.
 *
 * A good example of a preorder is "lists under containment":
 * let (a ≤ b) if every element of the list a is also in b.
 *
 * Preorders are like partial orders, but without requiring antisymmetry.
 * For example, [0,1] ≤ [1,0] under "containment", but [0,1] ≠ [1,0].
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
 *      Op ** Op  = Op
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
let meet (a: tone) (b: tone): tone = match a, b with
  | Iso, _ | _, Iso | Id, Op | Op, Id -> Iso
  | x, Path | Path, x -> x
  | Id, Id | Op, Op -> a


(* ========== TYPES ========== *)
(* Here is a simple fragment of Modal Datafun's type system.
 *
 * You can think of it as a type system for a simply typed lambda calculus,
 * but one where types are interpreted as /preorders/, not sets; and where
 * all functions are monotone.
 *)
type tp
  = Base                        (* some arbitrary type *)
  | Fn of tp * tp               (* functions *)
  | Tuple of tp list            (* tuples *)
  | Box of tp                   (* internalizes Iso / the discrete ordering *)
  | Opp of tp                   (* internalizes Op / the opposite ordering *)

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
 *
 * And that's what I /hope/ this code does. I have sketches of the cases for a
 * proof that, if (s = subtype a b), then (A^s <: B). I also have, for many of
 * my subtyping rules, counterexamples that show that their conclusions can't be
 * safely strengthened. However, that's as far as I've gotten, proof-wise.
 *)
exception Incompatible of tp * tp
let rec subtype (a: tp) (b: tp): tone =
  let fail () = raise (Incompatible (a,b)) in
  match a,b with
  | Base, Base -> Id           (* base type not assumed to be discrete *)

  (* I believe the order of these two Box rules doesn't matter.
   * But I haven't proven this. *)
  | x, Box y -> subtype x y ** Iso
  | Box x, y -> Path ** subtype x y

  | Opp x, y | x, Opp y -> Op ** subtype x y (* NB. Op ** s = s ** Op *)

  | Tuple xs, Tuple ys ->
     (try List.(map2 subtype xs ys |> fold_left meet Path)
      with Invalid_argument _ -> fail())

  | Fn(a1,b1), Fn(a2,b2) ->
     (* TODO: failure messages should mention the tones as the issue. *)
     let s,t = subtype a2 a1, subtype b1 b2 in
     begin match t, s with
     | Iso, Path | Id, (Id|Path) | Op, (Op|Path) | Path, (Id|Op|Path) -> t
     | Iso, _    | Id, _         | Op, _         | Path, _            -> fail()
     end

  (* Incongruous cases. *)
  | (Base|Tuple _|Fn _), (Base|Tuple _|Fn _) -> fail()
