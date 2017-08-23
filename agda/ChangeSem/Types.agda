{-# OPTIONS --postfix-projections #-}
module ChangeSem.Types where

open import Cat
open import ChangeCat
open import Changes
open import Datafun
open import Decidability
open import Monads
open import Prelude
open import Prosets
open import TreeSet

 ---------- Denotations of types & tones ----------
Vars : Cx -> Set
Vars X = ∃ (λ a -> X a)
pattern Var {o} {a} p = (o , a) , p

type : Type -> Change
type bool = change-bool
type (set a p) = change-tree (change□ (type a))
type (□ a) = change□ (type a)
type (a ⊃ b) = type a ⇨ type b
type (a * b) = type a ∧ type b
type (a + b) = type a ∨ type b

⟦_⟧₁ : Tone × Type -> Change
⟦ mono , a ⟧₁ = type a
⟦ disc , a ⟧₁ = change□ (type a)

⟦_⟧ : Cx -> Change
⟦_⟧+ : Premise -> Change
⟦ X ⟧ = changeΠ (Vars X) (λ v -> ⟦ proj₁ v ⟧₁)
⟦ nil ⟧+    = ⊤-change
⟦ P , Q ⟧+  = ⟦ P ⟧+ ∧ ⟦ Q ⟧+
⟦ □ P ⟧+    = change□ ⟦ P ⟧+
⟦ X ▷ P ⟧+  = ⟦ X ⟧ ⇨ ⟦ P ⟧+
⟦ term a ⟧+ = type a

 -- What does it mean for a type's denotation to be a semilattice?
record Semilat (A : Change) : Set where
  field vee : A ∧ A ≤ A
  field eps : ⊤-change ≤ A
  -- Do I need a proof that _∨_ actually is a semilattice on (𝑶 A)?

open Semilat public

 ---------- Semantics of type-classes ----------
class : Class -> Change -> Set
class (c , d) A = class c A × class d A
-- If I were to add equality testing as an expression, I'd need that equality
-- has a derivative, which shouldn't be hard to prove.
class DEC A  = Decidable (Hom (𝑶 A))
class SL  A  = Semilat A
class FIN A  = TODO
class ACC A  = TODO
class ACC≤ A = TODO

is! : ∀{C a} -> Is C a -> class C (type a)
is! {c , d} (x , y) = is! x , is! y

is! {DEC} bool = bool≤?
is! {DEC} (set a p) = tree≤? _ (isos≤? (type a .𝑶) (is! p))
is! {DEC} (□ a p) = isos≤? (type a .𝑶) (is! p)
is! {DEC} (a * b) = decidable× (is! a) (is! b)
is! {DEC} (a + b) = decidable+ (is! a) (is! b)

-- Can't I give a general proof that any semilattice operator is monotone?
-- wait, isn't ∨-functor exactly that, for Sums?
--
-- also, can't I give a general proof that its derivative is itself?!
-- yes, I think I can!
is! {SL} bool .vee .func = Sums.∨-functor bool-sums
is! {SL} bool .vee .deriv = {!!}
is! {SL} bool .vee .is-id = {!!}
is! {SL} bool .eps = {!!}

is! {SL} (set a) = {!!}
is! {SL} (a * b) = {!!}
is! {SL} (a ⊃ b) = {!!}

is! {FIN} a = TODO
is! {ACC} a = TODO
is! {ACC≤} a = TODO

