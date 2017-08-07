-- Denotational semantics for types in core Datafun.
module TypeSem where

open import Prelude
open import Cat
open import Prosets
open import Datafun
open import Monads
open import TreeSet

 ---------- Denotations of types & tones ----------
Vars : Cx -> Set
Vars X = ∃ (λ a -> X a)
pattern Var {o} {a} p = (o , a) , p

type : Type -> Proset
type bool = bools
type (set a p) = trees (isos (type a))
type (□ a) = isos (type a)
type (a ⊃ b) = type a ⇨ type b
type (a * b) = type a ∧ type b
type (a + b) = type a ∨ type b

⟦_⟧₁ : Tone × Type -> Proset
⟦ mono , a ⟧₁ = type a
⟦ disc , a ⟧₁ = isos (type a)

⟦_⟧ : Cx -> Proset
⟦_⟧+ : Premise -> Proset
⟦ X ⟧ = catΠ (Vars X) (λ v -> ⟦ proj₁ v ⟧₁)
⟦ nil ⟧+    = ⊤-proset
⟦ P , Q ⟧+  = cat× ⟦ P ⟧+ ⟦ Q ⟧+
⟦ □ P ⟧+    = isos ⟦ P ⟧+
⟦ X ▷ P ⟧+  = ⟦ X ⟧ ⇨ ⟦ P ⟧+
⟦ term a ⟧+ = type a

 ---------- Semantics of type-classes ----------
class : Class -> Proset -> Set
class DEC  A = Decidable (Hom A)
class SL   = Sums
class FIN  = TODO
class ACC  = TODO
class ACC≤ = TODO
class (C , D) P = class C P × class D P

is! : ∀{C a} -> Is C a -> class C (type a)
is! {DEC} bool = bool≤-decidable
-- argh!
is! {DEC} (set {a} p) = trees-decidable (isos (type a)) (isos-decidable (type a) (is! p))
-- argh.
is! {DEC} (□ {a} p) = isos-decidable (type a) (is! p)
is! {DEC} (a * b) = decidable× (is! a) (is! b)
is! {DEC} (a + b) = decidable+ (is! a) (is! b)

is! {SL} bool     = bool-sums
is! {SL} (set a)  = tree-sums (isos (type a))
is! {SL} (a * b)  = cat×-sums (is! a) (is! b)
is! {SL} (a ⊃ b)  = proset→-sums (is! b)

is! {FIN} a = TODO
is! {ACC} a = TODO
is! {ACC≤} a = TODO

is! {C , D} (x , y) = is! x , is! y

-- IsDecidable HasACC : Proset -> Set
-- IsDecidable A = {!!}
-- HasACC A = {!!}

-- is-dec : ∀{a} -> DEC a -> IsDecidable (type a)
-- is-dec = {!!}

-- is-acc : ∀{a} -> ACC a -> HasACC (type a)
-- is-acc = {!!}

-- IsSemilattice : Proset -> Set
-- IsSemilattice A = Sums A

-- is-sl : ∀ {a} -> Is SL a -> IsSemilattice (type a)
-- is-sl bool = bool-sums
-- is-sl (set a) = tree-sums (isos (type a))
-- is-sl (a * b) = cat×-sums (is-sl a) (is-sl b)
-- is-sl (a ⊃ b) = proset→-sums (is-sl b)
