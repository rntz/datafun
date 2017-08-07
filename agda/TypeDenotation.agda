-- Denotational semantics for types & such core Datafun.
module TypeDenotation where

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

 ---------- TODO: Semantics of type-classes ----------

-- IsDecidable HasACC : Proset -> Set
-- IsDecidable A = {!!}
-- HasACC A = {!!}

-- prove-dec : ∀{a} -> DEC a -> IsDecidable (type a)
-- prove-dec = {!!}

-- prove-acc : ∀{a} -> ACC a -> HasACC (type a)
-- prove-acc = {!!}

IsSemilattice : Proset -> Set
IsSemilattice A = Sums A

is-sl : ∀ {a} -> Is SL a -> IsSemilattice (type a)
is-sl bool = bool-sums
is-sl (set a) = tree-sums (isos (type a))
is-sl (a * b) = cat×-sums (is-sl a) (is-sl b)
is-sl (a ⊃ b) = proset→-sums (is-sl b)
