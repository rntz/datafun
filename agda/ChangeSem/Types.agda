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

 ---------- Semantics of type-classes ----------
-- TODO
