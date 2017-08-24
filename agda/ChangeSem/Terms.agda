{-# OPTIONS --postfix-projections #-}
module ChangeSem.Terms where

open import Cat
open import ChangeCat
open import ChangeSem.Types
open import Changes
open import Datafun
open import Monads
open import Prelude
open import Prosets
open import TreeSet

 -- Lemmas for semantics of terms

-- TODO: implement SetΠ Change instead and use that.
change-comapΠ : ∀{A B} (C : B → Change) (f : A → B) -> changeΠ B C ≤ changeΠ A (λ x → C (f x))
change-comapΠ _ F .funct = prefixΠ _ F
change-comapΠ _ F .deriv = π₂ • prefixΠ _ F
change-comapΠ _ F .is-id df-ok = df-ok ∘ F

-- ⟦_⟧ is a functor, Cx^op -> Change
comap⟦_⟧ : ∀{X Y} -> X ⊆ Y -> ⟦ Y ⟧ ≤ ⟦ X ⟧
comap⟦ f ⟧ = change-comapΠ ⟦_⟧v (∃-map f)

foo : ∀{A B} (a : A) -> changeΠ A B ≤ B a
foo = {!!}

-- Managing environments.
lookup : ∀{X x} -> X x -> ⟦ X ⟧ ≤ ⟦ x ⟧₁
lookup p = {!!}
-- lookup p .funct = fun (λ f → f (, p))
-- lookup p .deriv = fun (π₂ • (λ f → f (, p)))
-- -- lookup p .deriv .ap = (λ { (γ , dγ) → dγ (, p) })
-- -- lookup p .deriv .map (f≈g , df≤dg) = df≤dg (Var p)
-- lookup p .is-id df-ok = df-ok (, p)
