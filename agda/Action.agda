module Action where

open import Level using (_⊔_)
open import Function using (_∘_)

record Action {i j} (A : Set i) (B : Set j) : Set (i ⊔ j) where
  field action : A → B → B

open Action public
open Action {{...}} public renaming (action to _·_)

instance
  pointwise-action : ∀{i j a b} → Action {i}{j} a b
                   → ∀{k} {Γ : Set k} → Action a (Γ → b)
  pointwise-action M .action a f = action M a ∘ f
