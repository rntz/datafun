-- Concise, infix, lambda-calculus-ish notation for arrows in cartesian closed
-- categories.
module Lambdas where

open import Prelude
open import Cat

module _ {i j} {{C : Cat i j}} {{cc : CC C}} where
  fn : ∀{Γ a b : Obj C} -> (Γ ∧ a) ≤ b -> Γ ≤ (a ⇨ b)
  fn = curry

  _!_ : ∀{Γ a b : Obj C} -> Γ ≤ a ⇨ b -> Γ ≤ a -> Γ ≤ b
  _!_ = call

  module _ {{sums : Sums C}} where
    case : ∀{Γ a b c : Obj C} -> Γ ≤ a ∨ b -> Γ ≤ a ⇨ c -> Γ ≤ b ⇨ c -> Γ ≤ c
    case M N₁ N₂ = ⟨ M , id ⟩ • distrib-∧/∨ • {!!}
