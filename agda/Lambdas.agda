-- Concise, infix, lambda-calculus-ish notation for arrows in cartesian closed
-- categories.
--
-- Hypothesis: if we mirror the rules of natural deduction / STLC, we'll get a
-- fairly nice syntax for - except for variables, which will become ugly
-- compositions of π₁ and π₂.

module Lambdas where

open import Prelude
open import Cat

module _ {i j} {{C : Cat i j}} {{P : Products C}} where
  πl : ∀{Γ a b : Obj C} -> Γ ≤ a ∧ b -> Γ ≤ a; πl f = f • π₁
  πr : ∀{Γ a b : Obj C} -> Γ ≤ a ∧ b -> Γ ≤ b; πr f = f • π₂

module _ {i j} {{C : Cat i j}} where
  module _ {{cc : CC C}} where
    fn : ∀{Γ a b : Obj C} -> (Γ ∧ a) ≤ b -> Γ ≤ (a ⇨ b)
    fn = curry

    -- TODO: find the right infixity
    _$_ : ∀{Γ a b : Obj C} -> Γ ≤ a ⇨ b -> Γ ≤ a -> Γ ≤ b
    _$_ = call

  module _ {{sums : Sums C}} where
    inl : ∀{Γ a b : Obj C} -> Γ ≤ a -> Γ ≤ a ∨ b; inl x = x • in₁
    inr : ∀{Γ a b : Obj C} -> Γ ≤ b -> Γ ≤ a ∨ b; inr x = x • in₂

    module _ {{cc : CC C}} where
      -- Often, we want to get *rid* of some piece of the Γ that was used to prove
      -- (a ∨ b), and only use the remainder Γ' in proving (Γ' ∧ a ≤ c) and (Γ' ∧
      -- b ≤ c). Can we capture this idiom nicely?
      cases : ∀{Γ a b c : Obj C} -> Γ ≤ a ∨ b -> Γ ∧ a ≤ c -> Γ ∧ b ≤ c -> Γ ≤ c
      cases M N₁ N₂ = ⟨ M , id ⟩ • distrib-∧/∨ • [ swap • N₁ , swap • N₂ ]

      cases⇨ : ∀{Γ a b c : Obj C} -> Γ ≤ a ∨ b -> Γ ≤ a ⇨ c -> Γ ≤ b ⇨ c -> Γ ≤ c
      cases⇨ M N₁ N₂ = cases M (uncurry N₁) (uncurry N₂)
