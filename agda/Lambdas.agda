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
  -- should these be prefix operators so that they chain without parens?
  πl : ∀{Γ a b : Obj C} -> Γ ≤ a ∧ b -> Γ ≤ a; πl f = f ∙ π₁
  πr : ∀{Γ a b : Obj C} -> Γ ≤ a ∧ b -> Γ ≤ b; πr f = f ∙ π₂

module _ {i j} {{C : Cat i j}} where
  module _ {{cc : CC C}} where
    -- Is this the right infixity for _$_?
    -- It must be < 9 to bind less tightly than ∙.
    infixr 1 _$_

    fn : ∀{Γ a b : Obj C} -> Γ ∧ a ≤ b -> Γ ≤ a ⇨ b
    fn = curry

    fnₗ : ∀{Γ a b : Obj C} → a ∧ Γ ≤ b → Γ ≤ a ⇨ b
    fnₗ = curryₗ

    -- Cat.call is great when we want to _compute_ the internal-morphism we
    -- call, but if it's static we have use 'constant. Need another notation. In
    -- fact, we just want prefix composition. Feel a bit bad about using _$_ for
    -- this, though. Would prefer ∘, but I also use dependent function
    -- composition.
    _$_ : ∀{Γ a b : Obj C} -> a ≤ b -> Γ ≤ a -> Γ ≤ b
    f $ x = x ∙ f

  module _ {{sums : Sums C}} where
    inl : ∀{Γ a b : Obj C} -> Γ ≤ a -> Γ ≤ a ∨ b; inl x = x ∙ in₁
    inr : ∀{Γ a b : Obj C} -> Γ ≤ b -> Γ ≤ a ∨ b; inr x = x ∙ in₂

    module _ {{cc : CC C}} where
      casesₗ : ∀{Γ a b c : Obj C} → a ∧ Γ ≤ c → b ∧ Γ ≤ c → (a ∨ b) ∧ Γ ≤ c
      casesₗ f g = distrib-∧/∨ₗ ∙ [ f , g ]

      casesᵣ : ∀{Γ a b c : Obj C} → Γ ∧ a ≤ c → Γ ∧ b ≤ c → Γ ∧ (a ∨ b) ≤ c
      casesᵣ f g = distrib-∧/∨ᵣ ∙ [ f , g ]

      -- Often, we want to get *rid* of some piece of the Γ that was used to prove
      -- (a ∨ b), and only use the remainder Γ' in proving (Γ' ∧ a ≤ c) and (Γ' ∧
      -- b ≤ c). Can we capture this idiom nicely?
      cases : ∀{Γ a b c : Obj C} -> Γ ≤ a ∨ b -> Γ ∧ a ≤ c -> Γ ∧ b ≤ c -> Γ ≤ c
      cases M N₁ N₂ = ⟨ M , id ⟩ ∙ casesₗ (swap ∙ N₁) (swap ∙ N₂)

      -- case/drop : ∀{Γ Δ a b c : Obj C} → Γ ≤ a ∨ b → Γ ≤ Δ → Δ ∧ a ≤ c → Δ ∧ b ≤ c → Γ ≤ c
      -- case/drop M Γ→Δ

      cases⇨ : ∀{Γ a b c : Obj C} -> Γ ≤ a ∨ b -> Γ ≤ a ⇨ c -> Γ ≤ b ⇨ c -> Γ ≤ c
      cases⇨ M N₁ N₂ = cases M (uncurry N₁) (uncurry N₂)
