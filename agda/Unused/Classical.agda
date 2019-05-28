module Unused.Classical where

open import Prelude
open import Cat

import Data.Product

-- "triple negation elimination"
3¬e : ∀{i}{a : Set i} -> ¬ ¬ ¬ a -> ¬ a
3¬e ¬¬¬a a = ¬¬¬a λ ¬a → ¬a a

-- Double negation forms a monadic functor on Set.
¬¬ : ∀{i} -> sets {i} ≤ sets {i}
ap ¬¬ a = ¬ ¬ a
map ¬¬ f ¬¬a ¬b = ¬¬a (¬b ∘ f)

-- open import Monads
-- instance
--   ¬¬Monad : ∀{i} -> Monad (¬¬ {i})
--   Monad.join ¬¬Monad = 3¬e
--   Monad.pure ¬¬Monad a ¬a = ¬a a

 -- Classical connectives
infixr 1 _∨?_
_∨?_ : ∀{i j} -> Set i -> Set j -> Set _
a ∨? b = ¬ (¬ a × ¬ b)

infix 2 Σ?-syntax
Σ? Σ?-syntax : ∀{a b} (A : Set a) -> (A -> Set b) -> Set _
Σ? A B = ¬ ∀ (a : A) → ¬ B a
Σ?-syntax = Σ?

syntax Σ?-syntax A (λ x → B) = Σ?[ x ∈ A ] B

∃? : ∀{a b} {A : Set a} -> (A -> Set b) -> Set _
∃? = Σ? _

 -- Rules for classical connectives.
lem? : ∀{i}{a : Set i} -> a ∨? ¬ a
lem? (a , ¬a) = ¬a a

module _ {i j} {a : Set i} {b : Set j} where
  ∨?-i : ¬ ¬ (a ⊎ b) -> a ∨? b
  ∨?-i a∨?b (¬a , ¬b) = a∨?b λ { (inj₁ x) → ¬a x ; (inj₂ y) → ¬b y }

  ∨?-e : a ∨? b -> ¬ ¬ (a ⊎ b)
  ∨?-e f ¬a⊎b = f (¬a⊎b ∘ inj₁ , ¬a⊎b ∘ inj₂)

  make-∨? : a ⊎ b -> a ∨? b
  make-∨? (inj₁ x) (¬a , ¬b) = ¬a x
  make-∨? (inj₂ y) (¬a , ¬b) = ¬b y

  make-∨?₁ : a -> a ∨? b; make-∨?₁ = make-∨? ∘ inj₁
  make-∨?₂ : b -> a ∨? b; make-∨?₂ = make-∨? ∘ inj₂

module _ {i j} {A : Set i} {B : A -> Set j} where
  ¬∃→∀¬ : ¬ (Σ A B) → ∀ a -> ¬ B a;  ¬∃→∀¬ = Data.Product.curry
  ∀¬→¬∃ : (∀ a -> ¬ B a) -> ¬ Σ A B; ∀¬→¬∃ = Data.Product.uncurry

  -- Σ?-i : (¬ ∀ a -> ¬ B a) -> Σ? A B; Σ?-i ¬all = ¬all ∘ ¬∃→∀¬
  -- Σ?-e : Σ? A B → ¬ ∀ a -> ¬ B a;    Σ?-e ex = ex ∘ ∀¬→¬∃

  -- make-Σ? : Σ A B -> Σ? A B
  -- make-Σ? x f = f x
