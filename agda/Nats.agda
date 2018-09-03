open import Prelude
open import Cat
-- Natural numbers. TODO: put these in their own module?
open import Data.Nat as Nat using (ℕ; z≤n; s≤s) renaming (_≤_ to _≤'_; _⊔_ to _⊔'_)
open import Data.Nat.Properties as ℕProp

module Nats where

instance
  ℕ≤ : Proset
  ℕ≤ = Cat: ℕ Nat._≤_ ℕProp.≤-refl ℕProp.≤-trans

  -- ℕ forms a semilattice with 0 and ⊔ (max).
  ℕ-sums : Sums ℕ≤
  bottom ℕ-sums = 0 , z≤n
  lub ℕ-sums x y = x Nat.⊔ y / ℕProp.m≤m⊔n x y / ℕProp.n≤m⊔n x y / ℕ⊔-is-lub
    where ℕ⊔-is-lub : ∀{x y z} → x ≤ z → y ≤ z → x Nat.⊔ y ≤ z
          ℕ⊔-is-lub z≤n b = b
          ℕ⊔-is-lub (s≤s a) z≤n = s≤s a
          ℕ⊔-is-lub (s≤s a) (s≤s b) = s≤s (ℕ⊔-is-lub a b)
