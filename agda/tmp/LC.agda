module LC where

open import Prelude

-- infix 4 _∘'_
-- _∘'_ : ∀{i j A R} {{C : Compose {i}{j} A R}} {a b c} -> R b c -> R a b -> R a c
-- f ∘' g = g • f

module _ {i j} {C : Cat i j} {_⊗_ _⊕_ hom}
         {{Prod : Products C _⊗_}}
         {{Sum : Sums C _⊕_}}
         {{Clo : Closed C _⊗_ hom}}
  where
  --private instance the-compose = isCat C

  open import Data.Nat
  x : ℕ
  x = 2

  hlkasdjflkjsdlkfjsdf : ∀{Γ a b} -> Γ ⊗ a ⇨ b -> Γ ⇨ hom a b
  hlkasdjflkjsdlkfjsdf = curry

  -- -- the rules of the simply typed lambda calculus!
  -- call : ∀{Γ a b} -> Γ ⇨ hom a b -> Γ ⇨ a -> Γ ⇨ b
  -- call M N = ⟨ M , N ⟩ • apply

  -- infixl 1 _$_
  -- _$_ = call

  -- λ! = call

  -- lambda : ∀{Γ a b} -> Γ ⊗ a ⇨ b -> Γ ⇨ hom a b
  -- lambda = curry

  -- pair : ∀{Γ a b} -> Γ ⇨ a -> Γ ⇨ b -> Γ ⇨ a ⊗ b
  -- pair = ⟨_,_⟩

