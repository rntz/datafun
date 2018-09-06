open import Prelude
open import Cat
open import Tones

module Precontexts (types : Proset) where

private Type = Obj types
private instance types-instance = types

---------- Contexts ----------
instance
  contexts : Cat (suc zero) zero
  contexts = cat→ types (sets {zero})

context-sums : Sums contexts
context-sums = it

Cx : Set1
Cx = Obj contexts

hyp : Type → Cx
hyp a .ap b = a ≤ b
hyp a .map a≤b b≤c = b≤c • a≤b

Hyp : Fun (op types) contexts
ap Hyp = hyp
map Hyp b≤a a≤c = b≤a • a≤c
-- map Hyp b≤a c≤d a≤c = b≤a • a≤c • c≤d

infixr 4 _∷_
_∷_ : Type -> Cx -> Cx
a ∷ X = hyp a ∨ X

infix 5 _∈_
_∈_ : Type → Cx → Set
a ∈ X = ap X a

pattern here = inj₁ Eq.refl
pattern next x = inj₂ x

∪/⊆ : {L R : Cx} → L ≤ R → ∀{X} → X ∨ L ≤ X ∨ R
∪/⊆ f = map∨ id f
-- ∪/⊆ = map∨₂
