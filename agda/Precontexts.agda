-- Generalizing "contexts as functions from types to Set", contexts as
-- _functors_ from types to sets. Here, the preorder on types could be a
-- subtyping relation, for example.
open import Prelude
open import Cat

module Precontexts (types : Proset) where

private Type = Obj types
private instance types-instance = types

---------- Contexts ----------
instance
  cxs : Cat (suc zero) zero
  cxs = cat→ types (sets {zero})

cx-sums : Sums cxs
cx-sums = it

Cx : Set1
Cx = Obj cxs

hyp : Type → Cx
hyp a .ap b = a ≤ b
hyp a .map a≤b b≤c = b≤c ∙ a≤b

Hyp : Fun (op types) cxs
ap Hyp = hyp
map Hyp b≤a a≤c = b≤a ∙ a≤c
-- map Hyp b≤a c≤d a≤c = b≤a ∙ a≤c ∙ c≤d

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
