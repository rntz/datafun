open import Prelude
open import Cat.Base
open import Cat.Cartesian

module Cat.Closed where

--- CC means "cartesian closed".
record CC {i j} (C : Cat i j) : Set (i ⊔ j) where
  constructor CC:
  private instance the-cat = C
  -- I used to have an "overlap" modifier on `products`. I removed it and
  -- everything /seems/ ok. TODO: Is "overlap" necessary here?
  field {{products}} : Products C
  -- TODO FIXME: shouldn't bind tighter than ∧.
  infixr 4 hom
  field hom : BinOp (Obj C)
  field apply : ∀{a b} -> hom a b ∧ a ≤ b
  field curry : ∀{Γ a b} -> Γ ∧ a ≤ b -> Γ ≤ hom a b

  call : ∀{Γ a b} -> Γ ≤ hom a b -> Γ ≤ a -> Γ ≤ b
  call f a = ⟨ f , a ⟩ ∙ apply

  swapply : ∀{a b : Obj C} -> a ∧ hom a b ≤ b
  swapply = swap ∙ apply

  uncurry : ∀{a b c : Obj C} -> a ≤ hom b c -> a ∧ b ≤ c
  uncurry f = map∧ f id ∙ apply

  flip : ∀{a b c : Obj C} -> a ≤ hom b c -> b ≤ hom a c
  flip f = curry (swap ∙ uncurry f)

  precompose : ∀{a b c : Obj C} -> a ≤ b -> hom b c ≤ hom a c
  precompose f = curry (map∧ id f ∙ apply)

  module _ {{S : Sums C}} where
    distrib-∧/∨ : ∀{a b c : Obj C} -> (a ∨ b) ∧ c ≤ (a ∧ c) ∨ (b ∧ c)
    distrib-∧/∨ = map∧ [ curry in₁ , curry in₂ ] id ∙ apply

open CC public using (hom)
module _ {i j} {{C : Cat i j}} {{cc : CC C}} where
  open CC cc public renaming (hom to _⇨_) hiding (products)
