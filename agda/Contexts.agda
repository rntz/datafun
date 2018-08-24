module Contexts (Type : Set) where

open import Prelude
open import Cat

---------- Contexts ----------
Cx : Set1
Cx = Type -> Set

hyp : Type -> Cx
hyp = _≡_

-- TODO: Stop using _∪_, use _∨_ instead.
infixr 4 _∪_
_∪_ : Cx -> Cx -> Cx
(X ∪ Y) a = X a ⊎ Y a

infixr 4 _∷_
_∷_ : Type -> Cx -> Cx
a ∷ X = hyp a ∪ X

pattern here = inj₁ Eq.refl
pattern next x = inj₂ x


---------- Context renamings ----------
infix 1 _⊆_
_⊆_ : Cx -> Cx -> Set
X ⊆ Y = ∀ a -> X a -> Y a

instance
  cxs : Cat _ _
  cxs = Cat: Cx _⊆_ (λ _ → id) (λ X⊆Y Y⊆Z x → X⊆Y x • Y⊆Z x)

  cx-sums : Sums cxs
  bottom cx-sums = (λ a → ⊥) , λ _ ()
  lub cx-sums X Y = (λ a → X a ⊎ Y a) / (λ _ → inj₁) / (λ _ → inj₂) / λ f g x → [ f x , g x ]

∪/⊆ : ∀ {X L R} -> L ⊆ R -> X ∪ L ⊆ X ∪ R
∪/⊆ = map∨ id
