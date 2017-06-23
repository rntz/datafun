module Contexts (Type : Set) where

open import Prelude
open import Data.Sum using ([_,_])


---------- Contexts ----------
Cx : Set1
Cx = Type -> Set

∅ : Cx
∅ _ = ⊥

infix 4 _∈_
_∈_ : Type -> Cx -> Set
a ∈ X = X a

hyp : Type -> Cx
hyp = _≡_

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
X ⊆ Y = ∀ {a} -> X a -> Y a

∪/⊆ : ∀ X L {R} -> L ⊆ R -> X ∪ L ⊆ X ∪ R
∪/⊆ _ _ f = Data.Sum.map id f

∷/⊆ : ∀ L {R a} -> L ⊆ R -> a ∷ L ⊆ a ∷ R
∷/⊆ _ = ∪/⊆ _ _

dedup : ∀ X -> X ∪ X ⊆ X
dedup _ = [ id , id ]
