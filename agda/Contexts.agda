module Contexts (Type : Set) where

open import Prelude
open import Cartesian


---------- Contexts ----------
Cx : Set1
Cx = Type -> Set

∅ : Cx
∅ _ = ⊥

-- infix 4 _∈_
-- _∈_ : Type -> Cx -> Set
-- a ∈ X = X a

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
X ⊆ Y = ∀ a -> X a -> Y a

instance
  compose:Cx : Compose Cx _⊆_
  identity compose:Cx _ = id
  compose  compose:Cx X⊆Y Y⊆Z o = X⊆Y o • Y⊆Z o

cat:Cx = cat compose:Cx

-- ∪ forms coproducts on Cx under renaming.
instance
  sums:Cx : Sums cat:Cx _∪_
  in₁ {{sums:Cx}} _ = inj₁
  in₂ {{sums:Cx}} _ = inj₂
  [_,_] {{sums:Cx}} f g _ = [ f _ , g _ ]

-- TODO: does this really need X and L to be explicit arguments?
∪/⊆ : ∀ {X L R} -> L ⊆ R -> X ∪ L ⊆ X ∪ R
∪/⊆ f = [ in₁ , f • in₂ ]

∷/⊆ : ∀ L {R a} -> L ⊆ R -> a ∷ L ⊆ a ∷ R
∷/⊆ _ = ∪/⊆
