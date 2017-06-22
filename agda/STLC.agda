-- Interpreting a non-modal STLC into Posets.
module STLC where

open import Level renaming (zero to lzero; suc to lsuc)

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open import Data.Bool
open import Data.Empty
open import Data.Product
open import Data.Unit

open import Preorders
import Trees
open Trees using (TreeSet)


---------- Types and contexts ----------
infixr 6 _⊃_
data Type : Set where
  bool : Type
  setof : Type -> Type
  disc : Type -> Type
  _⊃_ : Type -> Type -> Type

open import Contexts (Type)


---------- Terms ----------
infix 1 _⊢_
data _⊢_ (X : Cx) : Type -> Set where
  var : ∀{a} (x : a ∈ X) -> X ⊢ a
  lam : ∀{a b} (M : a ∷ X ⊢ b) -> X ⊢ a ⊃ b
  app : ∀{a b} (M : X ⊢ a ⊃ b) (N : X ⊢ a) -> X ⊢ b

  -- -- Booleans
  -- boolean : (x : Bool) -> X ⊢ bool
  -- -- wait, this is non-monotone! aghksdfjlsdfjs
  -- ifThen : ∀{a} (M : X ⊢ bool) (N₁ N₂ : X ⊢ a) -> X ⊢ a
  -- -- Sets
  -- empty : ∀{a} -> X ⊢ setof a
  -- single : ∀{a} (M : X ⊢ a) -> X ⊢ setof a
  -- union : ∀{a} -> (M N : X ⊢ setof a) -> X ⊢ setof a
  -- -- This unnecessarily requires us to be monotone. Hm.
  -- setBind : ∀{a b} (M : X ⊢ setof a) (N : a ∷ X ⊢ setof b) -> X ⊢ setof b

-- -- Renaming
-- rename : ∀{X Y a} -> X ⊆ Y -> X ⊢ a -> Y ⊢ a
-- rename f (var x) = var (f x)
-- rename {X} f (lam M) = lam (rename (∷/⊆ X f) M)
-- rename f (app M N) = app (rename f M) (rename f N)
-- rename f (boolean x) = boolean x
-- rename f (ifThen M N₁ N₂) = ifThen (rename f M) (rename f N₁) (rename f N₂)


-- Denotations
⟦_⟧ : Type -> Proset
⟦ bool ⟧ = Proset:Bool
⟦ setof t ⟧ = TreeSet (carrier ⟦ t ⟧)
⟦ disc t ⟧ = Proset:Iso ⟦ t ⟧
⟦ s ⊃ t ⟧ = Proset:⇒ ⟦ s ⟧ ⟦ t ⟧

