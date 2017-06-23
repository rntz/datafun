-- Categories, without the laws, as a "typeclass".
module Composition where

open import Level

infix  3 _⇨_
infixr 5 _•_

record Compose {i j} (A : Set i) (R : A -> A -> Set j) : Set (i ⊔ j) where
  constructor Compose:
  field identity : ∀{a} -> R a a
  field compose : ∀{a b c} -> R a b -> R b c -> R a c

record Cat i j : Set (suc (i ⊔ j)) where
  constructor Cat:
  field Obj : Set i
  field Hom : (a b : Obj) -> Set j
  field compose:Hom : Compose Obj Hom

open Compose public
open Cat public

pattern cat {O} {H} I = Cat: O H I

_•_ : ∀ {i j A R} {{_ : Compose {i}{j} A R}} {a b c} -> R a b -> R b c -> R a c
id  : ∀ {i j A R} {{_ : Compose {i}{j} A R}} {a} -> R a a
_•_ {{P}} = compose P
id  {{P}} = identity P

_⇨_ : ∀{i j} {{C : Cat i j}} (a b : Obj C)-> Set j
_⇨_ {{C}} = Hom C


-- Function composition
instance
  compose:-> : ∀{i} -> Compose (Set i) (λ a b -> a -> b)
  identity compose:-> x = x
  compose compose:-> f g x = g (f x)

-- cat:Set : ∀{i} -> Cat (suc i) i
-- cat:Set = cat compose:->
