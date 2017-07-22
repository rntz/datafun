-- Categories and functors, without the laws, as "typeclasses".
module Cat where

open import Level

infix  3 _≤_
infixr 5 _•_

record Compose {i j} (A : Set i) (R : A -> A -> Set j) : Set (i ⊔ j) where
  constructor Compose:
  field ident : ∀{a} -> R a a
  field compo : ∀{a b c} -> R a b -> R b c -> R a c

record Cat i j : Set (suc (i ⊔ j)) where
  constructor Cat:
  field Obj : Set i
  field Arr : (a b : Obj) -> Set j
  field isCat : Compose Obj Arr

open Compose public
open Compose {{...}} public using () renaming (ident to id)
open Cat public
pattern cat {O} {H} I = Cat: O H I

_≤_ : ∀{i j} {{C : Cat i j}} (a b : Obj C)-> Set j
_≤_ {{C}} = Arr C

_•_ : ∀ {i j A R} {{_ : Compose {i}{j} A R}} {a b c} -> R a b -> R b c -> R a c
_•_ {{P}} = compo P

-- This appears to be critical.
instance
  auto-isCat : ∀{i j} {{C : Cat i j}} -> Compose (Obj C) (Arr C)
  auto-isCat {{C}} = isCat C


-- Functors.
record Homo {i j k l} (A : Cat i j) (B : Cat k l) : Set (i ⊔ j ⊔ k ⊔ l) where
  constructor Homo:
  -- `ap` for "apply"; `cov` for "covariant".
  private instance aa = A; bb = B
  field app : Obj A -> Obj B
  field cov : ∀{x y} -> x ≤ y -> app x ≤ app y

open Homo public
open Homo public using () renaming (app to _‼_)
open Homo {{...}} using () renaming (cov to map) public
pattern homo {F} f = Homo: F f


-- Sets & functions form a category.
Func : ∀{i j} (A : Set i) (B : Set j) -> Set _
Func a b = a -> b

compose:-> : ∀{i} -> Compose (Set i) Func
ident compose:-> x = x
compo compose:-> f g x = g (f x)

instance
  -- This doesn't need to be an instance b/c all that would give us is ≤ as a
  -- notation for non-dependent ->.
  cat:Set : ∀ i -> Cat _ _
  cat:Set i = cat (compose:-> {i})

-- Categories & functors form a category.
instance
  compose:Homo : ∀{i j} -> Compose (Cat i j) Homo
  ident compose:Homo = homo id
  compo compose:Homo (homo x) (homo y) = homo (x • y)

cat:Cat : ∀ i j -> Cat (suc (i ⊔ j)) (i ⊔ j)
cat:Cat i j = cat (compose:Homo {i}{j})

-- Allows using (C ≤ D) syntax for functors between categories with the same
-- Level indices.
instance auto-cat:Cat : ∀{i j} -> Cat _ _; auto-cat:Cat {i}{j} = cat:Cat i j
