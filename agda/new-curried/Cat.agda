-- Categories and functors, without the laws, as "typeclasses".
module Cat where

open import Level

record Compose {i j} (A : Set i) (R : A -> A -> Set j) : Set (i ⊔ j) where
  constructor Compose:
  infixr 5 compo
  field ident : ∀{a} -> R a a
  field compo : ∀{a b c} -> R a b -> R b c -> R a c

record Cat i j : Set (suc (i ⊔ j)) where
  constructor Cat:
  infix 3 Arr
  field Obj : Set i
  field Arr : (a b : Obj) -> Set j
  field instance isCat : Compose Obj Arr

open Compose public
open Compose {{...}} public using () renaming (ident to id; compo to _•_)
open Cat public
open Cat {{...}} public using () renaming (Arr to _≤_)
pattern cat {O} {H} I = Cat: O H I


-- Functors.
record Homo {i j k l} (A : Cat i j) (B : Cat k l) : Set (i ⊔ j ⊔ k ⊔ l) where
  constructor Homo:
  -- `ap` for "apply"; `cov` for "covariant".
  private instance aa = A; bb = B
  field ap : Obj A -> Obj B
  field cov : ∀{x y} -> x ≤ y -> ap x ≤ ap y

open Homo public
open Homo {{...}} using () renaming (cov to map) public
pattern homo {F} f = Homo: F f


-- Some categories.
Func : ∀{i j} (A : Set i) (B : Set j) -> Set _
Func a b = a -> b

instance
  compose:-> : ∀{i} -> Compose (Set i) Func
  ident compose:-> x = x
  compo compose:-> f g x = g (f x)

  compose:Homo : ∀{i j} -> Compose (Cat i j) Homo
  ident compose:Homo = homo id
  compo compose:Homo (homo x) (homo y) = homo (x • y)

-- This doesn't need to be an instance b/c all that would give us is ≤ as a
-- notation for non-dependent ->.
cat:set : ∀ i -> Cat _ _
cat:set i = cat (compose:-> {i})

cat:cat : ∀ i j -> Cat (suc (i ⊔ j)) (i ⊔ j)
cat:cat i j = cat (compose:Homo {i}{j})

-- Allows using (C ≤ D) syntax for functors between categories with the same
-- Level indices.
instance auto-cat:cat : ∀{i j} -> Cat _ _; auto-cat:cat {i}{j} = cat:cat i j
