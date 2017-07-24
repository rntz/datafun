-- Categories and functors, without the laws, as "typeclasses".
module Cat where

open import Level
open import Relation.Binary using (Rel)

Function : ∀{i j} (A : Set i) (B : Set j) -> Set (i ⊔ j)
Function a b = a -> b

---------- Categories ----------
record Compose {i j} Obj (Arr : Rel {i} Obj j) : Set (i ⊔ j) where
  constructor Compose:
  infixr 9 _•_
  field id : ∀{a} -> Arr a a
  field _•_ : ∀{a b c} -> Arr a b -> Arr b c -> Arr a c

record Cat i j : Set (suc (i ⊔ j)) where
  constructor Cat:
  field Obj : Set i
  field Arr : (a b : Obj) -> Set j
  field ident : ∀{a} -> Arr a a
  field compo : ∀{a b c} -> Arr a b -> Arr b c -> Arr a c

  instance
    cat->compose : Compose Obj Arr
    cat->compose = Compose: ident compo

open Compose {{...}} public
open Compose public using () renaming (id to ident; _•_ to compo)
open Cat public

infix  1 _≤_
_≤_ : ∀{i j} {{C : Cat i j}} (a b : Obj C) -> Set j
_≤_ {{C}} = Arr C

cat : ∀{i j A R} -> Compose {i}{j} A R -> Cat i j
cat {A = A} {R = R} C = Cat: A R (ident C) (compo C)


---------- Functors ----------
record Homo {i j k l} (A : Cat i j) (B : Cat k l) : Set (i ⊔ j ⊔ k ⊔ l) where
  constructor Homo:
  field app : Obj A -> Obj B
  field cov : ∀{a b} -> Arr A a b -> Arr B (app a) (app b)

open Homo public
pattern homo {app} f = Homo: app f
-- FIXME TODO does this definition of `map` even work wrt instance resolution?
open Homo {{...}} public using () renaming (cov to map)
-- module _ {i j k l} {{A : Cat i j}} {{B : Cat k l}} {{F : Homo A B}} where
--   open Homo F public using () renaming (cov to map)


---------- Some useful categories ----------
instance
  compose:-> : ∀{i} -> Compose (Set i) Function
  ident compose:-> x = x
  compo compose:-> f g x = g (f x)

  compose:homo : ∀{i j} -> Compose (Cat i j) Homo
  ident compose:homo = homo id
  compo compose:homo (homo f) (homo g) = homo (f • g)

  cat:set : ∀ {i} -> Cat _ _
  cat:set {i} = cat (compose:-> {i})
  cat:cat : ∀{i j} -> Cat _ _
  cat:cat {i} {j} = cat (compose:homo {i}{j})
