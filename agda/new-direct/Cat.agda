-- Categories and functors, without the laws, as "typeclasses".
module Cat where

open import Level
open import Relation.Binary using (Rel)

infix  1 _≤_

record Compose {i j} Obj (Arr : Rel {i} Obj j) : Set (i ⊔ j) where
  constructor Compose:
  infixr 9 _•_
  field id : ∀{a} -> Arr a a
  field _•_ : ∀{a b c} -> Arr a b -> Arr b c -> Arr a c

open Compose {{...}} public

record Cat i j : Set (suc (i ⊔ j)) where
  field Obj : Set i
  field Arr : (a b : Obj) -> Set j
  field ident : ∀{a} -> Arr a a
  field compo : ∀{a b c} -> Arr a b -> Arr b c -> Arr a c

open Cat public

_≤_ : ∀{i j} {{C : Cat i j}} (a b : Obj C) -> Set j; _≤_ {{C}} = Arr C

instance
  -- wait, this apparently has an effect?! despite taking an explicit argument?!
  cat->compose : ∀{i j} (C : Cat i j) -> Compose (Obj C) (Arr C)
  cat->compose C = Compose: (ident C) (compo C)
  -- cat->compose : ∀{i j} {{C : Cat i j}} -> Compose (Obj C) (Arr C)
  -- cat->compose {{C}} = Compose: (ident C) (compo C)

make-cat : ∀{i j A R} -> Compose {i}{j} A R -> Cat i j
make-cat {A = A} {R = R} C =
  record { Obj = A ; Arr = R ; ident = id {{C}} ; compo = _•_ {{C}} }

-- Functors
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


-- Some useful categories.
Function : ∀{i j} (A : Set i) (B : Set j) -> Set (i ⊔ j)
Function a b = a -> b

instance
  cat:set : ∀{i} -> Cat _ _
  Obj (cat:set {i}) = Set i
  Arr cat:set = Function
  ident cat:set x = x
  compo cat:set f g x = g (f x)

  cat:cat : ∀{i j} -> Cat _ _
  Obj (cat:cat {i}{j}) = Cat i j
  Arr cat:cat = Homo
  ident cat:cat = homo id
  compo cat:cat (homo f) (homo g) = homo (f • g)
