module Tmp where

open import Level

-- Ways of doing this:
--
--
-- 1. {A : Set i} {R : Rel A j} {{_ : Cat A R}}
-- or {A R} {{_ : Cat i j A R}}
--
-- 2. {Q : Quiv i j} {{_ : Cat Q}}
-- or {Q} {{_ : Cat i j Q}}
--
-- 3. {{_ : Cat i j}}

record Cat i j : Set (suc (i ⊔ j)) where
  field Obj : Set i
  field Arr : (a b : Obj) -> Set j
  field ident : ∀{a} -> Arr a a
  field compo : ∀{a b c} -> Arr a b -> Arr b c -> Arr a c

open Cat public
open Cat {{...}} public using () renaming (Arr to _⇨_; ident to id; compo to _•_)

record Homo {i j k l} (A : Cat i j) (B : Cat k l) : Set (i ⊔ j ⊔ k ⊔ l) where
  constructor Homo:
  private instance xx = A; instance yy = B
  field app : Obj A -> Obj B
  field cov : ∀{a b} -> a ⇨ b -> app a ⇨ app b

open Homo public
open Homo {{...}} public using () renaming (cov to map)
pattern homo {F} f = Homo: F f


-- Some categories
cat:Set : ∀ i -> Cat _ _
Obj (cat:Set i) = Set i
Arr (cat:Set i) a b = a -> b
ident (cat:Set i) x = x
compo (cat:Set i) f g x = g (f x)

instance autocat:Set : ∀{i} -> Cat _ _; autocat:Set {i} = cat:Set i

cat:Cat : ∀ i j -> Cat _ _
Obj (cat:Cat i j) = Cat i j
Arr (cat:Cat i j) = Homo
ident (cat:Cat i j) = homo id
compo (cat:Cat i j) (homo f) (homo g) = homo (f • g)

instance autocat:Cat : ∀{i j} -> Cat _ _; autocat:Cat {i}{j} = cat:Cat i j

postulate ℕ : Set
f : ℕ -> ℕ
f = id
