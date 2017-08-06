-- Categories and functors, without the laws, as "typeclasses".
module Cat where

open import Level

infix  3 _⇨_
infixr 5 _•_

record Compose {i j} (A : Set i) (R : A -> A -> Set j) : Set (i ⊔ j) where
  constructor Compose:
  field ident : ∀{a} -> R a a
  field compo : ∀{a b c} -> R a b -> R b c -> R a c

record Cat i j : Set (suc (i ⊔ j)) where
  constructor Cat:
  field Obj : Set i
  field Arr : (a b : Obj) -> Set j
  field instance isCat : Compose Obj Arr

open Compose public
open Compose {{...}} public using () renaming (ident to id)
open Cat public
pattern cat {O} {H} I = Cat: O H I

_⇨_ : ∀{i j} {{C : Cat i j}} (a b : Obj C)-> Set j
_⇨_ {{C}} = Arr C

_•_ : ∀ {i j A R} {{_ : Compose {i}{j} A R}} {a b c} -> R a b -> R b c -> R a c
_•_ {{P}} = compo P


-- Functors.
record Functor {i j k l} (A : Cat i j) (B : Cat k l) : Set (i ⊔ j ⊔ k ⊔ l) where
  constructor Functor:
  -- `ap` for "apply"; `cov` for "covariant".
  private instance aa = A; bb = B
  field ap : Obj A -> Obj B
  field cov : ∀{x y} -> x ⇨ y -> ap x ⇨ ap y

open Functor public
open Functor public using () renaming (ap to _‼_)
open Functor {{...}} using () renaming (cov to map) public
pattern functor {F} f = Functor: F f


-- Sets & functions form a category.
instance
  compose:-> : ∀{i} -> Compose (Set i) (λ a b -> a -> b)
  ident compose:-> x = x
  compo compose:-> f g x = g (f x)

-- This doesn't need to be an instance b/c all that would give us is ⇨ as a
-- notation for non-dependent ->.
cat:Set : ∀ i -> Cat _ _
cat:Set i = cat (compose:-> {i})

-- Categories & functors form a category.
instance
  compose:Functor : ∀{i j} -> Compose (Cat i j) Functor
  ident compose:Functor = functor id
  compo compose:Functor (functor x) (functor y) = functor (x • y)

cat:Cat : ∀ i j -> Cat (suc (i ⊔ j)) (i ⊔ j)
cat:Cat i j = cat (compose:Functor {i}{j})

-- Allows using (C ⇨ D) syntax for functors between categories with the same
-- Level indices.
instance auto-cat:Cat : ∀{i j} -> Cat _ _; auto-cat:Cat {i}{j} = cat:Cat i j
