module QuivTest where

open import Level

auto : ∀{i}{A : Set i}{{X : A}} -> A
auto {{X}} = X

record Quiv i j : Set (suc (i ⊔ j)) where
  constructor quiv
  eta-equality
  field Obj : Set i
  field Arr : (a b : Obj) -> Set j

open Quiv public

record Cat i j (Q : Quiv i j) : Set (i ⊔ j) where
  field ident : ∀{a} -> Arr Q a a
  field compo : ∀{a b c} -> Arr Q a b -> Arr Q b c -> Arr Q a c

open Cat public
id : ∀{i j A R} {{C : Cat i j (quiv A R)}} {a} -> R a a
id {{C}} = ident C
_•_ : ∀{i j A R} {{C : Cat i j (quiv A R)}} {a b c} -> R a b -> R b c -> R a c
_•_ {{C}} = compo C

_⇨_ : ∀{i j A}{{_ : Cat i j A}} -> (a b : Obj A) -> Set j
_⇨_ {A = A} = Arr A

quiv:Set : ∀ i -> Quiv _ _
Obj (quiv:Set i) = Set i
Arr (quiv:Set i) a b = a -> b
instance
  cat:Set : ∀ {i} -> Cat _ _ (quiv:Set i)
  ident cat:Set x = x
  compo cat:Set f g x = g (f x)

_∘_ : ∀{a b c : Set} -> (b -> c) -> (a -> b) -> a -> c
_∘_ f g = _•_ {{cat:Set}} g f
