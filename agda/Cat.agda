-- Categories, without the laws, as a "typeclass".
module Cat where

open import Level

record Cat i j : Set (suc (i ⊔ j)) where
  constructor Cat:
  field Obj : Set i
  field Hom : (a b : Obj) -> Set j
  field reflex : ∀{a} -> Hom a a
  field compos : ∀{a b c} -> Hom a b -> Hom b c -> Hom a c

open Cat public

_⇨_ : ∀ {i j} {{C : Cat i j}} (a b : Obj C) -> Set j
_•_ : ∀ {i j} {{C : Cat i j}} {a b c} -> a ⇨ b -> b ⇨ c -> a ⇨ c
id  : ∀ {i j} {{C : Cat i j}} {a} -> a ⇨ a
_⇨_ {{C}} = Hom C
_•_ {{P}} = compos P
id  {{P}} = reflex P

instance
  cat:Set : ∀{i} -> Cat _ _
  Obj (cat:Set {i}) = Set i
  Hom cat:Set A B = A -> B
  reflex cat:Set x = x
  compos  cat:Set f g x = g (f x)

open import Data.Nat

instance
  cat:ℕ : Cat _ _
  Obj cat:ℕ = ℕ
  Hom cat:ℕ = _≤_
  reflex cat:ℕ = {!!}
  compos cat:ℕ = {!!}

ident : ∀{a : Set} -> a -> a
ident = id

duh : 2 ⇨ 4
duh = duh1 • duh2
  where duh1 : 2 ≤ 3; duh1 = s≤s (s≤s z≤n)
        duh2 : 3 ≤ 4; duh2 = s≤s (s≤s (s≤s z≤n))
