-- Categories and functors, without the laws, as "typeclasses".
module Cat where

open import Level

infix  3 _⇨_
infixr 5 _•_
infixl 5 _⟨$⟩_

record Compose {i j} (A : Set i) (R : A -> A -> Set j) : Set (i ⊔ j) where
  constructor Compose:
  field identity : ∀{a} -> R a a
  field compose : ∀{a b c} -> R a b -> R b c -> R a c

record Cat i j : Set (suc (i ⊔ j)) where
  constructor Cat:
  field Obj : Set i
  field Hom : (a b : Obj) -> Set j
  field isCat : Compose Obj Hom

open Compose public
open Cat public
pattern cat {O} {H} I = Cat: O H I

_•_ : ∀ {i j A R} {{_ : Compose {i}{j} A R}} {a b c} -> R a b -> R b c -> R a c
id  : ∀ {i j A R} {{_ : Compose {i}{j} A R}} {a} -> R a a
_⇨_ : ∀{i j} {{C : Cat i j}} (a b : Obj C)-> Set j
_•_ {{P}} = compose P; id {{P}} = identity P; _⇨_ {{C}} = Hom C


-- Functors.
record Functor {i j k l} (A : Cat i j) (B : Cat k l) : Set (i ⊔ j ⊔ k ⊔ l) where
  constructor Functor:
  -- `ap` for "apply"; `cov` for "covariant".
  field ap : Obj A -> Obj B
  field cov : ∀{x y} -> x ⇨ y -> ap x ⇨ ap y

open Functor public
pattern functor {F} f = Functor: F f

map : ∀{i j k l A B} {{F : Functor {i}{j}{k}{l} A B}} {x y}
    -> x ⇨ y -> ap F x ⇨ ap F y
map {{F}} = cov F

_⟨$⟩_ = map


-- Sets & functions form a category.
instance
  compose:-> : ∀{i} -> Compose (Set i) (λ a b -> a -> b)
  identity compose:-> x = x
  compose compose:-> f g x = g (f x)

-- This doesn't need to be an instance b/c all that would give us is ⇨ as a
-- notation for non-dependent ->.
cat:Set : ∀ i -> Cat _ _
cat:Set i = cat (compose:-> {i})

-- The identity functor... just in case someone needs it?
IdentityFunctor : ∀{i j} C -> Functor {i}{j} C C
IdentityFunctor C = functor id

-- Categories & functors form a category.
instance
  compose:Functor : ∀{i j} -> Compose (Cat i j) Functor
  identity compose:Functor = functor id
  compose compose:Functor (functor x) (functor y) = functor (x • y)

cat:Cat : ∀ i j -> Cat (suc (i ⊔ j)) (i ⊔ j)
cat:Cat i j = cat (compose:Functor {i}{j})

-- Allows using (C ⇨ D) syntax for functors between categories with the same
-- Level indices.
instance auto-cat:Cat : ∀{i j} -> Cat _ _; auto-cat:Cat {i}{j} = cat:Cat i j
