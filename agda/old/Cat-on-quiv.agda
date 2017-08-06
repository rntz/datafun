module Cat-on-quiv where

open import Level

-- -- A generalization of Quiv. I have no use for this at present.
-- record Soup i {j} (S : Set j) : Set (suc i ⊔ j) where
--   constructor Soup:
--   field node : Set i
--   field edge : (a b : node) -> S

-- open Soup public


-- A quiver is a set equipped with a binary "relation" (map into Set).
--
-- ALTERNATIVELY, this is called a "Quiver":
-- https://en.wikipedia.org/wiki/Quiver_(mathematics)
-- maybe I should call it Quiv!
record Quiv i j : Set (suc (i ⊔ j)) where
  constructor Quiv:
  field node : Set i
  field edge : (a b : node) -> Set j

open Quiv public
open Quiv {{...}} using () renaming (edge to _⇨_) public


-- A (lawless) category is a quiv with identity edges & composition.
record IsCat {i j} (A : Quiv i j) : Set (i ⊔ j) where
  constructor IsCat:
  instance aa = A
  field identity : ∀{a} -> a ⇨ a
  field compose : ∀{a b c} -> a ⇨ b -> b ⇨ c -> a ⇨ c

record Cat i j : Set (suc (i ⊔ j)) where
  constructor Cat:
  field objhom : Quiv i j
  field isCat : IsCat objhom
  Obj = node objhom
  Hom = edge objhom

open IsCat public
open Cat public
-- TODO: do we need this pattern?
pattern cat {O} {H} I = Cat: (Quiv: O H) I

id : ∀{i j} {A : Set i} {R : A -> A -> Set j} {{C : IsCat (Quiv: A R)}} {a} -> R a a
_•_ : ∀{i j A} {{C : IsCat {i}{j} A}} {a b c} -> a ⇨ b -> b ⇨ c -> a ⇨ c
id {{C}} = identity C; _•_ {{C}} = compose C

instance
  -- cat-quiv : ∀{i j} {{C : Cat i j}} -> Quiv i j
  -- cat-quiv {{C}} = objhom C

  -- apparently this kills everything if I ever have an IsCat explicitly in
  -- scope instead of a Cat :(.
  --
  -- OK, I really need to minify this problem and ask #agda about it.
  cat-compose : ∀{i j} {{C : Cat i j}} -> IsCat (objhom C)
  cat-compose {{C}} = isCat C


-- Quiv homomorphisms.
record Homo {i j k l} (A : Quiv i j) (B : Quiv k l) : Set (i ⊔ j ⊔ k ⊔ l) where
  constructor Homo:
  -- `ap` for "apply"; `cov` for "covariant".
  field ap : node A -> node B
  field cov : ∀{x y} -> x ⇨ y -> ap x ⇨ ap y

-- Functors without laws are just quiver homomorphisms.
Functor : ∀ {i j k l} (A : Cat i j) (B : Cat k l) -> Set _
Functor A B = Homo (objhom A) (objhom B)

open Homo public
pattern homo {F} f = Homo: F f

open Homo {{...}} public using () renaming (cov to map)


-- Sets & functions form a category.
Set/-> = λ i -> Quiv: (Set i) (λ a b -> a -> b)
isCat:-> : ∀{i} -> IsCat (Set/-> i)
identity isCat:-> x = x
compose  isCat:-> f g x = g (f x)
--instance
cat:Set : ∀{i} -> Cat (suc i) i
cat:Set {i} = cat (isCat:-> {i})

-- Categories & functors form a category.
Quiv/Homo = λ i j -> Quiv: (Quiv i j) Homo
isCat:Homo : ∀ i j -> IsCat (Quiv/Homo i j)
identity (isCat:Homo i j) = homo (λ x -> x)
compose  (isCat:Homo i j) (homo f) (homo g) = homo (λ x -> g (f x))
cat:Quiv = λ i j -> Cat: _ (isCat:Homo i j)
cat:Cat = cat:Quiv

-- The identity functor... just in case someone needs it?
IdentityFunctor : ∀{i j} C -> Functor {i}{j} C C
IdentityFunctor C = homo (id {{isCat:->}})


-- Simple tests

-- open import Data.Nat renaming (suc to ℕ-suc; zero to ℕ-zero)

-- ℕ/≤ = quiv _≤_
-- instance
--   cat:ℕ : Cat _ _
--   cat:ℕ = Cat: ℕ/≤ (IsCat: refl trans)
--     where open import Relation.Binary
--           open DecTotalOrder decTotalOrder

-- foo : ∀{i} {a b c : Set i} -> (a → b) -> (b → c) -> (a → c)
-- foo = _•_

-- bar : ∀{a b c} -> a ≤ b -> b ≤ c -> a ≤ c
-- bar = _•_
