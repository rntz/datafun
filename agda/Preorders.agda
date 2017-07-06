module Preorders where

open import Prelude
import Data.Product

Rel : Set -> Set₁
Rel a = a -> a -> Set

Reflexive Transitive : ∀{A} -> Rel A -> Set
Reflexive {A} R = ∀{a} -> R a a
Transitive {A} R = ∀{a b c} -> R a b -> R b c -> R a c

Respects : ∀ {A B} (R : Rel A) (Q : Rel B) (f : A -> B) -> Set
Respects R Q f = ∀ {a b} -> R a b -> Q (f a) (f b)

Preorder : ∀ A -> Rel A -> Set
Preorder A R = Compose A R

-- A proset is just a name for a category regarded a certain way: we only care
-- about whether (a ⇨ b) is inhabited, not about its structure. In particular,
-- maps between prosets don't need to preserve id and •. (Although probably most
-- of those we define do, if you use the right equivalence relation.)
Proset : Set1
Proset = Cat lzero lzero
cat:Proset = cat:Cat lzero lzero
pattern proset {A} {R} P = Cat: A R P
preorder : ∀ P -> Preorder _ (Hom P)
preorder = isCat

-- For readability's sake, we define _⇒_ for monotone maps (i.e. functors) and
-- _≤_ for preorder relations (i.e. Hom-sets).
infix 3 _⇒_; _⇒_ : (a b : Proset) -> Set; _⇒_ = Functor
infix 3 _≤_; _≤_ : {{P : Proset}} -> Rel (Obj P); _≤_ = _⇨_


-- Ordering by projection, using Function._on_

-- this looks like a contravariant mapping function. Hm...
preorder:on : ∀{A B R} (f : B -> A) -> Preorder A R -> Preorder B (R on f)
preorder:on _ (Compose: r t) = Compose: r t


-- Pointwise preorder on functions
Pointwise : ∀{A B} -> Rel B -> Rel (A -> B)
Pointwise R f g = ∀ x -> R (f x) (g x)

preorder:Pointwise : ∀{A B R} -> Preorder B R -> Preorder (A -> B) (Pointwise R)
identity (preorder:Pointwise P) _ = id
compose  (preorder:Pointwise p) aRb bRc x = aRb x • bRc x

-- record Denotation {i j} (A : Set i) (B : Set j) : Set (i ⊔ j) where
--   field denotation : A -> B

-- open Denotation public
-- ⟦_⟧ : ∀ {i j A B} {{D : Denotation {i} {j} A B}} -> A -> B
-- ⟦_⟧ {{D}} = denotation D

proset:Pointwise : Set -> Proset -> Proset
Obj (proset:Pointwise A B) = A -> Obj B
Hom (proset:Pointwise A B) = Pointwise (Hom B)
identity (isCat (proset:Pointwise A (cat B))) _ = id
compose (isCat (proset:Pointwise A (cat B))) aRb bRc x = aRb x • bRc x

PointwiseΠ : ∀ A (B : A -> Set) (R : ∀ x -> Rel (B x)) -> Rel (∀ x -> B x)
PointwiseΠ _ _ R f g = ∀ x → R x (f x) (g x)

-- DEPENDENT FUNCTION TIME
preorder:PointwiseΠ : ∀ {A B R}
                    -> (∀ x -> Preorder (B x) (R x))
                    -> Preorder (∀ x -> B x) (PointwiseΠ A B R)
identity (preorder:PointwiseΠ P) x = identity (P x)
compose  (preorder:PointwiseΠ P) fRg gRh x = compose (P x) (fRg x) (gRh x)

proset:Π : ∀ {A : Set} (B : A -> Proset) -> Proset
proset:Π B = proset (preorder:PointwiseΠ (preorder ∘ B))


-- Products and sums
_⊗_ : ∀ {A B} (R : Rel A) (S : Rel B) -> Rel (A × B)
_⊗_ R S (a , x) (b , y) = R a b × S x y

data _⊕_ {A B} (R : Rel A) (S : Rel B) : Rel (A ⊎ B) where
  rel₁ : ∀{x y} -> R x y -> (R ⊕ S) (inj₁ x) (inj₁ y)
  rel₂ : ∀{x y} -> S x y -> (R ⊕ S) (inj₂ x) (inj₂ y)

module _ {A B R S} (P : Preorder A R) (Q : Preorder B S) where
  preorder:⊗ : Preorder (A × B) (R ⊗ S)
  preorder:⊗ = Compose: (id , id) (Data.Product.zip _•_ _•_)

  preorder:⊕ : Preorder (A ⊎ B) (R ⊕ S)
  identity preorder:⊕ {inj₁ _} = rel₁ id
  identity preorder:⊕ {inj₂ _} = rel₂ id
  compose  preorder:⊕ (rel₁ x) (rel₁ y) = rel₁ (x • y)
  compose  preorder:⊕ (rel₂ x) (rel₂ y) = rel₂ (x • y)


-- The "discrete" or "equivalence quotient" preorder.
-- TODO: maybe prove this is an equivalence relation?
Iso : ∀{A} -> Rel A -> Rel A
Iso R x y = R x y × R y x

preorder:Iso : ∀{A R} (P : Preorder A R) -> Preorder A (Iso R)
identity (preorder:Iso P) = id , id
compose  (preorder:Iso P) = Data.Product.zip _•_ (flip _•_)


-- The booleans, ordered false < true.
data bool≤ : Rel Bool where
  bool-refl : Reflexive bool≤
  false<true : bool≤ false true

preorder:bool≤ : Preorder Bool bool≤
identity preorder:bool≤ = bool-refl
compose  preorder:bool≤ bool-refl y = y
compose  preorder:bool≤ false<true bool-refl = false<true


-- Reflexive transitive closure of a relation
data Path {A} (R : Rel A) : Rel A where
  path-edge : ∀{a b} -> R a b -> Path R a b
  path-refl : Reflexive (Path R)
  path-trans : Transitive (Path R)

preorder:Path : ∀{A R} -> Preorder A (Path R)
preorder:Path = Compose: path-refl path-trans


-- Boilerplate.
proset:× proset:⊎ proset:⇒ : Proset -> Proset -> Proset
proset:Iso : Proset -> Proset
proset:Bool : Proset

proset:× (proset P) (proset Q) = proset (preorder:⊗ P Q)
proset:⊎ (proset P) (proset Q) = proset (preorder:⊕ P Q)
proset:⇒ P Q =
  proset {P ⇒ Q} (preorder:on ap (preorder:Pointwise (preorder Q)))
proset:Iso (proset P) = proset (preorder:Iso P)
proset:Bool = proset preorder:bool≤
