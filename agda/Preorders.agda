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

-- -- This is just a lawless category. We call it Proset because
-- -- (a) it's lawless;
-- -- (b) we care only whether two objects are related, not about the nature of the
-- --     maps between them;
-- -- (c) thus, we don't expect functors to preserve identity and composition;
-- --     they're just monotone maps.
-- record Proset : Set1 where
--   constructor Proset:
--   field obj : Set
--   field rel : (a b : obj) -> Set
--   field preorder : Preorder obj rel

-- open Proset public
-- pattern proset {A} {R} P = Proset: A R P

Proset : Set1
Proset = Cat lzero lzero

obj : Proset -> Set
rel : (P : Proset) -> Rel (obj P)
preorder : (P : Proset) -> Preorder (obj P) (rel P)
obj = Obj; rel = Hom; preorder = compose:Hom

pattern proset {A} {R} P = Cat: A R P

infix 3 _≤_
_≤_ : {{P : Proset}} -> Rel (obj P)
_≤_ = _⇨_

-- A functor, without the laws about preserving id and _•_.
infixr 1 _⇒_
record _⇒_ (A B : Proset) : Set where
  constructor func
  field call : obj A -> obj B
  field mono : ∀{x y} -> x ⇨ y -> call x ⇨ call y

open _⇒_

-- Prosets and ⇒ form a category.
instance
  compose:⇒ : Compose Proset _⇒_
  identity compose:⇒ = func id id
  compose compose:⇒ (func f f≤) (func g g≤) = func (f • g) (f≤ • g≤)


-- Ordering by projection, using Function._on_

-- TODO: check this experimentally: If I made this `instance`, would (Preorder A
-- R) get solved by instance search?
preorder:on : ∀{A B R} f -> Preorder A R -> Preorder B (R on f)
preorder:on _ (Compose: r t) = Compose: r t


-- Pointwise preorder on functions
Pointwise : ∀{A B} -> Rel B -> Rel (A -> B)
Pointwise R f g = ∀ x -> R (f x) (g x)

preorder:Pointwise : ∀{A B R} -> Preorder B R -> Preorder (A -> B) (Pointwise R)
identity (preorder:Pointwise P) _ = id
compose  (preorder:Pointwise p) aRb bRc x = aRb x • bRc x

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
proset:⇒ P Q = proset {P ⇒ Q} (preorder:on call (preorder:Pointwise (preorder Q)))
proset:Iso (proset P) = proset (preorder:Iso P)
proset:Bool = proset preorder:bool≤
