module Sem where

open import Data.Bool
open import Data.Empty
open import Data.Unit using (⊤; tt)
open import Level
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Product
open import Data.Sum

-- from https://agda.readthedocs.io/en/latest/language/instance-arguments.html
-- They call this "it", I call it "auto"
auto : ∀ {i} {A : Set i} {{_ : A}} -> A
auto {{x}} = x


---------- Relations ----------
Rel : Set -> Set₁
Rel a = a -> a -> Set

Reflexive Transitive : ∀{A} -> Rel A -> Set
Reflexive {A} R = ∀{a} -> R a a
Transitive {A} R = ∀{a b c} -> R a b -> R b c -> R a c

record IsPreorder {A} (R : Rel A) : Set where
  constructor IsPreorder:
  field
    reflexive : Reflexive R
    transitive : Transitive R

record Preorder (A : Set) : Set₁ where
  constructor Preorder:
  field
    rel : Rel A
    isPreorder : IsPreorder rel

open IsPreorder
open Preorder

Proset : Set₁
Proset = Σ Set Preorder

carrier : Proset -> Set
carrier = proj₁

preorder : (P : Proset) -> Preorder (carrier P)
preorder = proj₂


---------- IsPreorder as a typeclass ----------

-- Constructs the "natural" preorder on A, if it exists.
--
-- We don't declare this "instance" because there might be multiple R's
-- implicitly satisfying IsPreorder.
the-preorder : ∀{A R} {{_ : IsPreorder {A} R}} -> Preorder A
the-preorder = Preorder: _ auto

---------- Preorder as a typeclass ----------
_≤_ : {A : Set} {{pre : Preorder A}} -> Rel A
_≤_ {{P}} = rel P

is-preorder : {A : Set} {{pre : Preorder A}} -> IsPreorder _≤_
is-preorder = isPreorder auto

as-proset : (A : Set) {{pre : Preorder A}} -> Proset
as-proset A = A , auto


---------- Preorder constructions ----------
data bool≤ : Rel Bool where
  bool-refl : ∀{a} -> bool≤ a a
  false<true : bool≤ false true

instance
  IsPreorder:bool≤ : IsPreorder bool≤
  reflexive IsPreorder:bool≤ = bool-refl
  transitive IsPreorder:bool≤ bool-refl y = y
  transitive IsPreorder:bool≤ false<true bool-refl = false<true

  Bool≤ : Preorder Bool
  Bool≤ = the-preorder

Proset:Bool : Proset
Proset:Bool = Bool , Bool≤


-- Pairs
_⊗_ : ∀ {A B} (R : Rel A) (S : Rel B) -> Rel (A × B)
_⊗_ R S (a , x) (b , y) = R a b × S x y

IsPreorder:⊗ : ∀ {A B R S} -> IsPreorder {A} R -> IsPreorder {B} S
                -> IsPreorder (R ⊗ S)
reflexive (IsPreorder:⊗ P Q) = reflexive P , reflexive Q
transitive (IsPreorder:⊗ P Q) (aRb , xRy) (bRc , yRz) =
  transitive P aRb bRc , transitive Q xRy yRz

instance
  autoIsPreorder:⊗ : ∀{A B R S}
                     {{_ : IsPreorder {A} R}} {{_ : IsPreorder {B} S}}
                     -> IsPreorder (R ⊗ S)
  autoIsPreorder:⊗ = IsPreorder:⊗ auto auto

Preorder:× : ∀{A B} -> Preorder A -> Preorder B -> Preorder (A × B)
rel (Preorder:× P Q) = _≤_ ⊗ _≤_
isPreorder (Preorder:× P Q) = IsPreorder:⊗ is-preorder is-preorder

Proset:× : Proset -> Proset -> Proset
Proset:× (A , P) (B , Q) = (A × B) , Preorder:× P Q


-- TODO: Sums
_⊕_ : ∀ {A B} (R : Rel A) (S : Rel B) -> Rel (A ⊎ B)
_⊕_ R S (inj₁ x) (inj₁ y) = R x y
_⊕_ R S (inj₂ x) (inj₂ y) = S x y
_⊕_ R S _ _ = ⊥

IsPreorder:⊕ : ∀ {A B R S} -> IsPreorder {A} R -> IsPreorder {B} S
             -> IsPreorder (R ⊕ S)
reflexive (IsPreorder:⊕ P Q) = {!!}
transitive (IsPreorder:⊕ P Q) = {!!}

Proset:⊎ : Proset -> Proset -> Proset
Proset:⊎ (A , P) (B , Q) = (A ⊎ B) , {!!}


-- Ordering by projection
On : ∀{A B} (f : A -> B) (R : Rel B) -> Rel A
On f R x y = R (f x) (f y)

IsPreorder:On : ∀{A B R} f -> IsPreorder R -> IsPreorder (On {A}{B} f R)
reflexive (IsPreorder:On f P) = reflexive P
transitive (IsPreorder:On f P) = transitive P

Preorder:On : ∀{A B} (f : A -> B) -> Preorder B -> Preorder A
Preorder:On f P = Preorder: (On f _≤_) (IsPreorder:On f is-preorder)

Proset:On : ∀{A : Set} (P : Proset) (f : A -> carrier P) -> Proset
Proset:On {A} P f = A , Preorder:On f (preorder P)


-- Pointwise preorder on functions
Pointwise : ∀ {A B} (R : Rel B) -> Rel (A -> B)
Pointwise R f g = ∀ x -> R (f x) (g x)

IsPreorder:Pointwise : ∀{A B}{R : Rel B} (P : IsPreorder R)
                     -> IsPreorder (Pointwise {A} R)
reflexive (IsPreorder:Pointwise P) _ = reflexive P
transitive (IsPreorder:Pointwise P) aRb bRc x = transitive P (aRb x) (bRc x)

Preorder:Pointwise : ∀{A B} (P : Preorder B) -> Preorder (A -> B)
rel (Preorder:Pointwise P) = Pointwise _≤_
isPreorder (Preorder:Pointwise P) = IsPreorder:Pointwise is-preorder

-- Proset morphisms as a preorder
Respects : ∀ {A B} (R : Rel A) (Q : Rel B) (f : A -> B) -> Set
Respects R Q f = ∀ {a b} -> R a b -> Q (f a) (f b)

_⇒_ : (A B : Proset) -> Set
(A , P) ⇒ (B , Q) = Σ (A -> B) (Respects (rel P) (rel Q))

Proset:-> : Proset -> Proset -> Proset
Proset:-> P Q = P ⇒ Q , Preorder:On proj₁ (Preorder:Pointwise (preorder Q))


-- The "discrete" or "equivalence quotient" preorder
data Iso {A} (R : Rel A) : Rel A where
  iso : ∀{a b} -> R a b -> R b a -> Iso R a b

IsPreorder:Iso : ∀{A R} (P : IsPreorder {A} R) -> IsPreorder (Iso R)
reflexive (IsPreorder:Iso P) = iso (reflexive P) (reflexive P)
transitive (IsPreorder:Iso P) (iso aRb bRa) (iso bRc cRb) =
  iso (transitive P aRb bRc) (transitive P cRb bRa)

instance
  autoIsPreorder:Iso : ∀ {A R} {{_ : IsPreorder {A} R}} -> IsPreorder (Iso R)
  autoIsPreorder:Iso {{P}} = IsPreorder:Iso P

Preorder:Iso : ∀{A} (P : Preorder A) -> Preorder A
Preorder:Iso (Preorder: R is-pre) = Preorder: (Iso R) auto

Proset:Iso : Proset -> Proset
Proset:Iso (A , P) = A , Preorder:Iso P

  -- Disc≤ : ∀ {A} {{_ : Preorder A}} -> Preorder (Disc A)
  -- Disc≤ {A} {{P}} = Preorder: {Disc A} (disc≤ (rel P)) {!!}
  --   where instance x = isPreorder P


-- Reflexive transitive closure of a relation
data Path {A} (R : Rel A) : Rel A where
  lift : ∀{a b} -> R a b -> Path R a b
  refl : Reflexive (Path R)
  trans : Transitive (Path R)

instance
  IsPreorder:Path : ∀{A R} -> IsPreorder (Path {A} R)
  IsPreorder:Path = IsPreorder: refl trans


---------- Finite sets as a preorder ----------

-- This isn't actually "the" finite set preorder; rather, it is
-- preorder-isomorphic to it.

record Setof (A : Set) : Set where

Proset:Setof : Proset -> Proset
Proset:Setof = {!!}


---------- Types and their denotations ----------
data Type : Set where
  bool : Type
  set : (a : Type) -> Type
  _:->_ : (a b : Type) -> Type
  _:x_ : (a b : Type) -> Type
  _:+_ : (a b : Type) -> Type
  □ : (a : Type) -> Type

[[_]] : Type -> Proset
[[ bool ]] = Proset:Bool
[[ set a ]] = Proset:Setof [[ a ]]
[[ a :-> b ]] = Proset:-> [[ a ]] [[ b ]]
[[ a :x b ]] = Proset:× [[ a ]] [[ b ]]
[[ a :+ b ]] = Proset:⊎ [[ a ]] [[ b ]]
[[ □ a ]] = Proset:Iso [[ a ]]
