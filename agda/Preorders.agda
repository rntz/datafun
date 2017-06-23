module Preorders where

open import Prelude
import Data.Product

-- -- from https://agda.readthedocs.io/en/latest/language/instance-arguments.html
-- -- They call this "it", I call it "auto"
-- auto : ∀ {i} {A : Set i} {{_ : A}} -> A
-- auto {{x}} = x

Rel : Set -> Set₁
Rel a = a -> a -> Set

Reflexive Transitive : ∀{A} -> Rel A -> Set
Reflexive {A} R = ∀{a} -> R a a
Transitive {A} R = ∀{a b c} -> R a b -> R b c -> R a c

Respects : ∀ {A B} (R : Rel A) (Q : Rel B) (f : A -> B) -> Set
Respects R Q f = ∀ {a b} -> R a b -> Q (f a) (f b)

record IsPreorder {A} (R : Rel A) : Set where
  constructor IsPreorder:
  field
    reflexive : Reflexive R
    transitive : Transitive R

open IsPreorder

refl : ∀{A R} {{p : IsPreorder {A} R}} {x} -> R x x
trans : ∀{A R} {{p : IsPreorder {A} R}} {x y z} -> R x y -> R y z -> R x z
refl {{p}} = reflexive p; trans {{p}} = transitive p

Preorder : Set -> Set₁
Preorder A = Σ (Rel A) IsPreorder

infix 4 _≤_
_≤_ : ∀ {a} {{_ : Preorder a}} -> Rel a
isPreorder : ∀ {a} {{_ : Preorder a}} -> IsPreorder _≤_
Monotone : ∀ {A B} {{_ : Preorder A}} {{_ : Preorder B}} (f : A -> B) -> Set
_≤_ {{P}} = proj₁ P; isPreorder {{P}} = proj₂ P; Monotone = Respects _≤_ _≤_

Proset : Set₁
Proset = Σ Set Preorder

carrier : Proset -> Set
preorder : (P : Proset) -> Preorder (carrier P)
carrier = proj₁; preorder = proj₂

related : (P : Proset) -> Rel (carrier P)
related (_ , R , _) = R

infixr 1 _⇒_
record _⇒_ (A B : Proset) : Set where
  constructor func
  field call : carrier A -> carrier B
  field mono : ∀{x y} -> related A x y -> related B (call x) (call y)

open _⇒_


-- Ordering by projection
On : ∀{A B} (f : A -> B) (R : Rel B) -> Rel A
On f R x y = R (f x) (f y)

IsPreorder:On : ∀{A B R} f -> IsPreorder R -> IsPreorder (On {A}{B} f R)
IsPreorder:On _ (IsPreorder: r t) = IsPreorder: r t


-- Pointwise preorder on functions
Pointwise : ∀ {A B} (R : Rel B) -> Rel (A -> B)
Pointwise R f g = ∀ x -> R (f x) (g x)

IsPreorder:Pointwise : ∀{A B}{R : Rel B} (P : IsPreorder R)
                     -> IsPreorder (Pointwise {A} R)
reflexive (IsPreorder:Pointwise P) _ = refl
transitive (IsPreorder:Pointwise P) aRb bRc x = trans (aRb x) (bRc x)

PointwiseΠ : ∀ A (B : A -> Set) (R : ∀ x -> Rel (B x)) -> Rel (∀ x -> B x)
PointwiseΠ _ _ R f g = ∀ x → R x (f x) (g x)

-- DEPENDENT FUNCTION TIME
IsPreorder:PointwiseΠ : ∀ {A B R}
                        -> (∀ x -> IsPreorder (R x))
                        -> IsPreorder (PointwiseΠ A B R)
reflexive (IsPreorder:PointwiseΠ P) x = reflexive (P x)
transitive (IsPreorder:PointwiseΠ P) fRg gRh x = transitive (P x) (fRg x) (gRh x)

Preorder:Π : ∀{A} {B : A -> Set}
           -> (∀ x -> Preorder (B x)) -> Preorder (∀ x -> B x)
Preorder:Π P = , IsPreorder:PointwiseΠ (proj₂ ∘ P)

Proset:Π : ∀ {A : Set} (B : A -> Proset) -> Proset
Proset:Π B = , Preorder:Π (proj₂ ∘ B)


-- Products and sums
_⊗_ : ∀ {A B} (R : Rel A) (S : Rel B) -> Rel (A × B)
_⊗_ R S (a , x) (b , y) = R a b × S x y

data _⊕_ {A B} (R : Rel A) (S : Rel B) : Rel (A ⊎ B) where
  rel₁ : ∀{x y} -> R x y -> (R ⊕ S) (inj₁ x) (inj₁ y)
  rel₂ : ∀{x y} -> S x y -> (R ⊕ S) (inj₂ x) (inj₂ y)

module _ {A B R S} (P : IsPreorder R) (Q : IsPreorder S) where
  IsPreorder:⊗ : IsPreorder {A × B} (R ⊗ S)
  reflexive IsPreorder:⊗ = refl , refl
  transitive IsPreorder:⊗ = Data.Product.zip trans trans

  IsPreorder:⊕ : IsPreorder {A ⊎ B} (R ⊕ S)
  reflexive  IsPreorder:⊕ {inj₁ _} = rel₁ refl
  reflexive  IsPreorder:⊕ {inj₂ _} = rel₂ refl
  transitive IsPreorder:⊕ (rel₁ x) (rel₁ y) = rel₁ (trans x y)
  transitive IsPreorder:⊕ (rel₂ x) (rel₂ y) = rel₂ (trans x y)


-- The "discrete" or "equivalence quotient" preorder.
-- TODO: maybe prove this is an equivalence relation?
Iso : ∀{A} -> Rel A -> Rel A
Iso R x y = R x y × R y x

IsPreorder:Iso : ∀{A R} (P : IsPreorder {A} R) -> IsPreorder (Iso R)
reflexive (IsPreorder:Iso P) = refl , refl
transitive (IsPreorder:Iso P) = Data.Product.zip trans (flip trans)


-- The booleans, ordered false < true.
data bool≤ : Rel Bool where
  bool-refl : Reflexive bool≤
  false<true : bool≤ false true

IsPreorder:bool≤ : IsPreorder bool≤
reflexive IsPreorder:bool≤ = bool-refl
transitive IsPreorder:bool≤ bool-refl y = y
transitive IsPreorder:bool≤ false<true bool-refl = false<true


-- Reflexive transitive closure of a relation
data Path {A} (R : Rel A) : Rel A where
  path-edge : ∀{a b} -> R a b -> Path R a b
  path-refl : Reflexive (Path R)
  path-trans : Transitive (Path R)

IsPreorder:Path : ∀{A R} -> IsPreorder (Path {A} R)
IsPreorder:Path = IsPreorder: path-refl path-trans


-- Boilerplate.
Preorder:× : ∀{A B} -> Preorder A -> Preorder B -> Preorder (A × B)
Preorder:⊎ : ∀{A B} -> Preorder A -> Preorder B -> Preorder (A ⊎ B)
Preorder:-> : ∀{A B} (P : Preorder B) -> Preorder (A -> B)
Preorder:On : ∀{A B} (f : A -> B) -> Preorder B -> Preorder A
Preorder:Iso : ∀{A} (P : Preorder A) -> Preorder A
Preorder:Path : ∀{A} -> Rel A -> Preorder A
Preorder:Bool : Preorder Bool

Preorder:× P Q = , IsPreorder:⊗ isPreorder isPreorder
Preorder:⊎ P Q = , IsPreorder:⊕ isPreorder isPreorder
Preorder:-> P = _ , IsPreorder:Pointwise isPreorder
Preorder:On f P = , IsPreorder:On f isPreorder
Preorder:Iso P = , IsPreorder:Iso isPreorder
Preorder:Path R = , IsPreorder:Path {R = R}
Preorder:Bool = , IsPreorder:bool≤

Proset:× Proset:⊎ Proset:⇒ : Proset -> Proset -> Proset
Proset:Iso : Proset -> Proset
Proset:Bool : Proset

Proset:× (_ , P) (_ , Q) = , Preorder:× P Q
Proset:⊎ (_ , P) (_ , Q) = , Preorder:⊎ P Q
Proset:⇒ P Q = (P ⇒ Q) , Preorder:On call (Preorder:-> (proj₂ Q))
Proset:Iso (_ , P) = , Preorder:Iso P
Proset:Bool = , Preorder:Bool


-- ---------- Finite sets as a preorder ----------

-- -- This isn't actually "the" finite set preorder; rather, it is
-- -- preorder-isomorphic to it.

-- record Setof (A : Set) : Set where

-- Proset:Setof : Proset -> Proset
-- Proset:Setof = {!!}


-- ---------- Types and their denotations ----------
-- data Type : Set where
--   bool : Type
--   set : (a : Type) -> Type
--   _:->_ : (a b : Type) -> Type
--   _:x_ : (a b : Type) -> Type
--   _:+_ : (a b : Type) -> Type
--   □ : (a : Type) -> Type

-- [[_]] : Type -> Proset
-- [[ bool ]] = Proset:Bool
-- [[ set a ]] = Proset:Setof [[ a ]]
-- [[ a :-> b ]] = Proset:-> [[ a ]] [[ b ]]
-- [[ a :x b ]] = Proset:× [[ a ]] [[ b ]]
-- [[ a :+ b ]] = Proset:⊎ [[ a ]] [[ b ]]
-- [[ □ a ]] = Proset:Iso [[ a ]]
