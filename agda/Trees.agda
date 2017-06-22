module Trees where

open import Level renaming (zero to lzero; suc to lsuc)

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open import Data.Product
open import Data.Unit

open import Preorders

-- Preorder on trees representing finite sets.
data Tree (a : Set) : Set where
  empty : Tree a
  single : a -> Tree a
  _∪_ : (x y : Tree a) -> Tree a

module _ {A : Set} where
  -- The most obvious element-of relationship.
  infix 4 _∈_
  data _∈_ (x : A) : Tree A -> Set where
    here : x ∈ single x
    left : ∀{X Y} -> x ∈ X -> x ∈ X ∪ Y
    rite : ∀{X Y} -> x ∈ Y -> x ∈ X ∪ Y

-- Given an element-of relation, we can form a subset relation.
module ⊆-from-∈ (_∈_ : {A : Set} -> A -> Tree A -> Set) {A : Set} where
  infix 4 _⊆_
  _⊆_ : (X Y : Tree A) -> Set
  X ⊆ Y = ∀ {x} -> x ∈ X -> x ∈ Y

  _≈_ : (X Y : Tree A) -> Set
  X ≈ Y = X ⊆ Y × Y ⊆ X

  -- ⊆ is a preorder (thin category)
  ⊆refl : ∀{X} -> X ⊆ X
  ⊆trans : ∀{X Y Z} -> X ⊆ Y -> Y ⊆ Z -> X ⊆ Z
  ⊆refl x∈X = x∈X
  ⊆trans X⊆Y Y⊆Z x∈X = Y⊆Z (X⊆Y x∈X)

  -- structures on ⊆ and ≈
  open IsPreorder
  ⊆IsPreorder : IsPreorder _⊆_
  reflexive ⊆IsPreorder = ⊆refl
  transitive ⊆IsPreorder = ⊆trans

  ⊆Preorder : Preorder (Tree A)
  ⊆Preorder = _⊆_ , ⊆IsPreorder

module _ {A : Set} where
  open ⊆-from-∈ _∈_ {A} public

  -- empty is least (initial)
  ⊆empty : ∀ {X} -> empty ⊆ X
  ⊆empty ()

  -- union is coproduct
  ⊆∪l : ∀ {X Y} -> X ⊆ X ∪ Y
  ⊆∪r : ∀ {X Y} -> Y ⊆ X ∪ Y
  ⊆∪[_,_] : ∀ {X Y Z} -> X ⊆ Z -> Y ⊆ Z -> X ∪ Y ⊆ Z

  ⊆∪l = left
  ⊆∪r = rite
  ⊆∪[ X⊆Z , Y⊆Z ] (left x∈X) = X⊆Z x∈X
  ⊆∪[ X⊆Z , Y⊆Z ] (rite x∈Y) = Y⊆Z x∈Y

TreeSet : Set -> Proset
TreeSet A = Tree A , ⊆Preorder
