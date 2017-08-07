module TreeSet where

open import Prelude
open import Cat
open import Prosets
open import Monads

open import Data.Empty

data Tree (a : Set) : Set where
  empty : Tree a
  leaf : (x : a) -> Tree a
  node : (l r : Tree a) -> Tree a

infix 4 _∈[_]_
_∈[_]_ : ∀{a} -> a -> Rel a zero -> Tree a -> Set
x ∈[ R ] empty = ⊥
x ∈[ R ] leaf y = R x y
x ∈[ R ] node t u = x ∈[ R ] t ⊎ x ∈[ R ] u

trees : Proset -> Proset
trees C .Obj = Tree (Obj C)
trees C .Hom t u = ∀ {x} (p : x ∈[ Hom C ] t) -> x ∈[ Hom C ] u
trees C .ident = id
trees C .compo f g = f • g

tree-sums : (P : Proset) -> Sums (trees P)
_∨_ {{tree-sums C}} = node
in₁ {{tree-sums C}} = inj₁
in₂ {{tree-sums C}} = inj₂
[_,_] {{tree-sums C}} f g = [ f , g ]

instance
  tree-sums-auto : {{P : Proset}} -> Sums (trees P)
  tree-sums-auto {{P}} = tree-sums P
