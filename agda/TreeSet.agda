module TreeSet where

open import Prelude
open import Cat
open import Prosets
open import Monads

data Tree (a : Set) : Set where
  empty : Tree a
  leaf : (x : a) -> Tree a
  node : (l r : Tree a) -> Tree a

data _∈_ {a : Set} (x : a) : Tree a -> Set where
  ∈-leaf : x ∈ leaf x
  ∈-node : ∀{l r} -> (p : x ∈ l ⊎ x ∈ r) -> x ∈ node l r

infix 4 _⊑_
_⊑_ : ∀ {a} (t u : Tree a) -> Set
t ⊑ u = ∀{x} -> x ∈ t -> x ∈ u

trees : ∀ a -> Proset
trees a .Obj = Tree a
trees a .Hom = _⊑_
trees a .ident p = p
trees a .compo f g p = g (f p)

instance
  trees-auto : ∀{a} -> Proset
  trees-auto {a} = trees a

  -- node forms coproducts on trees under ⊑.
  tree-sums : ∀{a} -> Sums _ _
  tree-sums {a} .Sums.C = trees a
  _∨_ {{tree-sums}} = node
  in₁ {{tree-sums}} = in₁ • ∈-node
  in₂ {{tree-sums}} = in₂ • ∈-node
  [_,_] {{tree-sums}} f g (∈-node p) = [ f , g ] p
