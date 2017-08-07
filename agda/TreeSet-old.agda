module TreeSet-old where

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


-- A type for the elements of a given tree.
Elem : ∀ {a} (t : Tree a) -> Set
Elem t = ∃ λ x -> x ∈ t

module Elem {a} {t : Tree a} (E : Elem t) where
  val : a;         val = proj₁ E
  proof : val ∈ t; proof = proj₂ E

-- Elem coerces Trees into Sets.
instance
  cast-tree->obj : ∀{a i} -> Cast i (Tree a) (Set zero)
  cast-tree->obj {a} = Cast: (Elem {a})


-- Trees form a preorder/category if their elements do.

-- t R* u iff: ∀ x ∈ t, ∃ y ∈ u st. x R y
-- is this saying ∃ a functor with a natural transformation from 1/id?
rel-tree : ∀{a i} (R : Rel a i) -> Rel (Tree a) i
-- rel-tree R t u = Σ[ f ∈ (Elem t -> Elem u) ]
--                  (∀ {x} -> R (proj₁ x) (proj₁ (f x)))
-- version 2: -- rel-tree R t u = ∀{x} -> x ∈ t -> ∃ λ y -> y ∈ u × R x y
-- version 3
rel-tree R t u = (x : Elem t) -> Σ[ y ∈ Elem u ] (R (Elem.val x) (Elem.val y))

trees : Proset -> Proset
trees A .Obj = Tree (Obj A)
trees A .Hom = rel-tree (Hom A)
-- -- version 1
-- trees A .ident = id , ident A
-- trees A .compo (f , f≤) (g , g≤) = f • g , compo A f≤ g≤
-- version 3
trees A .ident x = x , ident A
trees A .compo f g x with f x
trees A .compo f g x | y , x≤y with g y
trees A .compo f g x | y , x≤y | z , y≤z = z , compo A x≤y y≤z


-- instance
--   trees-auto : ∀{a} -> Proset
--   trees-auto {a} = trees a

-- node forms coproducts on trees under rel-tree.
tree-sums : Proset -> Sums zero zero
tree-sums A .cat = trees A
_∨_ {{tree-sums A}} = node
-- in₁ {{tree-sums A}} .proj₁ (x , p) = , ∈-node (inj₁ p)
-- in₁ {{tree-sums A}} .proj₂ = ident A
-- in₂ {{tree-sums A}} = {!!} -- in₂ • ∈-node
-- [_,_] {{tree-sums A}} f g = {!!} -- [ f , g ] p
in₁ {{tree-sums A}} (_ , p) = (, ∈-node (inj₁ p)) , ident A
in₂ {{tree-sums A}} (_ , p) = (, ∈-node (inj₂ p)) , ident A -- in₂ • ∈-node
[_,_] {{tree-sums A}} f g = {!!} -- [ f , g ] p
