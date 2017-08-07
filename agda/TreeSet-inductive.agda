module TreeSet-inductive where

open import Prelude
open import Cat
open import Prosets
open import Monads

data Tree (a : Set) : Set where
  empty : Tree a
  leaf : (x : a) -> Tree a
  node : (l r : Tree a) -> Tree a

module _ (C : Proset) where
  private a = Obj C; instance cc = C
  data _⊑_ : Rel (Tree a) zero where
    empty⊑ : ∀{t} -> empty ⊑ t
    leaf⊑ : ∀{x y} -> x ≤ y -> leaf x ⊑ leaf y
    node⊑-r : ∀{t l r} -> t ⊑ l ⊎ t ⊑ r -> t ⊑ node l r
    node⊑-l : ∀{l r t} -> l ⊑ t × r ⊑ t -> node l r ⊑ t

  -- holy shit.
  instance
    trees : Proset
    Obj trees = Tree a
    Hom trees = _⊑_
    ident trees {empty} = empty⊑
    ident trees {leaf x} = leaf⊑ id
    ident trees {node l r} = node⊑-l (node⊑-r (inj₁ id) , node⊑-r (inj₂ id))
    compo trees empty⊑ _ = empty⊑
    compo trees (leaf⊑ x) (leaf⊑ y) = leaf⊑ (x • y)
    compo trees x (node⊑-r (inj₁ y)) = node⊑-r (inj₁ (x • y))
    compo trees x (node⊑-r (inj₂ y)) = node⊑-r (inj₂ (x • y))
    compo trees (node⊑-l (l , r)) x = node⊑-l (l • x , r • x)
    compo trees (node⊑-r (inj₁ x)) (node⊑-l (y , z)) = x • y
    compo trees (node⊑-r (inj₂ x)) (node⊑-l (y , z)) = x • z

  tree-sums : Sums _ _
  cat tree-sums = trees
  _∨_ {{tree-sums}} = node
  in₁ {{tree-sums}} = node⊑-r (inj₁ id)
  in₂ {{tree-sums}} = node⊑-r (inj₂ id)
  [_,_] {{tree-sums}} f g = node⊑-l (f , g)
