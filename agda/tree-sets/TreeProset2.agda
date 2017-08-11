module TreeProset2 where

open import Prelude
open import Cat
open import Prosets

module _ (A : Proset) where
  private instance aa = A
  data Tree : Set where
    empty : Tree
    leaf : (x : Obj A) -> Tree
    node : (l r : Tree) -> Tree

  data Tree∈ (x : Obj A) : Tree -> Set where
    in-leaf : ∀{y} -> x ≤ y -> Tree∈ x (leaf y)
    in-node : ∀{l r} -> Tree∈ x l ⊎ Tree∈ x r -> Tree∈ x (node l r)

  Tree≤ : Rel Tree zero
  Tree≤ empty t = ⊤
  Tree≤ (leaf x) t = Tree∈ x t
  Tree≤ (node l r) t = Tree≤ l t × Tree≤ r t

  Tree⊆ : Rel Tree zero
  Tree⊆ t u = ∀ {x} -> Tree∈ x t -> Tree∈ x u

  split : ∀{t l r} -> Tree≤ t l ⊎ Tree≤ t r -> Tree≤ t (node l r)
  split {empty} _ = tt
  split {leaf x} p = in-node p
  split {node t u} (inj₁ (p , q)) = split (inj₁ p) , split (inj₁ q)
  split {node t u} (inj₂ (p , q)) = split (inj₂ p) , split (inj₂ q)

  down : ∀{a b t} -> a ≤ b -> Tree∈ b t -> Tree∈ a t
  down a≤b (in-leaf b≤c) = in-leaf (a≤b • b≤c)
  down a≤b (in-node p) = in-node (∨-map (down a≤b) (down a≤b) p)

  chase : ∀ t {u} -> Tree≤ t u -> Tree⊆ t u
  chase empty tt ()
  chase (leaf _) x∈u (in-leaf x≤y) = down x≤y x∈u
  chase (node l r) (l≤u , r≤u) (in-node p) = [ chase l l≤u , chase r r≤u ] p

  instance
    trees : Proset
    Obj trees = Tree
    Hom trees = Tree≤
    ident trees {empty} = tt
    ident trees {leaf x} = in-leaf (ident A)
    ident trees {node l r} = split (inj₁ id) , split (inj₂ id)
    compo trees {empty}    {b} _ _ = tt
    compo trees {leaf _}   {b} x y = chase b y x
    compo trees {node _ _} {b} (l , r) x = l • x , r • x

    tree-sums : Sums trees
    _∨_ {{tree-sums}} = node
    in₁ {{tree-sums}} = split (inj₁ id)
    in₂ {{tree-sums}} = split (inj₂ id)
    [_,_] {{tree-sums}} = _,_
    init {{tree-sums}} = empty
    init≤ {{tree-sums}} = tt

  -- Decidability
  module _ (≤? : Decidable≤ A) where
    decide-Tree∈ : ∀ x t -> Dec (Tree∈ x t)
    decide-Tree∈ x empty = no λ {()}
    decide-Tree∈ x (leaf y) with ≤? x y
    ... | yes x≤y = yes (in-leaf x≤y)
    ... | no  x≰y = no  λ { (in-leaf x≤y) → x≰y x≤y }
    decide-Tree∈ x (node t u) with decide-Tree∈ x t | decide-Tree∈ x u
    ... | yes p | _ = yes (in-node (inj₁ p))
    ... | _ | yes p = yes (in-node (inj₂ p))
    ... | no p | no q = no λ { (in-node y) → [ p , q ] y }

    trees-decidable : Decidable≤ trees
    trees-decidable empty u = yes tt
    trees-decidable (leaf x) u = decide-Tree∈ x u
    trees-decidable (node l r) u = dec× (trees-decidable l u) (trees-decidable r u)


-- Functoriality
Trees : prosets ≤ prosets
ap Trees = trees
map Trees F .ap empty = empty
map Trees F .ap (leaf x) = leaf (ap F x)
map Trees F .ap (node t u) = node (map Trees F .ap t) (map Trees F .ap u)
map Trees F .map {empty} tt = tt
map Trees F .map {leaf _} (in-leaf x≤y) = in-leaf (map F x≤y)
map Trees F .map {leaf x} (in-node (inj₁ y)) = in-node (inj₁ (map Trees F .map y))
map Trees F .map {leaf x} (in-node (inj₂ y)) = in-node (inj₂ (map Trees F .map y))
map Trees F .map {node a₁ a₂} (x , y) = map Trees F .map x , map Trees F .map y
