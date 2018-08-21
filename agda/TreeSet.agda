module TreeSet where

open import Prelude
open import Cat
open import Prosets
open import Decidability

data Tree (a : Set) : Set where
  empty : Tree a
  leaf : (x : a) -> Tree a
  node : (l r : Tree a) -> Tree a

module Trees (C : Proset) where
  private instance cc = C
  data _⊑_ : Rel (Tree (Obj C)) zero where
    empty≤ : ∀{t} -> empty ⊑ t
    leaf≤ : ∀{x y} -> x ≤ y -> leaf x ⊑ leaf y
    node≤ : ∀{l r t} -> l ⊑ t -> r ⊑ t -> node l r ⊑ t
    split₁ : ∀{t l r} -> t ⊑ l -> t ⊑ node l r
    split₂ : ∀{t l r} -> t ⊑ r -> t ⊑ node l r

  unsplit : ∀{l r t} -> node l r ⊑ t -> l ⊑ t × r ⊑ t
  unsplit (node≤ l r) = l , r
  unsplit (split₁ p) = map∧ split₁ split₁ (unsplit p)
  unsplit (split₂ p) = map∧ split₂ split₂ (unsplit p)

  trees : Proset
  private instance trees-auto : Proset; trees-auto = trees
  Obj trees = Tree (Obj C)
  Hom trees = _⊑_
  ident trees {empty} = empty≤
  ident trees {leaf x} = leaf≤ id
  ident trees {node l r} = node≤ (split₁ id) (split₂ id)
  compo trees empty≤ _ = empty≤
  compo trees (leaf≤ x) (leaf≤ y) = leaf≤ (x • y)
  compo trees x (split₁ y) = split₁ (x • y)
  compo trees x (split₂ y) = split₂ (x • y)
  compo trees (node≤ l r) x = node≤ (l • x) (r • x)
  compo trees (split₁ x) (node≤ y z) = x • y
  compo trees (split₂ x) (node≤ y z) = x • z

  instance
    -- tree-sums : Sums trees
    -- _∨_ {{tree-sums}} = node
    -- in₁ {{tree-sums}} = split₁ id
    -- in₂ {{tree-sums}} = split₂ id
    -- [_,_] {{tree-sums}} f g = node≤ f g
    -- bot {{tree-sums}} = empty
    -- bot≤ {{tree-sums}} = empty≤

    tree-joins : Joins trees
    Joins.join tree-joins a b = node a b / split₁ id / split₂ id / node≤
    Joins.bottom tree-joins = empty , empty≤

  -- This is used in Changes.agda. TODO: avoid need for it?
  tree-sums = joins→sums trees tree-joins

  -- Semilattice join / categorical sum lifted over trees, ⋁
  module _ (Sums : Sums C) where
    private instance s = Sums
    tree-⋁ : trees ⇒ C
    ap tree-⋁ empty = bot
    ap tree-⋁ (leaf x) = x
    ap tree-⋁ (node l r) = ap tree-⋁ l ∨ ap tree-⋁ r
    map tree-⋁ empty≤ = bot≤
    map tree-⋁ (leaf≤ x≤y) = x≤y
    map tree-⋁ (node≤ t≤u t≤v) = [ map tree-⋁ t≤u , map tree-⋁ t≤v ]
    map tree-⋁ (split₁ t≤u) = map tree-⋁ t≤u • in₁
    map tree-⋁ (split₂ t≤u) = map tree-⋁ t≤u • in₂

  -- Decidability
  module _ (≤? : Decidable≤ C) where
    tree≤? : Decidable≤ trees
    tree≤? empty y = yes empty≤
    tree≤? (leaf x) empty = no λ {()}
    tree≤? (leaf x) (leaf y) with ≤? x y
    ... | yes x≤y = yes (leaf≤ x≤y)
    ... | no ¬x≤y = no λ { (leaf≤ x≤y) → ¬x≤y x≤y }
    tree≤? (leaf x) (node l r) with tree≤? (leaf x) l | tree≤? (leaf x) r
    ... | yes p | _ = yes (split₁ p)
    ... | _ | yes p = yes (split₂ p)
    ... | no ¬p | no ¬q = no λ { (split₁ p) → ¬p p ; (split₂ q) → ¬q q }
    tree≤? (node l r) y with tree≤? l y | tree≤? r y
    ... | yes p | yes q = yes (node≤ p q)
    ... | no ¬p | _ = no (unsplit • π₁ • ¬p)
    ... | _ | no ¬q = no (unsplit • π₂ • ¬q)

open Trees public renaming (_⊑_ to Tree≤) hiding (unsplit)


-- Functoriality
Trees : prosets ≤ prosets
ap Trees = trees
map Trees F .ap empty = empty
map Trees F .ap (leaf x) = leaf (ap F x)
map Trees F .ap (node t u) = node (map Trees F .ap t) (map Trees F .ap u)
map Trees F .map empty≤ = empty≤
map Trees F .map (leaf≤ x) = leaf≤ (map F x)
map Trees F .map (node≤ x y) = node≤ (map Trees F .map x) (map Trees F .map y)
map Trees F .map (split₁ x) = split₁ (map Trees F .map x)
map Trees F .map (split₂ x) = split₂ (map Trees F .map x)

-- TODO: Is this... 2-Functoriality or something? I'm not sure.
Tree-map : ∀{A B} -> A ⇨ B ⇒ trees A ⇨ trees B
ap Tree-map = map Trees
-- this proof looks suspiciously like the cases for `map Trees F .map`, above.
map Tree-map f≤g empty≤ = empty≤
map Tree-map f≤g (leaf≤ x≤y) = leaf≤ (f≤g x≤y)
map Tree-map f≤g (node≤ t≤u t≤v) = node≤ (map Tree-map f≤g t≤u) (map Tree-map f≤g t≤v)
map Tree-map f≤g (split₁ t≤u) = split₁ (map Tree-map f≤g t≤u)
map Tree-map f≤g (split₂ t≤u) = split₂ (map Tree-map f≤g t≤u)
