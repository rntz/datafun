module TreeSet where

open import Prelude
open import Cat
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
    ≤node : ∀{t u v} → t ⊑ u ⊎ t ⊑ v → t ⊑ node u v

  pattern split₁ p = ≤node (inj₁ p)
  pattern split₂ p = ≤node (inj₂ p)

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
  compo trees (leaf≤ x) (leaf≤ y) = leaf≤ (x ∙ y)
  compo trees x (≤node p) = ≤node (map∨ (x ∙_) (x ∙_) p)
  compo trees (node≤ l r) x = node≤ (l ∙ x) (r ∙ x)
  compo trees (≤node p) (node≤ y z) = [ _∙ y , _∙ z ] p

  instance
    tree-sums : Sums trees
    bottom tree-sums = empty , empty≤
    lub tree-sums a b = node a b / split₁ id / split₂ id / node≤

  -- Semilattice join / categorical sum lifted over trees, ⋁
  module _ (Sums : Sums C) where
    private instance s = Sums
    tree-⋁ : trees ⇒ C
    ap tree-⋁ empty = ⊥
    ap tree-⋁ (leaf x) = x
    ap tree-⋁ (node l r) = ap tree-⋁ l ∨ ap tree-⋁ r
    map tree-⋁ empty≤ = ⊥≤
    map tree-⋁ (leaf≤ x≤y) = x≤y
    map tree-⋁ (node≤ t≤u t≤v) = [ map tree-⋁ t≤u , map tree-⋁ t≤v ]
    map tree-⋁ (split₁ t≤u) = map tree-⋁ t≤u ∙ in₁
    map tree-⋁ (split₂ t≤u) = map tree-⋁ t≤u ∙ in₂

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
    ... | no _ | yes p = yes (split₂ p)
    ... | no ¬p | no ¬q = no λ { (≤node pq) → [ ¬p , ¬q ] pq }
    tree≤? (node l r) y with tree≤? l y | tree≤? r y
    ... | yes p | yes q = yes (node≤ p q)
    ... | no ¬p | _ = no (unsplit ∙ π₁ ∙ ¬p)
    ... | yes _ | no ¬q = no (unsplit ∙ π₂ ∙ ¬q)

open Trees public renaming (_⊑_ to Tree≤) hiding (unsplit)

_∈_ : {{C : Proset}} → Obj C → Tree (Obj C) → Set
_∈_ {{C}} a X = Tree≤ C (leaf a) X

-- -- TODO: Do I really need this, rather than just saying (a ∈ X = leaf a ≤ X)?
-- module _ {{C : Proset}} where
--   _∈_ : Obj C → Tree (Obj C) → Set
--   a ∈ empty = ∅
--   a ∈ leaf b = a ≤ b
--   a ∈ node T U = a ∈ T ⊎ a ∈ U

--   ∈→≤ : ∀{T a} → a ∈ T → leaf a ≤ T
--   ∈→≤ {empty} ()
--   ∈→≤ {leaf b} a≤b = leaf≤ a≤b
--   ∈→≤ {node T U} = ≤node ∘ map∨ ∈→≤ ∈→≤

--   ≤→∈ : ∀{a T} → leaf a ≤ T → a ∈ T
--   ≤→∈ (leaf≤ x) = x
--   ≤→∈ (≤node p) = map∨ ≤→∈ ≤→∈ p

--   Tree∈ : Fun (op C ∧ trees C) sets
--   ap Tree∈ (a , T) = a ∈ T
--   map Tree∈ {b , T} {a , U} (a≤b , T≤U) a∈T = ≤→∈ (leaf≤ a≤b ∙ ∈→≤ a∈T ∙ T≤U)


-- Trees is a functor.
tree-map : ∀{A B} → A ⇒ B → trees A ⇒ trees B
tree-map F .ap empty = empty
tree-map F .ap (leaf x) = leaf (ap F x)
tree-map F .ap (node T U) = node (tree-map F .ap T) (tree-map F .ap U)
tree-map F .map empty≤ = empty≤
tree-map F .map (leaf≤ x) = leaf≤ (map F x)
tree-map F .map (node≤ x y) = node≤ (tree-map F .map x) (tree-map F .map y)
tree-map F .map (≤node p) = ≤node (map∨ (tree-map F .map) (tree-map F .map) p)

Trees : cats ≤ cats
ap Trees = trees
map Trees = tree-map

-- I think this is 2-functoriality? Not sure.
Tree-map : ∀{A B} -> A ⇨ B ⇒ trees A ⇨ trees B
ap Tree-map = tree-map
map (Tree-map {A} {B}) {f} {g} f≤g {empty} = empty≤
map (Tree-map {A} {B}) {f} {g} f≤g {leaf x} = leaf≤ f≤g
map (Tree-map {A} {B}) {f} {g} f≤g {node l r} =
  node≤ (split₁ (Tree-map {A} .map f≤g {l}))
        (split₂ (Tree-map {A} .map f≤g {r}))


-- Trees is a monad. TODO: used anywhere?
tree-join : ∀{A} → Tree (Tree A) → Tree A
tree-join empty = empty
tree-join (leaf X) = X
tree-join (node X Y) = node (tree-join X) (tree-join Y)

Tree-join : ∀{{C}} → trees (trees C) ⇒ trees C
Tree-join .ap = tree-join
Tree-join .map empty≤ = empty≤
Tree-join .map (leaf≤ x≤y) = x≤y
Tree-join .map (node≤ p q) = node≤ (map Tree-join p) (map Tree-join q)
Tree-join .map (≤node x) = ≤node (map∨ (map Tree-join) (map Tree-join) x)

open import Monads
instance
  Tree-monad : Monad Trees
  Monad.pure Tree-monad = fun leaf≤
  Monad.join Tree-monad = Tree-join
