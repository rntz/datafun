module TreeSet3 where

open import Prelude
open import Cat
open import Decidability

data Tree (a : Set) : Set where
  empty : Tree a
  leaf : (x : a) -> Tree a
  node : (T U : Tree a) -> Tree a

module _ {{C : Proset}} where
  data _∈_ (a : Obj C) : Tree (Obj C) → Set where
    leaf : ∀{b} → a ≤ b → a ∈ leaf b
    node : ∀{T U} → a ∈ T ⊎ a ∈ U → a ∈ node T U

module Trees (C : Proset) where
  private instance cc = C

  pattern node₁ p = node (inj₁ p)
  pattern node₂ p = node (inj₂ p)

  ≤∈ : ∀{a b T} → a ≤ b → b ∈ T → a ∈ T
  ≤∈ a≤b (leaf b≤c) = leaf (a≤b • b≤c)
  ≤∈ a≤b (node x) = node (map∨ (≤∈ a≤b) (≤∈ a≤b) x)

  _⊑_ : Rel (Tree (Obj C)) zero
  T ⊑ U = ∀{x y} → x ≤ y → y ∈ T → x ∈ U

  ∈≤ : ∀{x T U} → x ∈ T → T ⊑ U → x ∈ U
  ∈≤ x ρ = ρ id x

  trees : Proset
  Obj trees = Tree (Obj C)
  Hom trees = _⊑_
  ident trees = ≤∈
  compo trees F G x≤y y∈X = G id (F x≤y y∈X)

  private instance trees-auto : Proset; trees-auto = trees

  instance
    tree-sums : Sums trees
    bottom tree-sums = empty , λ { _ () }
    lub tree-sums a b = node a b
      / (λ x≤y y → node₁ (≤∈ x≤y y)) / (λ x≤y y → node₂ (≤∈ x≤y y))
      / λ { X≤C Y≤C x≤y (node p) → [ X≤C x≤y , Y≤C x≤y ] p }

  -- Semilattice join / categorical sum lifted over trees, ⋁
  module _ (Sums : Sums C) where
    private instance s = Sums
    tree-⋁ : trees ⇒ C
    ap tree-⋁ empty = ⊥
    ap tree-⋁ (leaf x) = x
    ap tree-⋁ (node l r) = ap tree-⋁ l ∨ ap tree-⋁ r
    map tree-⋁ {X}{Y} ρ = {!!}

open Trees public renaming (_⊑_ to Tree≤)


-- Functoriality
module _ {A B} (F : A ⇒ B) where
  private instance -A = A; -B = B
  tree-map : trees A ⇒ trees B
  tree-map .ap empty = empty
  tree-map .ap (leaf x) = leaf (ap F x)
  tree-map .ap (node X Y) = node (tree-map .ap X) (tree-map .ap Y)
  tree-map .map {empty} ρ x≤y ()
  tree-map .map {leaf a} ρ x≤y y∈FX with ρ id (leaf id)
  tree-map .map ρ x≤y (leaf y≤Fa) | leaf a≤b = leaf (x≤y • y≤Fa • map F a≤b)
  tree-map .map {leaf a} ρ x≤y (leaf y≤Fa) | node₁ p = node₁ {!!}
  tree-map .map {leaf a} ρ x≤y (leaf y≤Fa) | node₂ p = {!!}
  tree-map .map {node X X₁} {Y} ρ x≤y y∈FX = {!!}
