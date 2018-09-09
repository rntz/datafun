-- 2018-09-06: I don't think this approach is worth it.
module TreeSet2 where

open import Prelude
open import Cat
open import Decidability

data Tree (a : Set) : Set where
  empty : Tree a
  leaf : (x : a) -> Tree a
  node : (T U : Tree a) -> Tree a

module Trees (C : Proset) where
  private instance cc = C

  _∈_ : Obj C → Tree (Obj C) → Set
  a ∈ empty = ∅
  a ∈ leaf b = a ≤ b
  a ∈ node T U = a ∈ T ⊎ a ∈ U

  ≤∈ : ∀{a b} → a ≤ b → ∀ T → b ∈ T → a ∈ T
  ≤∈ a≤b empty ()
  ≤∈ a≤b (leaf c) b≤c = a≤b • b≤c
  ≤∈ a≤b (node T U) = map∨ (≤∈ a≤b T) (≤∈ a≤b U)

  _⊑_ : Rel (Tree (Obj C)) zero
  empty ⊑ Y = Unit
  leaf x ⊑ Y = x ∈ Y
  node X₁ X₂ ⊑ Y = X₁ ⊑ Y × X₂ ⊑ Y

  ∈≤ : ∀{x} T → x ∈ T → ∀ U → T ⊑ U → x ∈ U
  ∈≤ empty ()
  ∈≤ (leaf b) a≤b U b∈U = ≤∈ a≤b U b∈U
  ∈≤ (node T₁ T₂) (inj₁ x) U (T₁≤U , T₂≤U) = ∈≤ T₁ x U T₁≤U
  ∈≤ (node T₁ T₂) (inj₂ y) U (T₁≤U , T₂≤U) = ∈≤ T₂ y U T₂≤U

  split₁ : ∀ T {U V} → T ⊑ U → T ⊑ node U V
  split₁ empty tt = tt
  split₁ (leaf x) = inj₁
  split₁ (node T₁ T₂) (T₁≤U , T₂≤U) = split₁ T₁ T₁≤U , split₁ T₂ T₂≤U

  split₂ : ∀ T {U V} → T ⊑ V → T ⊑ node U V
  split₂ empty tt = tt
  split₂ (leaf x) = inj₂
  split₂ (node T₁ T₂) (T₁≤U , T₂≤U) = split₂ T₁ T₁≤U , split₂ T₂ T₂≤U

  trees : Proset
  private instance trees-auto : Proset; trees-auto = trees
  Obj trees = Tree (Obj C)
  Hom trees = _⊑_
  ident trees {empty} = tt
  ident trees {leaf x} = ident C
  ident trees {node T U} = split₁ T (id {a = T}) , split₂ U (id {a = U}) 
  compo trees {empty} tt U≤V = tt
  compo trees {leaf x} {U} {V} x∈U U≤V = ∈≤ U x∈U V U≤V
  compo trees {node T₁ T₂} {U} {V} (T₁≤U , T₂≤U) U≤V =
    ( compo trees {T₁}{U}{V} T₁≤U U≤V , compo trees {T₂}{U}{V} T₂≤U U≤V )

  instance
    tree-sums : Sums trees
    bottom tree-sums = empty , tt
    lub tree-sums a b = node a b / split₁ a (id {a = a}) / split₂ b (id {a = b}) / _,_

  -- Semilattice join / categorical sum lifted over trees, ⋁
  module _ (Sums : Sums C) where
    private instance s = Sums
    tree-⋁ : trees ⇒ C
    ap tree-⋁ empty = ⊥
    ap tree-⋁ (leaf x) = x
    ap tree-⋁ (node l r) = ap tree-⋁ l ∨ ap tree-⋁ r
    map tree-⋁ {empty} {U} tt = Sums.⊥≤ s
    map tree-⋁ {leaf x} {U} x∈U = {!x∈U!}
    map tree-⋁ {node T T₁} {U} T≤U = {!!}  
