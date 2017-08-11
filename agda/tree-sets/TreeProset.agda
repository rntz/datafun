module TreeProset where

open import Prelude
open import Cat
open import Prosets

module _ (A : Proset) where
  private instance aa = A
  data Tree : Set where
    empty : Tree
    leaf : (x : Obj A) -> Tree
    node : (l r : Tree) -> Tree

  data Tree≤ : Rel Tree zero where
    empty≤ : ∀{t} -> Tree≤ empty t
    leaf≤ : ∀{x y} -> x ≤ y -> Tree≤ (leaf x) (leaf y)
    node≤ : ∀{l r t} -> Tree≤ l t -> Tree≤ r t -> Tree≤ (node l r) t
    split₁ : ∀{l r t} -> Tree≤ t l -> Tree≤ t (node l r)
    split₂ : ∀{l r t} -> Tree≤ t r -> Tree≤ t (node l r)

  -- Couldn't I just define this as:
  --     Tree∈ x t = Tree≤ (leaf x) t?
  -- well, not if I want Tree⊆ to be useful.
  Tree∈ : Obj A -> Tree -> Set
  Tree∈ x empty = ⊥
  Tree∈ x (leaf y) = x ≤ y
  Tree∈ x (node l r) = Tree∈ x l ⊎ Tree∈ x r

  down : ∀{a b} t -> Tree∈ b t -> a ≤ b -> Tree∈ a t
  down empty ()
  down (leaf c) b≤c a≤b = a≤b • b≤c
  down (node l r) (inj₁ p) = inj₁ ∘ down l p
  down (node l r) (inj₂ p) = inj₂ ∘ down r p

  Tree⊆ : Rel Tree zero
  Tree⊆ t u = ∀ {x} -> Tree∈ x t -> Tree∈ x u

  ≤→⊆ : ∀{t u} -> Tree≤ t u -> Tree⊆ t u
  ≤→⊆ empty≤ ()
  ≤→⊆ (leaf≤ x≤y) z≤x = z≤x • x≤y
  ≤→⊆ (node≤ t≤u t≤v) = [ ≤→⊆ t≤u , ≤→⊆ t≤v ]
  ≤→⊆ (split₁ x) = inj₁ ∘ ≤→⊆ x
  ≤→⊆ (split₂ x) = inj₂ ∘ ≤→⊆ x

  ⊆→≤ : ∀{t u} -> Tree⊆ t u -> Tree≤ t u
  ⊆→≤ {empty}    {u} f = empty≤
  ⊆→≤ {node l r} {u} f = node≤ (⊆→≤ (inj₁ • f)) (⊆→≤ (inj₂ • f))
  ⊆→≤ {leaf x} {empty} f = ⊥-elim (f id) -- zat is impossible, my friend.
  ⊆→≤ {leaf x} {leaf y} f = leaf≤ (f id)
  ⊆→≤ {leaf x} {node l r} f with f id
  ... | inj₁ y = split₁ (⊆→≤ (down l y))
  ... | inj₂ y = split₂ (⊆→≤ (down r y))

  instance
    trees : Proset
    Obj trees = Tree
    Hom trees = Tree≤
    -- hax.
    ident trees = ⊆→≤ id
    compo trees f g = ⊆→≤ (≤→⊆ f • ≤→⊆ g)

    tree-sums : Sums trees
    _∨_ {{tree-sums}} = node
    in₁ {{tree-sums}} = split₁ id
    in₂ {{tree-sums}} = split₂ id
    [_,_] {{tree-sums}} = node≤
    init {{tree-sums}} = empty
    init≤ {{tree-sums}} = empty≤

  -- Decidability
  module _ (≤? : Decidable≤ A) where
    trees-decidable : Decidable≤ trees
    trees-decidable empty u = yes empty≤
    trees-decidable (leaf x) empty = no λ {()}
    trees-decidable (leaf x) (leaf y) with ≤? x y
    ... | yes p = yes (leaf≤ p)
    ... | no ¬p = no λ { (leaf≤ x≤y) → ¬p x≤y }
    trees-decidable (leaf x) (node l r) with trees-decidable (leaf x) l | trees-decidable (leaf x) r
    ... | yes p | _   = yes (split₁ p)
    ... | _ | yes p   = yes (split₂ p)
    ... | no p | no q = no (λ { (split₁ z) → p z ; (split₂ z) → q z } )
    -- maybe using ⊆→≤ or reverse would help?
    trees-decidable (node l r) u with trees-decidable l u | trees-decidable r u
    ... | yes p | yes q = yes (node≤ p q)
    ... | no ¬p | _ = no λ { (node≤ x y) → ¬p x ; (split₁ x) → ¬p {!!} ; (split₂ x) → {!!} }
    ... | _ | no ¬p = no {!!}


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
