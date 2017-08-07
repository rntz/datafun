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

Tree∈ : ∀{a} -> Rel a zero -> a -> Tree a -> Set
Tree∈ R x empty = ⊥
Tree∈ R x (leaf y) = R x y
Tree∈ R x (node t u) = Tree∈ R x t ⊎ Tree∈ R x u

infix 4 _∈[_]_
_∈[_]_ : ∀{a} -> a -> Rel a zero -> Tree a -> Set
x ∈[ R ] t = Tree∈ R x t

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
init {{tree-sums C}} = empty
init≤ {{tree-sums C}} ()

instance
  tree-sums-auto : {{P : Proset}} -> Sums (trees P)
  tree-sums-auto {{P}} = tree-sums P

-- Decidability of relations
decide-Tree∈ : ∀{a}{R : Rel a zero} -> Decidable R -> Decidable (Tree∈ R)
decide-Tree∈ test x empty = no ⊥-elim
decide-Tree∈ test x (leaf y) = test x y
decide-Tree∈ test x (node t u) with decide-Tree∈ test x t | decide-Tree∈ test x u
... | yes a | b = yes (inj₁ a)
... | a | yes b = yes (inj₂ b)
... | no ¬a | no ¬b = no [ ¬a , ¬b ]

module _ {P : Proset} (≤? : Decidable≤ P) where
  private instance pp = P
  trees-decidable : Decidable≤ (trees P)
  trees-decidable empty t = yes ⊥-elim
  trees-decidable (leaf x) t with decide-Tree∈ ≤? x t
  -- TODO: need downward-closure lemma!
  ... | yes p = yes λ {x'} x'≤x → {!!}
  ... | no ¬p = no  λ y → ¬p (y id)
  trees-decidable (node l r) t with dec× (trees-decidable l t) (trees-decidable r t)
  ... | yes (a , b) = yes λ { (inj₁ x) → a x; (inj₂ y) → b y }
  ... | no ¬p = no λ x → ¬p (in₁ • x , in₂ • x)
