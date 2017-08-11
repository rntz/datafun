module TreeSet where

open import Prelude
open import Cat
open import Prosets

-- Maybe Tree should just take a Proset instead of a set.
-- would that help?
data Tree (a : Set) : Set where
  empty : Tree a
  leaf : (x : a) -> Tree a
  node : (l r : Tree a) -> Tree a

tree-map : ∀{a b} -> (a -> b) -> Tree a -> Tree b
tree-map f empty = empty
tree-map f (leaf x) = leaf (f x)
tree-map f (node l r) = node (tree-map f l) (tree-map f r)

-- Isn't this just interpreting Trees into Contexts?
-- can we see this as a functor on some category?
infix 4 _∈[_]_
_∈[_]_ : ∀{a} -> a -> Rel a zero -> Tree a -> Set
x ∈[ R ] empty = ⊥
x ∈[ R ] leaf y = R x y
x ∈[ R ] node l r = x ∈[ R ] l ⊎ x ∈[ R ] r

Tree∈ : ∀{a} -> Rel a zero -> a -> Tree a -> Set
Tree∈ R x t = x ∈[ R ] t

module _ (C : Proset) where
  private instance cc = C
  trees : Proset
  Obj trees = Tree (Obj C)
  Hom trees t u = ∀ {x} (p : x ∈[ Hom C ] t) -> x ∈[ Hom C ] u
  ident trees = id
  compo trees f g = f • g

  down : ∀{x y : Obj C} t -> y ∈[ _≤_ ] t -> x ≤ y -> x ∈[ _≤_ ] t
  down empty ()
  down (leaf z) y≤z x≤y = x≤y • y≤z
  down (node l r) (inj₁ z) x≤y = inj₁ (down l z x≤y)
  down (node l r) (inj₂ z) x≤y = inj₂ (down r z x≤y)

-- TODO FIXME: RENAME & CLEAN UP THIS CODE
∈/tree-map : ∀{R Q} (F : R ⇒ Q) -> ∀{x} t
           -> x ∈[ Hom R ] t -> ap F x ∈[ Hom Q ] (tree-map (ap F) t)
∈/tree-map F empty ()
∈/tree-map F (leaf y) = map F
∈/tree-map F (node l r) = ∨-map (∈/tree-map F l) (∈/tree-map F r)

Trees : prosets ≤ prosets
ap Trees = trees
-- where does this use the fact that F is monotone?! oh, when it calls ∈/tree-map.
map Trees F .ap = tree-map (ap F)
map Trees F .map {empty} t≤u ()
map Trees {A}{B} F .map {leaf y}   {u} t≤u =
   down B (tree-map (ap F) u) (∈/tree-map F u (t≤u (ident A)))
map Trees F .map {node l r} {u} t≤u =
  [ map Trees F .map {l} {u} (inj₁ • t≤u)
  , map Trees F .map {r} {u} (inj₂ • t≤u) ]

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

module _ (P : Proset) (≤? : Decidable≤ P) where
  private instance pp = P

  trees-decidable : Decidable≤ (trees P)
  trees-decidable empty t = yes λ {()}
  trees-decidable (leaf x) t with decide-Tree∈ ≤? x t
  ... | yes p = yes (down P t p)
  ... | no ¬p = no  λ y → ¬p (y id)
  trees-decidable (node l r) t with dec× (trees-decidable l t) (trees-decidable r t)
  ... | yes (a , b) = yes λ { (inj₁ x) → a x; (inj₂ y) → b y }
  ... | no ¬p = no λ x → ¬p (in₁ • x , in₂ • x)
