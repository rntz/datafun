-- Using Agda 2.5.2.
open import Level
open import Data.Nat hiding (_⊔_)

data Pair {i j} (A : Set i) (B : A -> Set j) : Set (i ⊔ j) where
  _,_ : (a : A) (b : B a) -> Pair A B

-- uses instance resolution to solve something
auto : ∀{i}{A : Set i}{{X : A}} -> A
auto {{X}} = X

-- I use postulates for brevity only; I could implement these, but the
-- implementations aren't relevant to the problem.
postulate
  Transitive : (A : Set) -> (A -> A -> Set) -> Set1
  trans : ∀{A R} (C : Transitive A R) {a b c} -> R a b -> R b c -> R a c
  instance trans-≤ : Transitive ℕ _≤_

  -- the same thing, but using a pair
  Transitive' : Pair Set (λ A -> A -> A -> Set) -> Set1
  trans' : ∀{A R} (C : Transitive' (A , R)) {a b c} -> R a b -> R b c -> R a c
  instance trans'-≤ : Transitive' (ℕ , _≤_)

-- THE PROBLEM --
fuz qux : ∀{A B C} -> B ≤ C -> A ≤ B -> A ≤ C
fuz f g = trans  auto g f     -- Why does this work...
qux f g = trans' auto g f     -- and this doesn't work?

-- NB. I use Data.Nat for ℕ and _≤_, but any Set with a relation on it will do.


-- -- This also fails to work, which is a little more understandable.
-- postulate
--   trans'' : ∀{X} (C : Transitive' X) {a b c} -> proj₂ X a b -> proj₂ X b c -> proj₂ X a c
--   instance auto-trans'' : Transitive' (Set , λ a b -> a -> b)

-- wam : ∀{a b c : Set} -> (b -> c) -> (a -> b) -> a -> c
-- wam f g = trans'' auto g f
