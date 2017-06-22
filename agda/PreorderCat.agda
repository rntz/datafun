module PreorderCat where

open import Data.Bool
open import Data.Empty
open import Data.Product
open import Data.Sum
open import Data.Unit using (⊤; tt)
open import Function using (id; _∘_)

-- Theorem: if x ≤ y and f ≤ g and f, g monotone then f x ≤ g y.
Pointwise-square≤ : ∀{A B P Q} {f g : A , P ⇒ B , Q} {x y : A}
                  -> Pointwise _≤_ (_$_ f) (_$_ g) -> x ≤ y -> f $ x ≤ g $ y
Pointwise-square≤ {Q = _ , Q}{g = g}{x = x} f≤g x≤y = f≤g x • g $≤ x≤y
