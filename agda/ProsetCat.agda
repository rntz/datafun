-- Proset forms a bicartesian closed category. We don't prove this here, but
-- we prove enough of it to write a semantics for Datafun.
module ProsetCat where

open import Prelude
open import Data.Product using (<_,_>)

open import Preorders
open import Cartesian

-- Lemma: if x ≤ y and f ≤ g and f, g monotone then f x ≤ g y.
Pointwise-square≤ : ∀{A B} (f g : A ⇒ B) {x y : Obj A}
                    -> (Pointwise _≤_ (ap f) (ap g)) × (x ≤ y)
                  -> ap f x ≤ ap g y
Pointwise-square≤ {B = proset B'} f g {x = x} (f≤g , x≤y) = f≤g x • cov g x≤y

-- Products
instance
  products:proset : Products cat:Proset proset:×
  ⟨_,_⟩ {{products:proset}} (functor f) (functor g) = functor < f , g >
  π₁ {{products:proset}} = functor proj₁
  π₂ {{products:proset}} = functor proj₂


-- Closure / curry & apply
Proset-λ : ∀{A B C} -> proset:× A B ⇒ C -> A ⇒ (proset:⇒ B C)
ap  (ap (Proset-λ {A}{B}{C} f) a) b        = ap f (a , b)
cov (ap (Proset-λ {proset A} f) a) b1≤b2   = cov f (id , b1≤b2)
cov (Proset-λ {A}{proset B} f)     a1≤a2 b = cov f (a1≤a2 , id)

instance
  closed:proset : Closed cat:Proset proset:× proset:⇒
  curry {{closed:proset}} = Proset-λ
  ap (apply {{closed:proset}}) (f , a) = ap f a
  cov (apply {{closed:proset}}) {f , a} {g , b} = Pointwise-square≤ f g
