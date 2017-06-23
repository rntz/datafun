-- Proset forms a bicartesian closed category. We don't prove this here, but
-- we prove enough of it to write a semantics for Datafun.
module PreorderCat where

open import Prelude
open import Data.Product using (<_,_>)

open import Preorders
open _⇒_

-- -- This doesn't work. Why?
-- instance
--   foo : {{A : Proset}} -> Preorder _ (rel A)
--   foo {{proset A}} = A

-- Lemma: if x ≤ y and f ≤ g and f, g monotone then f x ≤ g y.
Pointwise-square≤ : ∀{A B} (f g : A ⇒ B) {x y : obj A}
                  -> (Pointwise _≤_ (call f) (call g) × x ≤ y)
                  -> call f x ≤ call g y
Pointwise-square≤ {B = proset B'} f g {x = x} (f≤g , x≤y) = f≤g x • mono g x≤y


-- Products
⟨_,_⟩ : ∀{A B C} -> A ⇒ B -> A ⇒ C -> A ⇒ proset:× B C
⟨ func f f≤ , func g g≤ ⟩ = func < f , g > < f≤ , g≤ >

π₁ : ∀{A B} -> (proset:× A B) ⇒ A
π₂ : ∀{A B} -> (proset:× A B) ⇒ B
π₁ = func proj₁ proj₁
π₂ = func proj₂ proj₂


-- Closure / λ & eval / curry & apply
Preorder-eval : ∀{A B} -> proset:× (proset:⇒ A B) A ⇒ B
call Preorder-eval (f , a) = call f a
mono Preorder-eval {f , a} {g , b} = Pointwise-square≤ f g

infix 9 _$_
_$_ = call

Preorder-λ : ∀{A B C} -> proset:× A B ⇒ C -> A ⇒ (proset:⇒ B C)
call (call (Preorder-λ {A}{B}{C} f) a) b = f $ (a , b)
mono (call (Preorder-λ {proset A} f) a) b1≤b2 = mono f (id , b1≤b2)
mono (Preorder-λ {A}{proset B} f) a1≤a2 b = mono f (a1≤a2 , id)
