-- Preorder forms a bicartesian closed category. We don't prove this here, but
-- we prove enough of it to write a semantics for Datafun.
module PreorderCat where

open import Prelude
open import Data.Product using (<_,_>)

open import Preorders
open IsPreorder
open _⇒_

-- Theorem: if x ≤ y and f ≤ g and f, g monotone then f x ≤ g y.
Pointwise-square≤ : ∀{A B P Q} (f g : A , P ⇒ B , Q) {x y : A}
                  -> (Pointwise _≤_ (call f) (call g) × x ≤ y)
                  -> call f x ≤ call g y
Pointwise-square≤ {Q = _ , Q} f g {x = x} (f≤g , x≤y) = trans (f≤g x) (mono g x≤y)

-- Composition
_•_ : ∀{A B C} -> A ⇒ B -> B ⇒ C -> A ⇒ C
func f f≤ • func g g≤ = func (g ∘ f) (g≤ ∘ f≤)

-- Products
⟨_,_⟩ : ∀{A B C} -> A ⇒ B -> A ⇒ C -> A ⇒ Proset:× B C
⟨ func f f≤ , func g g≤ ⟩ = func < f , g > < f≤ , g≤ >

π₁ : ∀{A B} -> (Proset:× A B) ⇒ A
π₂ : ∀{A B} -> (Proset:× A B) ⇒ B
π₁ = func proj₁ proj₁
π₂ = func proj₂ proj₂

-- Closure / λ & eval / curry & apply
Preorder-eval : ∀{A B} -> Proset:× (Proset:⇒ A B) A ⇒ B
call Preorder-eval (f , a) = call f a
mono Preorder-eval {f , a} {g , b} = Pointwise-square≤ f g

infix 9 _$_
_$_ = call

Preorder-λ : ∀{A B C} -> Proset:× A B ⇒ C -> A ⇒ (Proset:⇒ B C)
call (call (Preorder-λ {A}{B}{C} f) a) b = f $ (a , b)
mono (call (Preorder-λ {_ , _ , A} f) a) b1≤b2 = mono f (refl , b1≤b2)
mono (Preorder-λ {A}{_ , _ , B} f) a1≤a2 b = mono f (a1≤a2 , refl)
