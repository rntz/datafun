{-# OPTIONS --postfix-projections #-}
module WeirdSem where

open import Data.Product
open import Data.Sum
open import Relation.Binary.PropositionalEquality
open import Level
open import Data.Maybe

postulate
  funext : ∀{i j}{A : Set i}{B : A → Set j}
         → (f g : (a : A) → B a)
         → (∀(x : A) → f x ≡ g x)
         → f ≡ g

record CP i j k : Set (suc (i ⊔ j ⊔ k)) where
  field Obj : Set i
  field Δ : Set j
  field valid : Δ → Obj → Obj → Set k
  private _#_⇒_ = valid
  field uniq : ∀{dx x y z} → dx # x ⇒ y → dx # x ⇒ z → y ≡ z

  field nil : Obj → Δ
  field then : Δ → Δ → Δ
  private _·_ = then

  field ident : ∀{x} → nil x # x ⇒ x
  field compo : ∀{dx dy x y z} → dx # x ⇒ y → dy # y ⇒ z → (dx · dy) # x ⇒ z

  field ·nil : ∀{x dx} → nil x · dx ≡ dx
  field nil· : ∀{x dx} → dx · nil x ≡ dx
  field assoc : ∀{dx dy dz} → (dx · dy) · dz ≡ dx · (dy · dz)

open CP public

Product : ∀{i j k} (A B : CP i j k) → CP i j k
Product A B .Obj = Obj A × Obj B
Product A B .Δ = Δ A × Δ B
Product A B .valid (da , db) (a₁ , b₁) (a₂ , b₂)
  = valid A da a₁ a₂ × valid B db b₁ b₂ 
Product A B .uniq (p₁ , q₁) (p₂ , q₂) with uniq A p₁ p₂ | uniq B q₁ q₂
... | refl | refl = refl
Product A B .nil (a , b) = nil A a , nil B b
Product A B .then (da , db) (da' , db') = then A da da' , then B db db'
Product A B .ident = ident A , ident B
Product A B .compo (p₁ , q₁) (p₂ , q₂) = compo A p₁ p₂ , compo B q₁ q₂
Product A B .·nil {a , b} {da , db}
  rewrite ·nil A {a} {da} | ·nil B {b} {db} = refl
Product A B .nil· {a , b} {da , db}
  rewrite nil· A {a} {da} | nil· B {b} {db} = refl
Product A B .assoc {a₁ , a₂} {b₁ , b₂} {c₁ , c₂}
  rewrite assoc A {a₁} {b₁} {c₁} | assoc B {a₂} {b₂} {c₂} = refl
