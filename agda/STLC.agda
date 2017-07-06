-- Interpreting a non-modal STLC into Preorder.
module STLC where

open import Prelude

open import Cartesian
open import ProsetCat
open import Preorders


---------- Types and contexts ----------
infixr 6 _⊃_
data Type : Set where
  _⊃_ _*_ : (a b : Type) -> Type

open import Contexts (Type)


---------- Terms ----------
infix 1 _⊢_
data _⊢_ (X : Cx) : Type -> Set where
  var : ∀{a} (x : X a) -> X ⊢ a
  lam : ∀{a b} (M : a ∷ X ⊢ b) -> X ⊢ a ⊃ b
  app : ∀{a b} (M : X ⊢ a ⊃ b) (N : X ⊢ a) -> X ⊢ b
  pair : ∀{a b} (M : X ⊢ a) (N : X ⊢ b) -> X ⊢ a * b
  proj : ∀{a b} (d : Bool) (M : X ⊢ a * b) -> X ⊢ (if d then a else b)

-- Renaming
rename : ∀{X Y a} -> X ⊆ Y -> X ⊢ a -> Y ⊢ a
rename f (var x) = var (f _ x)
rename {X} f (lam M) = lam (rename (∷/⊆ X f) M)
rename f (app M N) = app (rename f M) (rename f N)
rename f (pair M N) = pair (rename f M) (rename f N)
rename f (proj d M) = proj d (rename f M)


---------- Denotations ----------
⟦_⟧ : Type -> Proset
⟦ s ⊃ t ⟧ = proset:⇒ ⟦ s ⟧ ⟦ t ⟧
⟦ s * t ⟧ = proset:× ⟦ s ⟧ ⟦ t ⟧

Vars : Cx -> Set
Vars X = ∃ (λ a -> X a)
pattern at p = _ , p
typeof : ∀ {X} -> Vars X -> Type
typeof = proj₁

-- you can solve every problem with enough abstract nonsense
⟦_⟧* : Cx -> Proset
⟦ X ⟧* = proset:Π {Vars X} (λ v → ⟦ typeof v ⟧)

module _ where
  open import Data.Sum using ([_,_])

  lookup : ∀{X a} -> X a -> ⟦ X ⟧* ⇒ ⟦ a ⟧
  lookup p = functor {(λ f -> f (at p))} (λ f -> f (at p))

  cons : ∀{X a} -> proset:× ⟦ X ⟧* ⟦ a ⟧ ⇒ ⟦ a ∷ X ⟧*
  ap  cons (env , x) (at here) = x
  cov cons (env , x) (at here) = x
  ap  cons (env , x) (at (next p)) = env (at p)
  cov cons (env , x) (at (next p)) = env (at p)

  eval : ∀{X a} -> X ⊢ a -> ⟦ X ⟧* ⇒ ⟦ a ⟧
  eval (var x) = lookup x
  eval (app M N) = ⟨ eval M , eval N ⟩ • apply
  eval (lam M) = curry (cons • eval M)
  eval (pair M N) = ⟨ eval M , eval N ⟩
  eval (proj true  M) = eval M • π₁
  eval (proj false M) = eval M • π₂
