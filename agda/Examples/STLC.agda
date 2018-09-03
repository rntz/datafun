-- Interpreting a non-modal STLC into Preorder.
module Examples.STLC where

open import Prelude
open import Cat


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
rename {X} f (lam M) = lam (rename (∪/⊆ f) M)
rename f (app M N) = app (rename f M) (rename f N)
rename f (pair M N) = pair (rename f M) (rename f N)
rename f (proj d M) = proj d (rename f M)

-- Substitution
infix 1 _⊢*_
_⊢*_ : Cx -> Cx -> Set
X ⊢* Y = ∀{a} -> Y a -> X ⊢ a

∷/⊢* : ∀{X Y} -> X ⊢* Y -> ∀{a} -> a ∷ X ⊢* a ∷ Y
∷/⊢* σ here = var here
∷/⊢* σ (next x) = rename (λ _ → inj₂) (σ x)

subst : ∀{X Y a} -> X ⊢* Y -> Y ⊢ a -> X ⊢ a
subst σ (var x) = σ x
subst σ (lam M) = lam (subst (∷/⊢* σ) M)
subst σ (app M N) = app (subst σ M) (subst σ N)
subst σ (pair M N) = pair (subst σ M) (subst σ N)
subst σ (proj d M) = proj d (subst σ M)


---------- Denotations ----------
⟦_⟧ : Type -> Proset
⟦ s ⊃ t ⟧ = ⟦ s ⟧ ⇨ ⟦ t ⟧
⟦ s * t ⟧ = ⟦ s ⟧ ∧ ⟦ t ⟧

Vars : Cx -> Set
Vars X = ∃ (λ a -> X a)
pattern at p = _ , p
typeof : ∀ {X} -> Vars X -> Type
typeof = proj₁

-- you can solve every problem with enough abstract nonsense
⟦_⟧* : Cx -> Proset
⟦ X ⟧* = catΠ (Vars X) (λ v → ⟦ typeof v ⟧)

lookup : ∀{X a} -> X a -> ⟦ X ⟧* ≤ ⟦ a ⟧
lookup p = fun {(λ f -> f (at p))} (λ f -> f (at p))

cons : ∀{X a} -> ⟦ X ⟧* ∧ ⟦ a ⟧ ≤ ⟦ a ∷ X ⟧*
ap  cons (env , x) (at here) = x
map cons (env , x) (at here) = x
ap  cons (env , x) (at (next p)) = env (at p)
map cons (env , x) (at (next p)) = env (at p)

eval : ∀{X a} -> X ⊢ a -> ⟦ X ⟧* ≤ ⟦ a ⟧
eval (var x) = lookup x
eval (app M N) = ⟨ eval M , eval N ⟩ • apply
eval (lam M) = curry (cons • eval M)
eval (pair M N) = ⟨ eval M , eval N ⟩
eval (proj true  M) = eval M • π₁
eval (proj false M) = eval M • π₂
