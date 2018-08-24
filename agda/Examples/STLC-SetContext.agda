module Examples.STLC-SetContext where

open import Prelude
open import Cat
open import Prosets


---------- Types and contexts ----------
infixr 6 _⊃_
data Type : Set where
  _⊃_ _*_ : (a b : Type) -> Type

types : Proset
Obj types = Type
Hom types = _≡_
ident types = refl
compo types refl refl = refl

open import SetContext (types)


---------- Terms ----------
infix 1 _⊢_
data _⊢_ (X : Cx) : Type -> Set where
  var : (x : Var X) -> X ⊢ typeof X x
  lam : ∀{a b} (M : a ∷ X ⊢ b) -> X ⊢ a ⊃ b
  app : ∀{a b} (M : X ⊢ a ⊃ b) (N : X ⊢ a) -> X ⊢ b
  pair : ∀{a b} (M : X ⊢ a) (N : X ⊢ b) -> X ⊢ a * b
  proj : ∀{a b} (d : Bool) (M : X ⊢ a * b) -> X ⊢ (if d then a else b)

-- Renaming
rename : ∀{X Y a} -> X ⊆ Y -> X ⊢ a -> Y ⊢ a
rename (ρ , ok) (var x) rewrite ok x = var (ρ x)
rename {X} f (lam M) = lam (rename (∪/⊆ f) M)
rename f (app M N) = app (rename f M) (rename f N)
rename f (pair M N) = pair (rename f M) (rename f N)
rename f (proj d M) = proj d (rename f M)

-- Substitution
infix 1 _⊢*_
_⊢*_ : Cx -> Cx -> Set
X ⊢* Y = (y : Var Y) -> X ⊢ typeof Y y

∷/⊢* : ∀{X Y} -> X ⊢* Y -> ∀{a} -> a ∷ X ⊢* a ∷ Y
∷/⊢* σ here = var here
∷/⊢* σ (next y) = rename (inj₂ , λ _ → refl) (σ y)

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

-- you can solve every problem with enough abstract nonsense
⟦_⟧* : Cx -> Proset
⟦ X ⟧* = catΠ (Var X) (λ x → ⟦ typeof X x ⟧)

lookup : ∀ X x -> ⟦ X ⟧* ≤ ⟦ typeof X x ⟧
lookup _ p = fun (λ f -> f p)

cons : ∀{X a} -> ⟦ X ⟧* ∧ ⟦ a ⟧ ≤ ⟦ a ∷ X ⟧*
ap cons (env , x) here = x
map cons (env , x) here = x
ap cons (env , x) (next p) = env p
map cons (env , x) (next p) = env p

eval : ∀{X a} -> X ⊢ a -> ⟦ X ⟧* ≤ ⟦ a ⟧
eval {X} (var x) = lookup X x
eval (app M N) = ⟨ eval M , eval N ⟩ • apply
eval (lam M) = curry (cons • eval M)
eval (pair M N) = ⟨ eval M , eval N ⟩
eval (proj true  M) = eval M • π₁
eval (proj false M) = eval M • π₂
