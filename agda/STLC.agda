-- Interpreting a non-modal STLC into Posets.
module STLC where

open import Prelude

open import Preorders
import Trees
open Trees using (TreeSet)


---------- Types and contexts ----------
infixr 6 _⊃_
data Type : Set where
  _⊃_ : Type -> Type -> Type
  bool : Type
  disc : Type -> Type
  setof : Type -> Type

open import Contexts (Type)


---------- Terms ----------
infix 1 _⊢_
data _⊢_ (X : Cx) : Type -> Set where
  var : ∀{a} (x : a ∈ X) -> X ⊢ a
  lam : ∀{a b} (M : a ∷ X ⊢ b) -> X ⊢ a ⊃ b
  app : ∀{a b} (M : X ⊢ a ⊃ b) (N : X ⊢ a) -> X ⊢ b

  -- -- Booleans
  -- boolean : (x : Bool) -> X ⊢ bool
  -- -- wait, this is non-monotone! aghksdfjlsdfjs
  -- ifThen : ∀{a} (M : X ⊢ bool) (N₁ N₂ : X ⊢ a) -> X ⊢ a
  -- -- Sets
  -- empty : ∀{a} -> X ⊢ setof a
  -- single : ∀{a} (M : X ⊢ a) -> X ⊢ setof a
  -- union : ∀{a} -> (M N : X ⊢ setof a) -> X ⊢ setof a
  -- -- This unnecessarily requires us to be monotone. Hm.
  -- setBind : ∀{a b} (M : X ⊢ setof a) (N : a ∷ X ⊢ setof b) -> X ⊢ setof b

-- Renaming
rename : ∀{X Y a} -> X ⊆ Y -> X ⊢ a -> Y ⊢ a
rename f (var x) = var (f x)
rename {X} f (lam M) = lam (rename (∷/⊆ X f) M)
rename f (app M N) = app (rename f M) (rename f N)
-- rename f (boolean x) = boolean x
-- rename f (ifThen M N₁ N₂) = ifThen (rename f M) (rename f N₁) (rename f N₂)


---------- Denotations ----------
⟦_⟧ : Type -> Proset
⟦ s ⊃ t ⟧ = Proset:⇒ ⟦ s ⟧ ⟦ t ⟧
⟦ bool ⟧ = Proset:Bool
⟦ disc t ⟧ = Proset:Iso ⟦ t ⟧
⟦ setof t ⟧ = TreeSet (carrier ⟦ t ⟧)

record Vars (X : Cx) : Set where
  constructor Var
  field typeof : Type
  field posn : typeof ∈ X
open Vars

at : ∀{X a} -> a ∈ X -> Vars X
at p = record { typeof = _; posn = p }

-- Vars : Cx -> Set
-- Vars X = ∃ (λ a -> a ∈ X)

-- typeof : ∀ {X} -> Vars X -> Type
-- typeof = proj₁

-- at : ∀{X a} -> a ∈ X -> Vars X
-- at = ,_

-- you can solve every problem with enough abstract nonsense
⟦_⟧* : Cx -> Proset
⟦ X ⟧* = Proset:Π {Vars X} (λ v → ⟦ typeof v ⟧)

module _ where
  open _⇒_

  private
    -- flipped function application
    pipe : ∀{A : Set}{B : A -> Set} (x : A) (f : ∀ x -> B x) -> B x
    pipe x f = f x

    -- -- _$_ : A ⇒ B -> carrier A -> carrier B
    -- infixr 1 _$_
    -- _$_ = call

  eval : ∀{X a} -> X ⊢ a -> ⟦ X ⟧* ⇒ ⟦ a ⟧
  eval (var x) = func (pipe (at x)) (pipe (at x))
  _$_  (eval (app M N)) env = (eval M $ env) $ eval N $ env
  _$≤_ (eval {X} {a} (app M N)) {e1} {e2} e1≤e2 = {!!}
    where foo : related {!!} (eval M $ e1) {!!}
          foo = {!!}
          bar = proj₂ (preorder ⟦ a ⟧)
  eval (lam M) = {!!}
