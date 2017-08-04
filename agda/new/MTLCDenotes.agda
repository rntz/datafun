module MTLCDenotes where

open import Data.Sum using (inj₁; inj₂)

open import Prelude
open import Cat
open import MTLC
open import Monads
open import Prosets


---------- Denotations of types & tones ----------
Vars : Cx -> Set
Vars X = ∃ (λ a -> X a)
pattern Var {o} {a} p = (o , a) , p

■ = isos

type : Type -> Proset
type (a ⊃ b) = type a ⇨ type b
type (a * b) = type a ∧ type b
type (a + b) = type a ∨ type b
type bool = bools
type (□ a) = ■ (type a)

⟦_⟧₁ : Tone × Type -> Proset
⟦ mono , a ⟧₁ = type a
⟦ disc , a ⟧₁ = ■ (type a)

⟦_⟧ : Cx -> Proset
⟦_⟧+ : Premise -> Proset
⟦ X ⟧ = catΠ (Vars X) (λ v -> ⟦ proj₁ v ⟧₁)
⟦ nil ⟧+    = ⊤-proset
⟦ P , Q ⟧+  = cat× ⟦ P ⟧+ ⟦ Q ⟧+
⟦ □ P ⟧+    = ■ ⟦ P ⟧+
⟦ X ▷ P ⟧+  = ⟦ X ⟧ ⇨ ⟦ P ⟧+
⟦ term a ⟧+ = type a


---------- Lemmas for denotational semantics of terms ----------
-- I've tried to put the most general lemmas at the beginning.
precompose : ∀{i j} {{C : CCC i j}}
           {a b c : obj C} -> a ≤ b -> b ⇨ c ≤ a ⇨ c
precompose {{C}} f = curry (∧-map id f • apply)

-- -- This actually holds in any bicartesian closed category, but if I write it
-- -- that way typechecking takes an extra .8 seconds or so. Argh!
-- distrib-×/⊎ : ∀{a b c} -> proset:× (proset:⊎ a b) c ⇒ proset:⊎ (proset:× a c) (proset:× b c)
-- distrib-×/⊎ = ×-map [ curry in₁ , curry in₂ ] id • apply

-- -- (a ⊎ b) × c ----> (a × c) ⊎ (a × b)

-- -- distrib : ∀{i j} {C : Cat i j} {_⊗_ _⊕_ hom : Obj C -> Obj C -> Obj C}
-- --           {{Pro : Products {i}{j} C _⊗_}} {{Sum : Sums C _⊕_}} {{Clo : Closed C _⊗_ hom}}
-- --           {a b c} -> (a ⊕ b) ⊗ c ≤ (a ⊗ c) ⊕ (b ⊗ c)
-- -- distrib {C = cat C} = ×-map [ curry in₁ , curry in₂ ] id • apply

-- -- Lifts a non-monotone function over an antisymmetric domain into a monotone
-- -- map over its discrete preorder.
-- antisym-lift : ∀{A B} -> Antisym (Hom A) -> (Obj A -> Obj B) -> ■ A ⇒ B
-- antisym-lift {A}{B} antisym f = Functor: f helper
--   where helper : ∀{x y} -> Hom (■ A) x y -> Hom B (f x) (f y)
--         helper x with antisym x
--         ... | Eq.refl = id {{isCat B}}

-- instance
--   -- If (f : a -> b) is monotone, then (f : Disc a -> Disc b) is also monotone.
--   Discrete : Functor cat:Proset cat:Proset
--   ap Discrete = ■
--   cov Discrete f = functor (λ { (x , y) -> cov f x , cov f y })

--   comonadic:■ : Comonadic _ Discrete
--   dup {{comonadic:■}} = functor ⟨ id , swap ⟩
--   extract {{comonadic:■}} = functor proj₁

-- -- ⟦_⟧ is a functor, Cx^op -> Proset
-- -- TODO: better name
-- corename : ∀{X Y} -> X ⊆ Y -> ⟦ Y ⟧ ⇒ ⟦ X ⟧
-- corename f = functor (λ { γ≤σ (Var p) -> γ≤σ (Var (f _ p)) })

-- -- Managing environments.
-- lookup : ∀{X x} -> X x -> ⟦ X ⟧ ⇒ ⟦ x ⟧₁
-- lookup p = functor (λ f -> f (Var p))

-- cons : ∀{X Y} -> proset:× ⟦ X ⟧ ⟦ Y ⟧ ⇒ ⟦ Y ∪ X ⟧
-- ap cons (f , g) (Var p) = [ g ∘ Var , f ∘ Var ] p
-- cov cons (f , g) (_ , inj₁ p) = g (Var p)
-- cov cons (f , g) (_ , inj₂ p) = f (Var p)

-- singleton : ∀{x} -> ⟦ x ⟧₁ ⇒ ⟦ hyp x ⟧
-- ap  singleton x   (Var Eq.refl) = x
-- cov singleton x≤y (Var Eq.refl) = x≤y

-- wipe-sym : ∀{X x y} -> Hom ⟦ wipe X ⟧ x y -> Hom ⟦ wipe X ⟧ y x
-- wipe-sym f (Var {mono} ())
-- wipe-sym f (Var {disc} p) = swap {{products:Set}} (f (Var {disc} p))

-- wipe⇒■ : ∀{X} -> ⟦ wipe X ⟧ ⇒ ■ ⟦ wipe X ⟧
-- wipe⇒■ = functor ⟨ id , wipe-sym ⟩

-- lambda : ∀{x c} -> proset:⇒ ⟦ hyp x ⟧ c ⇒ proset:⇒ ⟦ x ⟧₁ c
-- lambda = precompose singleton


-- ---------- Denotations of terms, premises, and term formers ----------
-- eval  : ∀{X P} -> X ⊢ P -> ⟦ X ⟧ ⇒ ⟦ P ⟧+
-- eval⊩ : ∀{P a} -> P ⊩ a -> ⟦ P ⟧+ ⇒ type a

-- eval tt = functor (λ _ -> tt)
-- eval (M , N) = ⟨ eval M , eval N ⟩
-- eval (bind M) = curry (cons • eval M)
-- eval (box M) = corename extract • wipe⇒■ • map (eval M)
-- eval (var mono p) = lookup p
-- eval (var disc p) = lookup p • extract
-- eval (form ! M) = eval M • eval⊩ form

-- eval⊩ lam = lambda
-- eval⊩ app = apply
-- eval⊩ box = id
-- eval⊩ letbox = ×-map id lambda • swap • apply
-- eval⊩ pair = id
-- eval⊩ (proj true)  = π₁
-- eval⊩ (proj false) = π₂
-- eval⊩ (bool b) = Functor: (λ _ -> b) (λ _ → bool-refl)
-- eval⊩ if = uncurry (antisym-lift antisym:bool≤ (λ x -> if x then π₁ else π₂))
-- eval⊩ (inj true)  = in₁
-- eval⊩ (inj false) = in₂
-- eval⊩ case = distrib-×/⊎
--            • [ ×-map singleton π₁ • swap • apply
--              , ×-map singleton π₂ • swap • apply ]
-- ap (eval⊩ splitsum) x = x
-- cov (eval⊩ splitsum) (rel₁ x , rel₁ y) = rel₁ (x , y)
-- cov (eval⊩ splitsum) (rel₂ x , rel₂ y) = rel₂ (x , y)
