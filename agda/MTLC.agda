-- Interpreting a modal typed lambda calculus into Preorder.
module MTLC where

open import Prelude
open import Monads
open import Preorders
open import ProsetCat


---------- Tones, types ----------
data Tone : Set where mono disc : Tone

data _≺_ : (o p : Tone) -> Set where
  tone-refl : ∀{o} -> o ≺ o
  tone-disc : ∀{o} -> disc ≺ o

-- NB. ≺ forms a Preorder but I haven't needed an instance for it... yet.

_≺?_ : ∀ o p -> Dec (o ≺ p)
mono ≺? mono = yes tone-refl
mono ≺? disc = no (λ ())
disc ≺? _ = yes tone-disc

infixr 6 _⊃_
data Type : Set where
  _⊃_ _*_ _+_ : (a b : Type) -> Type
  □ : Type -> Type
  bool : Type
  -- TODO: sets


---------- Contexts / typing environments ----------
open import Contexts (Tone × Type) public

-- Singleton context.
infix 7 _is_
_is_ : Type -> Tone -> Cx
a is o = hyp (o , a)

-- Wipe is a comonad on contexts that removes all non-discrete variables.
instance
  Wipe : cat:Cx ⇨ cat:Cx
  ap Wipe X (mono , _) = ⊥
  ap Wipe X (disc , a) = X (disc , a)
  cov Wipe f (mono , _) ()
  cov Wipe f (disc , a) = f (disc , a)

  comonadic:Wipe : Comonadic _ Wipe
  -- dup : wipe X ⊆ wipe (wipe X)
  -- extract : wipe X ⊆ X
  dup {{comonadic:Wipe}} (mono , _) ()
  dup {{comonadic:Wipe}} (disc , a) = id
  extract {{comonadic:Wipe}} (mono , _) ()
  extract {{comonadic:Wipe}} (disc , a) = id

wipe = ap Wipe

infix 4 _at_
_at_ : Cx -> Tone -> Cx
X at mono = X
X at disc = wipe X


---------- ABTs ----------
infix  3 _⊩_ _⊢_ _!_
infixr 4 _∧_ _,_
infix  5 _▷_

data Premise : Set1 where
  nil : Premise
  _∧_ : (P Q : Premise) -> Premise
  □ : (P : Premise) -> Premise
  _▷_ : (X : Cx) (P : Premise) -> Premise
  term : (a : Type) -> Premise

-- Term formers
data _⊩_ : Premise -> Type -> Set where
  -- functions
  lam : ∀{a b} -> a is mono ▷ term b ⊩ a ⊃ b
  app : ∀{a b} -> term (a ⊃ b) ∧ term a ⊩ b
  -- box
  box    : ∀{a} -> □ (term a) ⊩ □ a
  letbox : ∀{a b} -> term (□ a) ∧ (a is disc ▷ term b) ⊩ b
  -- products
  pair   : ∀{a b} -> term a ∧ term b ⊩ a * b
  proj   : ∀{a b} d -> term (a * b) ⊩ (if d then a else b)
  -- TODO sums
  inj    : ∀{a b} d -> term (if d then a else b) ⊩ a + b
  case   : ∀{a b c} -> term (a + b) ∧ (a is mono ▷ term c) ∧ (b is mono ▷ term c) ⊩ c
  splitsum : ∀{a b} -> term (□ (a + b)) ⊩ □ a + □ b
  -- booleans
  bool   : Bool -> nil ⊩ bool
  if     : ∀{a} -> □ (term bool) ∧ term a ∧ term a ⊩ a
  -- TODO: monotone `if` eliminator, using semilattices

data _⊢_ (X : Cx) : Premise -> Set1 where
  tt   : X ⊢ nil
  _,_  : ∀{P Q} (M : X ⊢ P) (q : X ⊢ Q) -> X ⊢ P ∧ Q
  bind : ∀{P Y} (M : Y ∪ X ⊢ P) -> X ⊢ Y ▷ P
  box  : ∀{P}   (M : wipe X ⊢ P) -> X ⊢ □ P
  -- terms
  _!_ : ∀{P a} (form : P ⊩ a) (args : X ⊢ P) -> X ⊢ term a
  var : ∀{a} o (p : X (o , a)) -> X ⊢ term a


-- Pattern synonyms for terms.
pattern lam! {a b} M        = lam {a}{b} ! bind M
pattern app! {a b} M N      = app {a}{b} ! M , N
pattern box! {a} M          = box {a} ! box M
pattern letbox! {a b} M N   = letbox {a}{b} ! M , bind N


-- Applying context renamings to terms
rename : ∀{X Y P} -> X ⊆ Y -> X ⊢ P -> Y ⊢ P
rename f tt = tt
rename f (M , N) = rename f M , rename f N
rename f (bind M) = bind (rename (∪/⊆ f) M)
rename f (box M) = box (rename (map f) M)
rename f (form ! M) = form ! rename f M
rename f (var o p) = var o (f (o , _) p)

rename-at : ∀{X Y} o {a} -> X ⊆ Y -> X at o ⊢ a -> Y at o ⊢ a
rename-at mono f M = rename f M
rename-at disc f M = rename (map f) M


---------- TODO Substitutions ----------


---------- Denotations ----------
Vars : Cx -> Set
Vars X = ∃ (λ a -> X a)
pattern Var {o} {a} p = (o , a) , p

■ = proset:Iso

type : Type -> Proset
type (a ⊃ b) = proset:⇒ (type a) (type b)
type (a * b) = proset:× (type a) (type b)
type (a + b) = proset:⊎ (type a) (type b)
type bool = proset:Bool
type (□ a) = ■ (type a)

⟦_⟧₁ : Tone × Type -> Proset
⟦ mono , a ⟧₁ = type a
⟦ disc , a ⟧₁ = ■ (type a)

⟦_⟧ : Cx -> Proset
⟦_⟧+ : Premise -> Proset
⟦ X ⟧ = proset:Π {Vars X} (λ v -> ⟦ proj₁ v ⟧₁)
⟦ nil ⟧+    = proset:⊤
⟦ P ∧ Q ⟧+  = proset:× ⟦ P ⟧+ ⟦ Q ⟧+
⟦ □ P ⟧+    = ■ ⟦ P ⟧+
⟦ X ▷ P ⟧+  = proset:⇒ ⟦ X ⟧ ⟦ P ⟧+
⟦ term a ⟧+ = type a


---------- Lemmas for denotational semantics of terms ----------
-- I've tried to put the most general lemmas at the beginning.
precompose : ∀{i j C _⊗_ hom} {{P : Products {i}{j} C _⊗_}} {{Cl : Closed C _⊗_ hom}}
           {a b c} -> a ⇨ b -> hom b c ⇨ hom a c
precompose {C = cat C} f = curry (×-map id f • apply)

-- This actually holds in any bicartesian closed category, but if I write it
-- that way typechecking takes an extra .8 seconds or so. Argh!
distrib-×/⊎ : ∀{a b c} -> proset:× (proset:⊎ a b) c ⇒ proset:⊎ (proset:× a c) (proset:× b c)
distrib-×/⊎ = ×-map [ curry in₁ , curry in₂ ] id • apply

-- (a ⊎ b) × c ----> (a × c) ⊎ (a × b)

-- distrib : ∀{i j} {C : Cat i j} {_⊗_ _⊕_ hom : Obj C -> Obj C -> Obj C}
--           {{Pro : Products {i}{j} C _⊗_}} {{Sum : Sums C _⊕_}} {{Clo : Closed C _⊗_ hom}}
--           {a b c} -> (a ⊕ b) ⊗ c ⇨ (a ⊗ c) ⊕ (b ⊗ c)
-- distrib {C = cat C} = ×-map [ curry in₁ , curry in₂ ] id • apply

-- Lifts a non-monotone function over an antisymmetric domain into a monotone
-- map over its discrete preorder.
antisym-lift : ∀{A B} -> Antisym (Hom A) -> (Obj A -> Obj B) -> ■ A ⇒ B
antisym-lift {A}{B} antisym f = Functor: f helper
  where helper : ∀{x y} -> Hom (■ A) x y -> Hom B (f x) (f y)
        helper x with antisym x
        ... | Eq.refl = id {{isCat B}}

instance
  -- If (f : a -> b) is monotone, then (f : Disc a -> Disc b) is also monotone.
  Discrete : Functor cat:Proset cat:Proset
  ap Discrete = ■
  cov Discrete f = functor (λ { (x , y) -> cov f x , cov f y })

  comonadic:■ : Comonadic _ Discrete
  dup {{comonadic:■}} = functor ⟨ id , swap ⟩
  extract {{comonadic:■}} = functor proj₁

-- ⟦_⟧ is a functor, Cx^op -> Proset
-- TODO: better name
corename : ∀{X Y} -> X ⊆ Y -> ⟦ Y ⟧ ⇒ ⟦ X ⟧
corename f = functor (λ { γ≤σ (Var p) -> γ≤σ (Var (f _ p)) })

-- Managing environments.
lookup : ∀{X x} -> X x -> ⟦ X ⟧ ⇒ ⟦ x ⟧₁
lookup p = functor (λ f -> f (Var p))

cons : ∀{X Y} -> proset:× ⟦ X ⟧ ⟦ Y ⟧ ⇒ ⟦ Y ∪ X ⟧
ap cons (f , g) (Var p) = [ g ∘ Var , f ∘ Var ] p
cov cons (f , g) (_ , inj₁ p) = g (Var p)
cov cons (f , g) (_ , inj₂ p) = f (Var p)

singleton : ∀{x} -> ⟦ x ⟧₁ ⇒ ⟦ hyp x ⟧
ap  singleton x   (Var Eq.refl) = x
cov singleton x≤y (Var Eq.refl) = x≤y

wipe-sym : ∀{X x y} -> Hom ⟦ wipe X ⟧ x y -> Hom ⟦ wipe X ⟧ y x
wipe-sym f (Var {mono} ())
wipe-sym f (Var {disc} p) = swap {{products:Set}} (f (Var {disc} p))

wipe⇒■ : ∀{X} -> ⟦ wipe X ⟧ ⇒ ■ ⟦ wipe X ⟧
wipe⇒■ = functor ⟨ id , wipe-sym ⟩

lambda : ∀{x c} -> proset:⇒ ⟦ hyp x ⟧ c ⇒ proset:⇒ ⟦ x ⟧₁ c
lambda = precompose singleton
