-- Interpreting a modal typed lambda calculus into Preorder.
module MTLC where

open import Prelude
open import Data.Sum using () renaming (inj₁ to left; inj₂ to rite)

open import Cartesian
open import Monads
open import Preorders
open import ProsetCat

swap : ∀{A B : Set} -> A × B -> B × A
swap (x , y) = y , x


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
  _⊃_ _*_ : (a b : Type) -> Type
  □ : Type -> Type

-- NB. Type is currently uninhabited.


---------- Contexts / typing environments ----------
open import Contexts (Tone × Type)

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
infix  3 _⊫_ _⊩_ _⊢_ _!_
infixr 4 _∧_
infix  5 _▷_

data Premise : Set1 where
  nil : Premise
  _∧_ : (P Q : Premise) -> Premise
  □ : (P : Premise) -> Premise
  _▷_ : (X : Cx) (P : Premise) -> Premise
  term : (a : Type) -> Premise

-- Term formers
data _⊫_ : Premise -> Type -> Set where
  -- functions
  lam : ∀{a b} -> a is mono ▷ term b ⊫ a ⊃ b
  app : ∀{a b} -> term (a ⊃ b) ∧ term a ⊫ b
  -- box
  box    : ∀{a} -> □ (term a) ⊫ □ a
  letbox : ∀{a b} -> term (□ a) ∧ (a is disc ▷ term b) ⊫ b
  -- products
  pair   : ∀{a b} -> term a ∧ term b ⊫ a * b
  proj   : ∀{a b} d -> term (a * b) ⊫ (if d then a else b)

data _⊩_ (X : Cx) : Premise -> Set1 where
  tt   : X ⊩ nil
  _,_  : ∀{P Q} (M : X ⊩ P) (q : X ⊩ Q) -> X ⊩ P ∧ Q
  bind : ∀{P Y} (M : Y ∪ X ⊩ P) -> X ⊩ Y ▷ P
  box  : ∀{P}   (M : wipe X ⊩ P) -> X ⊩ □ P
  -- terms
  _!_ : ∀{P a} (form : P ⊫ a) (args : X ⊩ P) -> X ⊩ term a
  var : ∀{a} o (p : X (o , a)) -> X ⊩ term a

_⊢_ : Cx -> Type -> Set1
X ⊢ a = X ⊩ term a


-- Pattern synonyms for terms.
pattern lam! {a b} M        = lam {a}{b} ! bind M
pattern app! {a b} M N      = app {a}{b} ! M , N
pattern box! {a} M          = box {a} ! box M
pattern letbox! {a b} M N   = letbox {a}{b} ! M , bind N


-- Applying context renamings to terms
rename : ∀{X Y P} -> X ⊆ Y -> X ⊩ P -> Y ⊩ P
rename f tt = tt
rename f (M , N) = rename f M , rename f N
rename f (bind M) = bind (rename (∪/⊆ f) M)
rename f (box M) = box (rename (map {{Wipe}} f) M)
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
type (□ a) = ■ (type a)

toneType : Tone × Type -> Proset
toneType (mono , a) = type a
toneType (disc , a) = ■ (type a)

⟦_⟧* : Cx -> Proset
⟦_⟧ : Premise -> Proset
⟦ X ⟧* = proset:Π {Vars X} (λ v -> toneType (proj₁ v))
⟦ nil ⟧ = proset:⊤
⟦ P ∧ Q ⟧ = proset:× ⟦ P ⟧ ⟦ Q ⟧
⟦ □ P ⟧ = ■ ⟦ P ⟧
⟦ X ▷ P ⟧ = proset:⇒ ⟦ X ⟧* ⟦ P ⟧
⟦ term a ⟧ = type a

-- ⟦_⟧* is a functor, Cx^op -> Proset
-- TODO: better name
corename : ∀{X Y} -> X ⊆ Y -> ⟦ Y ⟧* ⇒ ⟦ X ⟧*
corename f = functor (λ { γ≤σ (Var p) -> γ≤σ (Var (f _ p)) })

lookup : ∀{X x} -> X x -> ⟦ X ⟧* ⇒ toneType x
lookup p = functor (λ f -> f (Var p))

cons : ∀{X Y} -> proset:× ⟦ X ⟧* ⟦ Y ⟧* ⇒ ⟦ Y ∪ X ⟧*
ap cons (f , g) (Var p) = [ g ∘ Var , f ∘ Var ] p
cov cons (f , g) (_ , left p) = g (Var p)
cov cons (f , g) (_ , rite p) = f (Var p)

instance
  -- If (f : a -> b) is monotone, then (f : Disc a -> Disc b) is also monotone.
  Discrete : Functor cat:Proset cat:Proset
  ap Discrete = ■
  cov Discrete f = functor (λ { (x , y) -> cov f x , cov f y })

  comonadic:Iso : Comonadic _ Discrete
  dup {{comonadic:Iso}} = functor ⟨ id , swap ⟩
  extract {{comonadic:Iso}} = functor proj₁

wipe-sym : ∀{X x y} -> Hom ⟦ wipe X ⟧* x y -> Hom ⟦ wipe X ⟧* y x
wipe-sym f (Var {mono} ())
wipe-sym f (Var {disc} p) = swap (f (Var {disc} p))

wipe⇒■ : ∀{X} -> ⟦ wipe X ⟧* ⇒ ■ ⟦ wipe X ⟧*
wipe⇒■ = functor ⟨ id , wipe-sym ⟩

-- TODO: organize helper functions
singleton : ∀{x} -> toneType x ⇒ ⟦ hyp x ⟧*
ap singleton x (Var Eq.refl) = x
cov singleton x≤y (Var Eq.refl) = x≤y

precompose : ∀{i j C _⊗_ hom} {{P : Products {i}{j} C _⊗_}} {{Cl : Closed C _⊗_ hom}}
           {a b c} -> a ⇨ b -> hom b c ⇨ hom a c
precompose {C = cat C} f = curry (⟨ π₁ , π₂ • f ⟩ • apply)

lambda : ∀{x c} -> proset:⇒ ⟦ hyp x ⟧* c ⇒ proset:⇒ (toneType x) c
lambda = precompose singleton

-- The heart of the matter.
eval : ∀{X P} -> X ⊩ P -> ⟦ X ⟧* ⇒ ⟦ P ⟧
eval⊫ : ∀{P a} -> P ⊫ a -> ⟦ P ⟧ ⇒ type a

eval tt = functor (λ _ -> tt)
eval (M , N) = ⟨ eval M , eval N ⟩
eval (bind M) = curry (cons • eval M)
eval (box M) = forget • wipe⇒■ • map (eval M)
  where forget = corename extract
eval (var mono p) = lookup p
eval (var disc p) = lookup p • extract
eval (form ! M) = eval M • eval⊫ form

eval⊫ lam = lambda
eval⊫ app = apply
eval⊫ box = id
eval⊫ letbox = ⟨ π₂ • lambda , π₁ ⟩ • apply
eval⊫ pair = id
eval⊫ (proj true) = π₁
eval⊫ (proj false) = π₂
