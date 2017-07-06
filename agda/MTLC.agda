-- Interpreting a modal typed lambda calculus into Preorder.
module MTLC where

open import Prelude
open import Data.Sum using () renaming (inj₁ to left; inj₂ to rite)

open import Cartesian
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
  _⊃_ : (a b : Type) -> Type
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
  ⊫lam : ∀{a b} -> a is mono ▷ term b ⊫ a ⊃ b
  ⊫app : ∀{a b} -> term (a ⊃ b) ∧ term a ⊫ b
  -- box
  ⊫box    : ∀{a} -> □ (term a) ⊫ □ a
  ⊫letbox : ∀{a b} -> term (□ a) ∧ (a is disc ▷ term b) ⊫ b

data _⊩_ (X : Cx) : Premise -> Set1 where
  tt   : X ⊩ nil
  _,_  : ∀{P Q} (p : X ⊩ P) (q : X ⊩ Q) -> X ⊩ P ∧ Q
  bind : ∀{P Y} (p : Y ∪ X ⊩ P) -> X ⊩ Y ▷ P
  box  : ∀{P}   (p : wipe X ⊩ P) -> X ⊩ □ P
  -- terms
  _!_ : ∀{P a} (form : P ⊫ a) (args : X ⊩ P) -> X ⊩ term a
  var : ∀{a} o (p : X (o , a)) -> X ⊩ term a

_⊢_ : Cx -> Type -> Set1
X ⊢ a = X ⊩ term a


-- Pattern synonyms for terms.
pattern lam! {a b} M        = ⊫lam {a}{b} ! bind M
pattern app! {a b} M N      = ⊫app {a}{b} ! M , N
pattern box! {a} M          = ⊫box {a} ! box M
pattern letbox! {a b} M N   = ⊫letbox {a}{b} ! M , bind N


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


---------- TODO Denotations ----------
