-- Interpreting a modal typed lambda calculus into Preorder.
module MTLC where

open import Prelude
-- maybe left/rite instead of car/cdr?
open import Data.Sum using ([_,_]) renaming (inj₁ to left; inj₂ to rite)

open import ProsetCat
open import Preorders
--open import Nonsense


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
  ■ : Type -> Type


---------- Contexts / typing environments ----------
Cx : Set₁
Cx = (o : Tone) (a : Type) -> Set

-- We have two possible choices of interpretation here:
--
-- 1. (X o a) means a variable with type `a` is in the context with tone `o`; or,
-- 2. (X o a) means a variable with type `a` is in the context with tone *at least* `o`.
--
-- That is to say, is X expected to preserve the subtone relationship? I.e, does this hold:
--
--     ∀(X : Cx) (a : Type) -> X a disc -> X a mono
--
-- Currently we choose interpretation (1), becuase it simplifies constructing
-- Cxs, but the other interpretation would simplify using them.

∅ : Cx
∅ o a = ⊥

-- Singleton context.
infix 5 _is_
data _is_ (a : Type) (o : Tone) : Cx where
  eq : (a is o) o a

infixr 4 _∪_
_∪_ : (X Y : Cx) -> Cx
(X ∪ Y) o a = X o a ⊎ Y o a

wipe : (X : Cx) -> Cx
wipe X mono = λ _ -> ⊥
wipe X disc = X disc

infix 4 _at_
_at_ : Cx -> Tone -> Cx
X at mono = X
X at disc = wipe X


---------- Context renamings ----------
infix 3 _⊆_
_⊆_ : (X Y : Cx) -> Set
X ⊆ Y = ∀ o {a} -> X o a -> Y o a

instance
  compose:Cx : Compose Cx _⊆_
  identity compose:Cx _ = id
  compose  compose:Cx X⊆Y Y⊆Z o = X⊆Y o • Y⊆Z o

wipe/⊆ : ∀{X Y} -> X ⊆ Y -> wipe X ⊆ wipe Y
wipe/⊆ f mono ()
wipe/⊆ f disc = f disc

record Comonadic {i j} (C : Cat i j) (□ : Functor C C) : Set (i ⊔ j) where
  field dup : ∀{x} -> ap □ x ⇨ ap □ (ap □ x)
  field extract : ∀{x} -> ap □ x ⇨ x

-- Make □/dup/extract instance methods.
open Comonadic {{...}}

instance
  comonadic:wipe : Comonadic (cat compose:Cx) (functor wipe/⊆)
  dup {{comonadic:wipe}} mono ()
  dup {{comonadic:wipe}} disc x = x
  extract {{comonadic:wipe}} mono ()
  extract {{comonadic:wipe}} disc x = x

-- ∪-inj₂ ?
drop : ∀{X Y} -> Y ⊆ X ∪ Y
drop o = rite

∪/⊆ : ∀{X Y Z} -> X ⊆ Y -> (Z ∪ X) ⊆ (Z ∪ Y)
∪/⊆ f _ = [ left , rite ∘ f _ ]

drop-mid : ∀{X Y Z} -> X ∪ Z ⊆ X ∪ Y ∪ Z
drop-mid o = [ left , rite ∘ rite ]


---------- ABTs ----------
