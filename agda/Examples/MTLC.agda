-- Interpreting a modal typed lambda calculus into Preorder.
module Examples.MTLC where

open import Prelude
open import Cat
open import Monads


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


---------- Contexts / typing environments ----------
open import Contexts (Tone × Type) public

-- Singleton context.
infix 7 _is_
_is_ : Type -> Tone -> Cx
a is o = hyp (o , a)

-- Wipe is a comonad on contexts that removes all non-discrete variables.
Wipe : cxs ≤ cxs
ap Wipe X (mono , _) = ⊥
ap Wipe X (disc , a) = X (disc , a)
map Wipe f (mono , _) ()
map Wipe f (disc , a) = f (disc , a)

instance
  Wipe-comonad : Comonad Wipe
  -- dup : wipe X ⊆ wipe (wipe X)
  Comonad.dup Wipe-comonad (mono , _) ()
  Comonad.dup Wipe-comonad (disc , a) = id
  -- extract : wipe X ⊆ X
  Comonad.extract Wipe-comonad (mono , _) ()
  Comonad.extract Wipe-comonad (disc , a) = id

wipe : Cx -> Cx
wipe = ap Wipe

infix 4 _at_
_at_ : Cx -> Tone -> Cx
X at mono = X
X at disc = wipe X


---------- ABTs ----------
infix  3 _⊩_ _⊢_ _!_
infixr 4 _,_
infix  5 _▷_

data Premise : Set1 where
  nil : Premise
  _,_ : (P Q : Premise) -> Premise
  □ : (P : Premise) -> Premise
  _▷_ : (X : Cx) (P : Premise) -> Premise
  term : (a : Type) -> Premise

-- Term formers
data _⊩_ : Premise -> Type -> Set where
  -- functions
  lam : ∀{a b} -> a is mono ▷ term b ⊩ a ⊃ b
  app : ∀{a b} -> term (a ⊃ b) , term a ⊩ b
  -- box
  box    : ∀{a} -> □ (term a) ⊩ □ a
  letbox : ∀{a b} -> term (□ a) , (a is disc ▷ term b) ⊩ b
  -- products
  pair   : ∀{a b} -> term a , term b ⊩ a * b
  proj   : ∀{a b} d -> term (a * b) ⊩ (if d then a else b)
  -- sums
  inj    : ∀{a b} d -> term (if d then a else b) ⊩ a + b
  case   : ∀{a b c} -> term (a + b) , (a is mono ▷ term c) , (b is mono ▷ term c) ⊩ c
  splitsum : ∀{a b} -> term (□ (a + b)) ⊩ □ a + □ b
  -- booleans
  bool   : Bool -> nil ⊩ bool
  if     : ∀{a} -> □ (term bool) , term a , term a ⊩ a

data _⊢_ (X : Cx) : Premise -> Set1 where
  tt   : X ⊢ nil
  _,_  : ∀{P Q} (M : X ⊢ P) (N : X ⊢ Q) -> X ⊢ P , Q
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
rename f tt         = tt
rename f (M , N)    = rename f M , rename f N
rename f (bind M)   = bind (rename (∪/⊆ f) M)
rename f (box M)    = box (rename (map Wipe f) M)
rename f (form ! M) = form ! rename f M
rename f (var o p)  = var o (f (o , _) p)

rename-at : ∀{X Y} o {a} -> X ⊆ Y -> X at o ⊢ a -> Y at o ⊢ a
rename-at mono f M = rename f M
rename-at disc f M = rename (map Wipe f) M
