module Datafun where

open import Prelude
open import Cat
open import Monads

 ---------- Tones and types ----------
data Tone : Set where mono disc : Tone

data _≺_ : (o p : Tone) -> Set where
  tone-refl : ∀{o} -> o ≺ o
  tone-disc : ∀{o} -> disc ≺ o

-- NB. ≺ forms a Preorder but I haven't needed an instance for it... yet.

_≺?_ : ∀ o p -> Dec (o ≺ p)
mono ≺? mono = yes tone-refl
mono ≺? disc = no (λ ())
disc ≺? _ = yes tone-disc

mutual
  infixr 6 _⊃_
  data Type : Set where
    bool : Type
    set : (a : Type) (p : DEC a) -> Type
    □ : Type -> Type
    _⊃_ _*_ _+_ : (a b : Type) -> Type

  DEC : Type -> Set
  DEC bool = ⊤
  DEC (set a _) = DEC a
  DEC (□ a) = DEC a
  DEC (_ ⊃ _) = ⊥
  DEC (a * b) = DEC a × DEC b
  DEC (a + b) = DEC a × DEC b

-- Type predicates
SL FIN ACC ACC≤ DECSL FIX FIX≤ : Type -> Set
SL bool = ⊤
SL (set _ _) = ⊤
SL (□ a) = ⊥
SL (a * b) = SL a × SL b
SL (a + b) = ⊥
SL (a ⊃ b) = SL b

FIN bool = ⊤
FIN (set a _) = FIN a
FIN (□ a) = FIN a
FIN (a * b) = FIN a × FIN b
FIN (a + b) = FIN a × FIN b
FIN (a ⊃ b) = ⊥

ACC bool = ⊤
ACC (set a _) = FIN a
ACC (□ a) = ⊤
ACC (a * b) = ACC a × ACC b
ACC (a + b) = ACC a × ACC b
ACC (a ⊃ b) = ⊥

ACC≤ bool = ⊤
ACC≤ (set a _) = ⊤
ACC≤ (□ a) = ⊤
ACC≤ (a ⊃ b) = ⊥
ACC≤ (a * b) = ACC≤ a × ACC≤ b
ACC≤ (a + b) = ACC≤ a × ACC≤ b

DECSL a = DEC a × SL a
FIX a = ACC a × DECSL a
FIX≤ a = ACC≤ a × DECSL a

 -- Deciding type predicates.

-- Currently only semi-deciding: that is, we prove that if we answer "yes" then
-- the type does have the property, but not vice-versa. TODO: Prove Dec for
-- decidability instead.
DEC? : ∀ a -> Maybe (DEC a)
DEC? bool = just tt
DEC? (set a _) = DEC? a
DEC? (□ a) = DEC? a
DEC? (a * b) with DEC? a | DEC? b
... | just x | just y = just (x , y)
... | _ | _ = nothing
DEC? (a + b) with DEC? a | DEC? b
... | just x | just y = just (x , y)
... | _ | _ = nothing
DEC? (a ⊃ b) = nothing

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
  letbox : ∀{a b} -> term (□ a) , a is disc ▷ term b ⊩ b
  -- products
  pair   : ∀{a b} -> term a , term b ⊩ a * b
  proj   : ∀{a b} d -> term (a * b) ⊩ (if d then a else b)
  -- sums
  inj    : ∀{a b} d -> term (if d then a else b) ⊩ a + b
  case   : ∀{a b c} -> term (a + b) , a is mono ▷ term c , b is mono ▷ term c ⊩ c
  splitsum : ∀{a b} -> term (□ (a + b)) ⊩ □ a + □ b
  -- booleans
  bool   : Bool -> nil ⊩ bool
  if     : ∀{a} -> □ (term bool) , term a , term a ⊩ a
  when   : ∀{a} -> DECSL a -> term bool , term a ⊩ a
  -- TODO: sets and set-comprehension
  single : ∀{a} (p : DEC a) -> □ (term a) ⊩ set a p
  for-in : ∀{a b} (p : DEC a) (q : DECSL b)
         -> term (set a p) , a is disc ▷ term b ⊩ b
  -- Semilattices. Do these need to be decidable, too?
  --
  --     d(bot) = d(λx. bot) = λx dx. d(bot) = λ x dx. bot = bot
  --
  --     d(f ∨ g) = d(λx. f x ∨ g x)
  --              = λx dx. d(f x ∨ g x)
  --              = λx dx. df x dx ∨ dg x dx
  --              = df v dg
  --
  -- So it looks like no.
  bottom : ∀{a} -> SL a -> nil ⊩ a
  join   : ∀{a} -> SL a -> term a , term a ⊩ a
  -- fixed points
  fix    : ∀{a} -> FIX a -> a is mono ▷ term a ⊩ a
  fix≤   : ∀{a} -> FIX≤ a -> term a , a is mono ▷ term a ⊩ a

data _⊢_ (X : Cx) : Premise -> Set1 where
  tt   : X ⊢ nil
  _,_  : ∀{P Q} (M : X ⊢ P) (N : X ⊢ Q) -> X ⊢ P , Q
  bind : ∀{P Y} (M : Y ∪ X ⊢ P) -> X ⊢ Y ▷ P
  box  : ∀{P}   (M : wipe X ⊢ P) -> X ⊢ □ P
  -- terms
  _!_ : ∀{P a} (form : P ⊩ a) (args : X ⊢ P) -> X ⊢ term a
  var : ∀{a} o (p : X (o , a)) -> X ⊢ term a

 -- Pattern synonyms for terms.
-- pattern lam! {a b} M        = lam {a}{b} ! bind M
-- pattern app! {a b} M N      = app {a}{b} ! M , N
-- pattern box! {a} M          = box {a} ! box M
-- pattern letbox! {a b} M N   = letbox {a}{b} ! M , bind N

 ---------- Renaming terms ----------
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

 ---------- TODO: Substitutions ----------
