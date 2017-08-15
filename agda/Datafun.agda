module Datafun where

open import Prelude
open import Cat
open import Monads

 ---------- Tones, types, and typeclasses ----------
data Tone : Set where mono disc : Tone

data _≺_ : (o p : Tone) -> Set where
  tone-refl : ∀{o} -> o ≺ o
  tone-disc : ∀{o} -> disc ≺ o

-- NB. ≺ forms a Preorder but I haven't needed an instance for it... yet.

_≺?_ : ∀ o p -> Dec (o ≺ p)
mono ≺? mono = yes tone-refl
mono ≺? disc = no (λ ())
disc ≺? _ = yes tone-disc

data Class : Set where
  DEC SL FIN ACC ACC≤ : Class
  _,_ : Op Class

FIX FIX≤ : Class
FIX = DEC , SL , ACC
FIX≤ = DEC , SL , ACC≤

mutual
  infixr 6 _⊃_
  data Type : Set where
    bool : Type
    set : (a : Type) (p : Is DEC a) -> Type
    □ : Type -> Type
    _⊃_ _*_ _+_ : (a b : Type) -> Type

  Is : Class -> Type -> Set
  Is DEC = Dec!
  Is SL = SL!
  Is FIN = Fin!
  Is ACC = Acc!
  Is ACC≤ = Acc≤!
  Is (C , D) a = Is C a × Is D a

  data Dec! : Type -> Set where
    bool : Dec! bool
    set  : ∀{a} p -> Dec! (set a p)
    □    : ∀{a} (p : Dec! a) -> Dec! (□ a)
    _*_  : ∀{a} (p : Dec! a) {b} (q : Dec! b) -> Dec! (a * b)
    _+_  : ∀{a} (p : Dec! a) {b} (q : Dec! b) -> Dec! (a + b)

  data SL! : Type -> Set where
    bool : SL! bool
    set  : ∀ a {p} -> SL! (set a p)
    _*_  : ∀{a} (p : SL! a) {b} (q : SL! b) -> SL! (a * b)
    _⊃_  : ∀ a {b} (p : SL! b) -> SL! (a ⊃ b)

  data Fin! : Type -> Set where
    bool : Fin! bool
    set  : ∀{a p} -> Fin! a -> Fin! (set a p)
    _*_  : ∀{a} (p : Fin! a) {b} (q : Fin! b) -> Fin! (a * b)
    _+_  : ∀{a} (p : Fin! a) {b} (q : Fin! b) -> Fin! (a + b)
    -- could add a case for (a ⊃ b) here, but would never use it.

  data Acc! : Type -> Set where
    bool : Acc! bool
    set  : ∀{a p} -> Fin! a -> Acc! (set a p)
    □    : ∀ a -> Acc! (□ a)    -- do we need □ for ACC?
    _*_  : ∀{a} (p : Acc! a) {b} (q : Acc! b) -> Acc! (a * b)
    -- do we need + for ACC types?
    _+_  : ∀{a} (p : Acc! a) {b} (q : Acc! b) -> Acc! (a + b)

  data Acc≤! : Type -> Set where -- TODO

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
  when   : ∀{a} -> Is (DEC , SL) a -> term bool , term a ⊩ a
  -- sets and set-comprehension
  single : ∀{a} (p : Is DEC a) -> □ (term a) ⊩ set a p
  for-in : ∀{a b} (p : Is DEC a) (q : Is (DEC , SL) b)
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
  bottom : ∀{a} -> Is SL a -> nil ⊩ a
  join   : ∀{a} -> Is SL a -> term a , term a ⊩ a
  -- fixed points
  fix    : ∀{a} -> Is FIX a -> a is mono ▷ term a ⊩ a
  fix≤   : ∀{a} -> Is FIX≤ a -> term a , a is mono ▷ term a ⊩ a

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
