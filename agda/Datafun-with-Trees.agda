module Datafun-with-Trees where

open import Prelude
open import Cat
open import Monads

 ---------- Modes ----------
data Mode : Set where mono disc : Mode

data _≺_ : (o p : Mode) -> Set where
  refl≺ : ∀{o} -> o ≺ o
  disc≺ : ∀{o} -> disc ≺ o

instance
  modes : Proset
  Obj modes = Mode
  Hom modes = _≺_
  ident modes = refl≺
  compo modes refl≺ b = b
  compo modes disc≺ b = disc≺

mode⇒tone : ∀{i} → Fun modes (tones {i}{i})
ap mode⇒tone mono = tone-id
ap mode⇒tone disc = tone-iso
map mode⇒tone refl≺ = id
map mode⇒tone {disc} {mono} disc≺ = fun proj₁
map mode⇒tone {disc} {disc} disc≺ = id

_≺?_ : ∀ o p -> Dec (o ≺ p)
mono ≺? mono = yes refl≺
mono ≺? disc = no (λ ())
disc ≺? _ = yes disc≺

 ---------- Types and typeclasses ----------
data Class : Set where
  _,_ : BinOp Class
  DEC SL FIN ACC ACC≤ : Class

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
  Is (C , D) a = Is C a × Is D a
  Is DEC = Dec!
  Is SL = SL!
  Is FIN = Fin!
  Is ACC = Acc!
  Is ACC≤ = Acc≤!

  data Dec! : Type -> Set where
    bool : Dec! bool
    set  : ∀ a p -> Dec! (set a p)
    □    : ∀ a (p : Dec! a) -> Dec! (□ a)
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
instance
  hyps : Proset
  hyps = op modes ∧ discrete Type

open import TreeSet
open Trees (hyps) using () renaming (trees to cxs) public
instance -cxs = cxs
Cx = Obj cxs

hyp : Mode × Type → Cx
hyp = leaf

-- Singleton context.
infix 7 _is_
_is_ : Type -> Mode -> Cx
a is o = leaf (o , a)

todisc : hyps ⇒ hyps
ap todisc = map∧ (const disc) id
map todisc = map∧ (const id) id

-- Wipe is a monad on contexts that makes all variables discrete.
Wipe : cxs ≤ cxs
Wipe = tree-map todisc

instance
  Wipe-monad : Monad Wipe
  Monad.join Wipe-monad {empty} = empty≤
  Monad.join Wipe-monad {leaf x} = leaf≤ (refl≺ , refl)
  Monad.join Wipe-monad {node X Y} = map∨ (join Wipe) (join Wipe)
  Monad.pure Wipe-monad {empty} = empty≤
  Monad.pure Wipe-monad {leaf x} = leaf≤ (disc≺ , refl)
  Monad.pure Wipe-monad {node X Y} = map∨ (pure Wipe) (pure Wipe)

wipe : Cx -> Cx
wipe = ap Wipe

 ---------- ABTs ----------
infix  1 _⊩_ _⊢_ _!_
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
  --     d(empty) = d(λx. empty) = λx dx. d(empty) = λ x dx. empty = empty
  --
  --     d(f ∨ g) = d(λx. f x ∨ g x)
  --              = λx dx. d(f x ∨ g x)
  --              = λx dx. df x dx ∨ dg x dx
  --              = df v dg
  --
  -- So it looks like no.
  empty : ∀{a} -> Is SL a -> nil ⊩ a
  -- TODO: rename this? it collides with Monad.join.
  lub-of : ∀{a} -> Is SL a -> term a , term a ⊩ a
  -- fixed points
  fix    : ∀{a} -> Is FIX a -> a is mono ▷ term a ⊩ a
  fix≤   : ∀{a} -> Is FIX≤ a -> term a , a is mono ▷ term a ⊩ a

data _⊢_ : (X : Cx) → Premise -> Set1 where
  tt   : ∀{X} → X ⊢ nil
  _,_  : ∀{X P Q} (M : X ⊢ P) (N : X ⊢ Q) -> X ⊢ P , Q
  bind : ∀{X P Y} (M : Y ∨ X ⊢ P) -> X ⊢ Y ▷ P
  box  : ∀{X P}   (M : X ⊢ P) -> wipe X ⊢ □ P
  -- terms
  _!_ : ∀{X P a} (form : P ⊩ a) (args : X ⊢ P) -> X ⊢ term a
  var : ∀{X a} o (p : (o , a) ∈ X) -> X ⊢ term a

--  -- Pattern synonyms for terms.
-- -- pattern lam! {a b} M        = lam {a}{b} ! bind M
-- -- pattern app! {a b} M N      = app {a}{b} ! M , N
-- -- pattern box! {a} M          = box {a} ! box M
-- -- pattern letbox! {a b} M N   = letbox {a}{b} ! M , bind N

 ---------- Renaming terms ----------
rename : ∀{X Y P} -> X ≤ Y -> X ⊢ P -> Y ⊢ P
rename f tt         = tt
rename f (M , N)    = rename f M , rename f N
rename f (bind M)   = bind (rename (map∨₂ f) M)
--rename f (box M)    = box (rename (map Wipe f) M)

-- this look hard. argh.
-- oh fuck, it's actually impossible! FUUUUUCK.
rename {._} {Y} {P} f (box {X} M) = {!X!}
rename f (form ! M) = form ! rename f M
--rename f (var o p)  = var o (f (o , _) p)
rename f (var o p)  = var o (p ∙ f)
-- rename f (var o p) = var o (≤→∈ (∈→≤ p ∙ f))

-- rename-at : ∀{X Y} o {a} -> X ≤ Y -> X at o ⊢ a -> Y at o ⊢ a
-- rename-at mono f M = rename f M
-- rename-at disc f M = rename (map Wipe f) M

 ---------- TODO: Substitutions ----------
