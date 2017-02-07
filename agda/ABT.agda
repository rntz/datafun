open import Data.Bool hiding (_∨_; _∧_)
open import Data.Empty
open import Data.Maybe hiding (map)
open import Data.Maybe hiding (map)
open import Data.Nat hiding (_≤_; _≤?_)
open import Data.Product hiding (map)
open import Data.Sum hiding (map; [_,_]) renaming (inj₁ to car; inj₂ to cdr)
open import Data.Unit hiding (_≤_; _≤?_)
open import Function using (id; _∘_; const)
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Relation.Nullary using (¬_; Dec; yes; no)

-- ordering: disc < mono.
-- anticipated future additions: disc < anti.
data Tone : Set where
  mono : Tone
  disc : Tone

_≤?_ : Tone -> Tone -> Bool
disc ≤? _ = true
mono ≤? mono = true
_ ≤? disc = false

_≤_ : Tone -> Tone -> Set
x ≤ y = (x ≤? y) ≡ true

data Type : Set where
  bool  : Type
  _:x_  : (a b : Type) -> Type
  _:->_ : (a b : Type) -> Type
  □ : (a : Type) -> Type


---------- Contexts (or typing environments) ----------
Cx : Set₁
Cx = (o : Tone) (a : Type) -> Set

infix 5 _is_
data _is_ (a : Type) (o : Tone) : Cx where
  eq : (a is o) o a

infixr 4 _∪_
_∪_ : (X Y : Cx) -> Cx
(X ∪ Y) o a = X o a ⊎ Y o a

wipe : (X : Cx) -> Cx
wipe X mono t = ⊥
wipe X disc t = X disc t

infix 4 _at_
_at_ : Cx -> Tone -> Cx
X at mono = X
X at disc = wipe X


---------- Terms ----------
data Premise : Set where
  nil    : Premise
  _∧_    : (P Q : Premise) -> Premise
  ∙      : (a : Type) -> Premise
  _is_~_ : (a : Type) (o : Tone) (P : Premise) -> Premise
  □      : (P : Premise) -> Premise

infix 3 _⊃_
data _⊃_ : Premise -> Type -> Set where
  bool : Bool   -> nil ⊃ bool
  lam  : ∀{a b} -> (a is mono ~ ∙ b) ⊃ b
  app  : ∀{a b} -> ∙ (a :-> b) ∧ ∙ b ⊃ b
  box  : ∀{a}   -> □ (∙ a) ⊃ (□ a)
  let□ : ∀{a b} -> ∙ (□ a) ∧ (a is disc ~ ∙ b) ⊃ b

mutual
  infix 3 _⊩_
  data _⊩_ (X : Cx) : Premise -> Set where
    tt   : X ⊩ nil
    _,_  : ∀{P Q}   (p : X ⊩ P) (q : X ⊩ Q) -> X ⊩ P ∧ Q
    term : ∀{a}     (M : X ⊢ a)              -> X ⊩ ∙ a
    bind : ∀{P a o} (p : a is o ∪ X ⊩ P)     -> X ⊩ a is o ~ P
    -- Maybe we should instead have:
    --   ● : Tone -> Premise -> Premise
    --   tone : ∀ {P} o (p : X at o ⊩ P) -> X ⊩ ● o P
    --   X at mono ⊩ P = X ⊩ P
    --   X at disc ⊩ P = wipe X ⊩ P
    disc : ∀{P}     (p : wipe X ⊩ P)         -> X ⊩ □ P

  infix 3 _⊢_
  infix 3 _!_
  data _⊢_ (X : Cx) (a : Type) : Set where
    var : ∀ o -> o ≤ mono -> X o a -> X ⊢ a
    _!_ : ∀{P} (form : P ⊃ a) (args : X ⊩ P) -> X ⊢ a


-- Extracting a ⊩ into an ordinary value.
premise : Cx -> Premise -> Set
premise X nil = ⊤
premise X (P ∧ Q) = premise X P × premise X Q
premise X (∙ a) = X ⊢ a
premise X (a is o ~ P) = premise (a is o ∪ X) P
premise X (□ P) = premise (wipe X) P

un : ∀{X P} -> X ⊩ P -> premise X P
un tt = tt
un (p , q) = un p , un q
un (term M) = M
un (bind p) = un p
un (disc p) = un p

into : ∀{X P} -> premise X P -> X ⊩ P
into {P = nil} tt = tt
into {P = P ∧ Q} (x , y) = into x , into y
into {P = ∙ a} x = term x
into {P = a is o ~ P} x = bind (into x)
into {P = □ P} x = disc (into x)


---------- Context renamings ----------
infix 3 _⊆_
_⊆_ : (X Y : Cx) -> Set
X ⊆ Y = ∀ o {a} -> X o a -> Y o a

cons/⊆ : ∀{X Y o a} -> X ⊆ Y -> (a is o ∪ X) ⊆ (a is o ∪ Y)
cons/⊆ f _ (car x) = car x
cons/⊆ f _ (cdr x) = cdr (f _ x)

wipe/⊆ : ∀{X Y} -> X ⊆ Y -> wipe X ⊆ wipe Y
wipe/⊆ f mono ()
wipe/⊆ f disc = f disc

wipe⊆ : ∀{X} -> wipe X ⊆ X
wipe⊆ mono ()
wipe⊆ disc x = x

wipe-idem : ∀{X} -> wipe X ⊆ wipe (wipe X)
wipe-idem mono ()
wipe-idem disc x = x

drop : ∀{X Y} -> Y ⊆ X ∪ Y
drop o = cdr


---------- Applying context renamings to terms ----------
rename : ∀{X Y a} -> X ⊆ Y -> X ⊢ a -> Y ⊢ a
rename* : ∀{X Y P} -> X ⊆ Y -> X ⊩ P -> Y ⊩ P

rename f (var o le a) = var o le (f o a)
rename f (form ! x) = form ! rename* f x

rename* f tt = tt
rename* f (p , q) = rename* f p , rename* f q
rename* f (term M) = term (rename f M)
rename* f (bind p) = bind (rename* (cons/⊆ f) p)
rename* f (disc p) = disc (rename* (wipe/⊆ f) p)

rename-at : ∀{X Y} o {a} -> X ⊆ Y -> X at o ⊢ a -> Y at o ⊢ a
rename-at mono s M = rename s M
rename-at disc s M = rename (wipe/⊆ s) M
--rename-at disc s M = un (rename* s (disc (term M)))

weaken : ∀{X a o b} -> X ⊢ a -> b is o ∪ X ⊢ a
weaken = rename drop

weaken-at : ∀ o₁ {X a o b} -> X at o₁ ⊢ a -> (b is o ∪ X) at o₁ ⊢ a
weaken-at o = rename-at o drop


---------- Substitutions ----------
infix 4 _⇉_
_⇉_ : Cx -> Cx -> Set
X ⇉ Y = ∀ o {a} -> Y o a -> X at o ⊢ a

cons/⇉ : ∀{X Y} o {a} -> X ⇉ Y -> (a is o ∪ X) ⇉ (a is o ∪ Y)
cons/⇉ disc s disc  (car eq) = var disc refl (car eq)
cons/⇉ mono s disc  (car ())
cons/⇉ .mono s mono (car eq) = var mono refl (car eq)
cons/⇉ o₁   s o₂    (cdr x) = weaken-at o₂ (s o₂ x)
