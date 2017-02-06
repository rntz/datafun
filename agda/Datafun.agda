open import Data.Bool
open import Data.Empty
open import Data.Maybe hiding (map)
open import Data.Maybe hiding (map)
open import Data.Nat hiding (_≤_; _≤?_)
open import Data.Product hiding (map)
open import Data.Sum hiding (map) renaming (inj₁ to car; inj₂ to cdr)
open import Data.Unit hiding (_≤_; _≤?_)
open import Function using (id; _∘_)
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Relation.Nullary using (¬_; Dec; yes; no)

-- ordering: disc < mono.
-- anticipated future additions: disc < anti.
data Tone : Set where disc : Tone; mono : Tone

_≤?_ : Tone -> Tone -> Bool
disc ≤? _ = true
mono ≤? mono = true
_ ≤? disc = false

_≤_ : Tone -> Tone -> Set
x ≤ y = (x ≤? y) ≡ true

infixr 4 _:->_
infixr 5 _:x_
data Type : Set where
  nat : Type
  _:->_ : Type -> Type -> Type
  _:x_ : Type -> Type -> Type
  □ : Type -> Type


---------- Environments ----------
Env : Set₁
Env = Tone -> Type -> Set

-- We have two possible choices of interpretation here:
--
-- 1. (X o a) means a variable with type `a` is in the context with tone `o`; or,
-- 2. (X o a) means a variable with type `a` is in the context with tone *at least* `o`.
--
-- That is to say, is X expected to preserve the subtone relationship? I.e, does this hold:
--
--     ∀(X : Env) (a : Type) -> X a disc -> X a mono
--
-- Currently we choose interpretation (1), becuase it simplifies constructing
-- Envs, but the other interpretation would simplify using them.

∅ : Env
∅ o a = ⊥

-- a singleton environment
infix 5 _is_
data _is_ (a : Type) (o : Tone) : Env where
  eq : (a is o) o a

infixr 4 _∪_
_∪_ : Env -> Env -> Env
(X ∪ Y) o a = X o a ⊎ Y o a

wipe : Env -> Env
wipe X disc a = X disc a
wipe X _ a = ⊥


---------- Terms ----------
infix 3 _⊢_
data _⊢_ (X : Env) : Type -> Set₁ where
  var : ∀ o {a} -> o ≤ mono -> X o a -> X ⊢ a
  nat : ℕ -> X ⊢ nat
  -- functions
  lam : ∀{a b} -> a is mono ∪ X ⊢ b -> X ⊢ a :-> b
  app : ∀{a b} -> X ⊢ a :-> b -> X ⊢ a -> X ⊢ b
  -- boxes
  box : ∀{a} -> wipe X ⊢ a -> X ⊢ □ a
  letbox : ∀{a b} -> X ⊢ □ a -> a is disc ∪ X ⊢ b -> X ⊢ b
  -- pairs
  -- pair : ∀{a b} -> X ⊢ a -> X ⊢ b -> X ⊢ a :x b
  -- proj : ∀{a b} -> (i : Bool) -> X ⊢ a :x b -> X ⊢ (if i then a else b)

infix 3 _⊢_at_
_⊢_at_ : Env -> Type -> Tone -> Set₁
X ⊢ a at mono = X ⊢ a
X ⊢ a at disc = wipe X ⊢ a


---------- Renamings ----------
infix 3 _⊆_
_⊆_ : Env -> Env -> Set
X ⊆ Y = ∀ o {a} -> X o a -> Y o a

cons/⊆ : ∀{X Y} o {a} -> X ⊆ Y -> (a is o ∪ X) ⊆ (a is o ∪ Y)
cons/⊆ _ f _ = [ car , cdr ∘ f _ ]

wipe/⊆ : ∀{X Y} -> X ⊆ Y -> wipe X ⊆ wipe Y
wipe/⊆ f disc = f disc
wipe/⊆ f mono ()

wipe⊆ : ∀{X} -> wipe X ⊆ X
wipe⊆ disc x = x
wipe⊆ mono ()

wipe-idem : ∀{X} -> wipe X ⊆ wipe (wipe X)
wipe-idem disc x = x
wipe-idem mono ()

cons⊆ : ∀ X o {a} -> X ⊆ (a is o ∪ X)
cons⊆ X o₁ o₂ = cdr

rename : ∀{X Y a} -> X ⊆ Y -> X ⊢ a -> Y ⊢ a
rename f (var o le x) = var o le (f o x)
rename f (nat x) = nat x
rename f (lam e) = lam (rename (cons/⊆ mono f) e)
rename f (app e e₁) = app (rename f e) (rename f e₁)
-- rename f (pair e e₁) = pair (rename f e) (rename f e₁)
-- rename f (proj i e) = proj i (rename f e)
rename f (box e) = box (rename (wipe/⊆ f) e)
rename f (letbox e e₁) = letbox (rename f e) (rename (cons/⊆ disc f) e₁)

rename-at : ∀{X Y} o {a} -> X ⊆ Y -> X ⊢ a at o -> Y ⊢ a at o
rename-at disc s x = rename (wipe/⊆ s) x
rename-at mono s x = rename s x

weaken : ∀{X a} o {b} -> X ⊢ a -> b is o ∪ X ⊢ a
weaken _ = rename (λ _ -> cdr)

weaken-at : ∀ o₁ {X a} o₂ {b} -> X ⊢ a at o₁ -> b is o₂ ∪ X ⊢ a at o₁
weaken-at disc {X} o = rename (wipe/⊆ (cons⊆ X o))
weaken-at mono = weaken


---------- Substitutions ----------
infix 4 _⇉_
_⇉_ : Env -> Env -> Set₁
X ⇉ Y = ∀ o {a} -> Y o a -> X ⊢ a at o

-- Not yet used.
-- cons⇉ : ∀{X Y} o {a} -> X ⊢ a is o -> X ⇉ Y -> X ⇉ a is o ∪ Y
-- cons⇉ = {!!}

cons/⇉ : ∀{X Y} o {a} -> X ⇉ Y -> (a is o ∪ X) ⇉ (a is o ∪ Y)
cons/⇉ disc s disc  (car eq) = var disc refl (car eq)
cons/⇉ mono s disc  (car ())
cons/⇉ .mono s mono (car eq) = var mono refl (car eq)
cons/⇉ o₁   s o₂    (cdr x) = weaken-at o₂ o₁ (s o₂ x)

wipe/⇉ : ∀{X Y} -> X ⇉ Y -> wipe X ⇉ wipe Y
wipe/⇉ s disc x = rename wipe-idem (s disc x)
wipe/⇉ s mono ()

sub : ∀{X Y a} -> X ⇉ Y -> Y ⊢ a -> X ⊢ a
sub s (var disc refl x) = rename wipe⊆ (s disc x)
sub s (var mono refl x) = s mono x
sub s (nat x) = nat x
sub s (lam e) = lam (sub (cons/⇉ mono s) e)
sub s (app e e₁) = app (sub s e) (sub s e₁)
-- sub s (pair e e₁) = pair (sub s e) (sub s e₁)
-- sub s (proj i e) = proj i (sub s e)
sub s (box e) = box (sub (wipe/⇉ s) e)
sub s (letbox e e₁) = letbox (sub s e) (sub (cons/⇉ disc s) e₁)


---------- Derivatives ----------
Δ : Type -> Type
Δ nat = nat
Δ (a :-> b) = □ a :-> Δ a :-> Δ b
Δ (a :x b) = Δ a :x Δ b
Δ (□ a) = □ (Δ a)

data Δ* (X : Env) : Env where
  orig : ∀ o {a} -> X o a -> Δ* X disc a
  deriv : ∀ {o a} -> X o a -> Δ* X o (Δ a)

wipeΔ*X⇉X : ∀{X} -> wipe (Δ* X) ⇉ X
wipeΔ*X⇉X disc x = var disc refl (orig disc x)
wipeΔ*X⇉X mono x = var disc refl (orig mono x)

Δ*X⇉X : ∀{X} -> Δ* X ⇉ X
Δ*X⇉X o x = rename-at o wipe⊆ (wipeΔ*X⇉X o x)

lam□ : ∀ {X a b} -> a is disc ∪ X ⊢ b -> X ⊢ □ a :-> b
lam□ M = lam (letbox (var mono refl (car eq))
                     (rename (λ o -> [ car , cdr ∘ cdr ]) M))

Δ*cons : ∀{X o a} -> Δ* (a is o ∪ X) ⊆ (Δ a is o) ∪ (a is disc) ∪ Δ* X
Δ*cons .disc (orig o (car eq)) = cdr (car eq)
Δ*cons .disc (orig o (cdr y)) = cdr (cdr (orig o y))
Δ*cons o (deriv (car eq)) = car eq
Δ*cons o (deriv (cdr y)) = cdr (cdr (deriv y))

static : ∀{X a} → X ⊢ a → Δ* X ⊢ a
static = sub Δ*X⇉X

static-box : ∀{X a} → X ⊢ a → Δ* X ⊢ □ a
static-box M = box (sub wipeΔ*X⇉X M)

Δ*-wipe-xchg : ∀{X} -> Δ* (wipe X) ⊆ wipe (Δ* X)
Δ*-wipe-xchg disc (orig disc x) = orig disc x
Δ*-wipe-xchg disc (orig mono ())
Δ*-wipe-xchg disc (deriv x) = deriv x
Δ*-wipe-xchg mono (deriv ())

δ : ∀{X a} -> X ⊢ a -> Δ* X ⊢ Δ a
δ (var o le x) = var o le (deriv x)
δ (nat x) = nat x
δ (lam e) = lam□ (lam (rename Δ*cons (δ e)))
δ (app e e₁) = app (app (δ e) (static-box e₁)) (δ e₁)
δ (box e) = box (rename Δ*-wipe-xchg (δ e))
δ (letbox M N) = letbox (static M)
                   (letbox (weaken disc (δ M))
                      (rename Δ*cons (δ N)))


-- Cx : Set₁
-- Cx = Set

-- data Var : Type -> Set where

-- mutual
--   data _⊢_ (X : Cx) : Type -> Set₁ where
--     nat : ℕ -> X ⊢ nat
--     app : ∀{a b} -> X ⊢ (a :-> b) -> X ⊢ a -> X ⊢ b
--     var : ∀{a} -> (X -> Var a) -> X ⊢ a
