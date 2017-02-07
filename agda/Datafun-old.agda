open import Data.Bool
open import Data.Empty
open import Data.Maybe hiding (map)
open import Data.Maybe hiding (map)
open import Data.Nat hiding (_≤_; _≤?_)
open import Data.Product hiding (map)
open import Data.Sum hiding (map) renaming (inj₁ to car; inj₂ to cdr)
open import Data.Unit hiding (_≤_; _≤?_)
open import Function using (id; _∘_; const)
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
  bool : Type
  _:->_ : Type -> Type -> Type
  _:x_ : Type -> Type -> Type
  □ : Type -> Type

-- Type predicates
DEC : Type -> Set
DEC bool = ⊤
DEC (_ :-> _) = ⊥
DEC (a :x b) = DEC a × DEC b
DEC (□ t) = DEC t

SL : Type -> Set
SL bool = ⊤
SL (a :-> b) = SL b
SL (a :x b) = SL a × SL b
SL (□ t) = ⊥

ACC : Type -> Set
ACC bool = ⊤
ACC (a :-> b) = ⊥
ACC (a :x b) = ACC a × ACC b
ACC (□ a) = ⊤

FIX : Type -> Set
FIX a = ACC a × DEC a × SL a

-- Deciding type predicates. Currently only semi-deciding: that is, we prove
-- that if we answer "yes" then the type does have the property, but not
-- vice-versa.
--
-- Maybe I should use Dec for this, and fully prove LEM for these properties?
DEC? : ∀ a -> Maybe (DEC a)
DEC? bool = just tt
DEC? (a :-> b) = nothing
DEC? (a :x b) with DEC? a | DEC? b
... | just x | just y = just (x , y)
... | _ | _ = nothing
DEC? (□ a) = DEC? a


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

infix 4 _at_
_at_ : Env -> Tone -> Env
X at mono = X
X at disc = wipe X


---------- Terms ----------
infix 3 _⊢_
data _⊢_ (X : Env) : Type -> Set where
  var : ∀ o {a} -> o ≤ mono -> X o a -> X ⊢ a

  -- functions
  lam : ∀{a b} -> a is mono ∪ X ⊢ b -> X ⊢ a :-> b
  app : ∀{a b} -> X ⊢ a :-> b -> X ⊢ a -> X ⊢ b

  -- boxes
  box : ∀{a} -> wipe X ⊢ a -> X ⊢ □ a
  letbox : ∀{a b} -> X ⊢ □ a -> a is disc ∪ X ⊢ b -> X ⊢ b

  -- pairs are boring so we omit them
  -- pair : ∀{a b} -> X ⊢ a -> X ⊢ b -> X ⊢ a :x b
  -- proj : ∀{a b} -> (i : Bool) -> X ⊢ a :x b -> X ⊢ (if i then a else b)

  -- semilattices
  eps : ∀{a} -> SL a -> X ⊢ a
  vee : ∀{a} -> SL a -> X ⊢ a -> X ⊢ a -> X ⊢ a

  -- booleans
  bool : Bool -> X ⊢ bool
  if : ∀{a} -> X ⊢ □ bool -> X ⊢ a -> X ⊢ a -> X ⊢ a
  when : ∀{a} -> SL a -> X ⊢ bool -> X ⊢ a -> X ⊢ a

  -- TODO: fixed points


---------- Renamings ----------
infix 3 _⊆_
_⊆_ : Env -> Env -> Set
X ⊆ Y = ∀ o {a} -> X o a -> Y o a

cons/⊆ : ∀{X Y o a} -> X ⊆ Y -> (a is o ∪ X) ⊆ (a is o ∪ Y)
cons/⊆ f _ = [ car , cdr ∘ f _ ]

wipe/⊆ : ∀{X Y} -> X ⊆ Y -> wipe X ⊆ wipe Y
wipe/⊆ f disc = f disc
wipe/⊆ f mono ()

wipe⊆ : ∀{X} -> wipe X ⊆ X
wipe⊆ disc x = x
wipe⊆ mono ()

wipe-idem : ∀{X} -> wipe X ⊆ wipe (wipe X)
wipe-idem disc x = x
wipe-idem mono ()

drop : ∀{X Y} -> Y ⊆ X ∪ Y
drop o = cdr

rename : ∀{X Y a} -> X ⊆ Y -> X ⊢ a -> Y ⊢ a
rename f (var o le x) = var o le (f o x)
rename f (lam e) = lam (rename (cons/⊆ f) e)
rename f (app e e₁) = app (rename f e) (rename f e₁)
-- rename f (pair e e₁) = pair (rename f e) (rename f e₁)
-- rename f (proj i e) = proj i (rename f e)
rename f (box e) = box (rename (wipe/⊆ f) e)
rename f (letbox e e₁) = letbox (rename f e) (rename (cons/⊆ f) e₁)
rename f (eps sl) = eps sl
rename f (vee sl M N) = vee sl (rename f M) (rename f N)
rename f (bool x) = bool x
rename f (if M N₁ N₂) = if (rename f M) (rename f N₁) (rename f N₂)
rename f (when p M N) = when p (rename f M) (rename f N)

rename-at : ∀{X Y} o {a} -> X ⊆ Y -> X at o ⊢ a -> Y at o ⊢ a
rename-at disc s x = rename (wipe/⊆ s) x
rename-at mono s x = rename s x

weaken : ∀{X a o b} -> X ⊢ a -> b is o ∪ X ⊢ a
weaken = rename drop

weaken-at : ∀ o₁ {X a o b} -> X at o₁ ⊢ a -> (b is o ∪ X) at o₁ ⊢ a
weaken-at o = rename-at o drop


---------- Substitutions ----------
infix 4 _⇉_
_⇉_ : Env -> Env -> Set
X ⇉ Y = ∀ o {a} -> Y o a -> X at o ⊢ a

-- Not yet used.
-- cons⇉ : ∀{X Y} o {a} -> X ⊢ a is o -> X ⇉ Y -> X ⇉ a is o ∪ Y
-- cons⇉ = {!!}

cons/⇉ : ∀{X Y} o {a} -> X ⇉ Y -> (a is o ∪ X) ⇉ (a is o ∪ Y)
cons/⇉ disc s disc  (car eq) = var disc refl (car eq)
cons/⇉ mono s disc  (car ())
cons/⇉ .mono s mono (car eq) = var mono refl (car eq)
cons/⇉ o₁   s o₂    (cdr x) = weaken-at o₂ (s o₂ x)

wipe/⇉ : ∀{X Y} -> X ⇉ Y -> wipe X ⇉ wipe Y
wipe/⇉ s disc x = rename wipe-idem (s disc x)
wipe/⇉ s mono ()

sub : ∀{X Y a} -> X ⇉ Y -> Y ⊢ a -> X ⊢ a
sub s (var disc refl x) = rename wipe⊆ (s disc x)
sub s (var mono refl x) = s mono x
sub s (lam e) = lam (sub (cons/⇉ mono s) e)
sub s (app e e₁) = app (sub s e) (sub s e₁)
-- sub s (pair e e₁) = pair (sub s e) (sub s e₁)
-- sub s (proj i e) = proj i (sub s e)
sub s (box e) = box (sub (wipe/⇉ s) e)
sub s (letbox e e₁) = letbox (sub s e) (sub (cons/⇉ disc s) e₁)
sub s (eps sl) = eps sl
sub s (vee sl M N) = vee sl (sub s M) (sub s N)
sub s (bool x) = bool x
sub s (if M N₁ N₂) = if (sub s M) (sub s N₁) (sub s N₂)
sub s (when p M N) = when p (sub s M) (sub s N)


---------- Change types ----------
Δ : Type -> Type
Δ bool = bool
Δ (a :-> b) = □ a :-> Δ a :-> Δ b
Δ (a :x b) = Δ a :x Δ b
Δ (□ a) = □ (Δ a)

ΔSL∈SL : ∀ a -> SL a -> SL (Δ a)
ΔSL∈SL bool tt = tt
ΔSL∈SL (a :-> b) sl = ΔSL∈SL b sl
ΔSL∈SL (a :x b) (asl , bsl) = ΔSL∈SL a asl , ΔSL∈SL b bsl
ΔSL∈SL (□ a) ()

DEC∧SL⊃Δ=id : ∀ a -> DEC a -> SL a -> Δ a ≡ a
DEC∧SL⊃Δ=id bool dec sl = refl
DEC∧SL⊃Δ=id (a :-> b) () sl
DEC∧SL⊃Δ=id (a :x b) (adec , bdec) (asl , bsl)
  rewrite DEC∧SL⊃Δ=id a adec asl
        | DEC∧SL⊃Δ=id b bdec bsl = refl
DEC∧SL⊃Δ=id (□ a) dec ()


---------- Change environments ----------
data Δ* (X : Env) : Env where
  orig  : ∀ o {a} -> X o a -> Δ* X disc a
  deriv : ∀ {o a} -> X o a -> Δ* X o (Δ a)

wipeΔ*X⇉X : ∀{X} -> wipe (Δ* X) ⇉ X
wipeΔ*X⇉X disc x = var disc refl (orig disc x)
wipeΔ*X⇉X mono x = var disc refl (orig mono x)

Δ*X⇉X : ∀{X} -> Δ* X ⇉ X
Δ*X⇉X o x = rename-at o wipe⊆ (wipeΔ*X⇉X o x)

Δ*/⊆ : ∀{X Y} -> X ⊆ Y -> Δ* X ⊆ Δ* Y
Δ*/⊆ f disc (orig o x) = orig o (f o x)
Δ*/⊆ f o (deriv x) = deriv (f o x)

Δ*cons : ∀{X o a} -> Δ* (a is o ∪ X) ⊆ (Δ a is o) ∪ (a is disc) ∪ Δ* X
Δ*cons .disc (orig o (car eq)) = cdr (car eq)
Δ*cons .disc (orig o (cdr y)) = cdr (cdr (orig o y))
Δ*cons o (deriv (car eq)) = car eq
Δ*cons o (deriv (cdr y)) = cdr (cdr (deriv y))

Δ*-wipe-xchg : ∀{X} -> Δ* (wipe X) ⊆ wipe (Δ* X)
Δ*-wipe-xchg disc (orig disc x) = orig disc x
Δ*-wipe-xchg disc (orig mono ())
Δ*-wipe-xchg disc (deriv x) = deriv x
Δ*-wipe-xchg mono (deriv ())


---------- Helpers for δ ----------

-- A pair of a term and its derivative.
_⊢δ_ : Env -> Type -> Set
X ⊢δ a = X ⊢ a × Δ* X ⊢ Δ a

lam□ : ∀ {X a b} -> a is disc ∪ X ⊢ b -> X ⊢ □ a :-> b
lam□ M = lam (letbox (var mono refl (car eq))
                     (rename (λ o -> [ car , cdr ∘ cdr ]) M))

static : ∀{X a} → X ⊢ a → Δ* X ⊢ a
static = sub Δ*X⇉X

static-box : ∀{X a} → X ⊢ a → Δ* X ⊢ □ a
static-box M = box (sub wipeΔ*X⇉X M)

lamδ : ∀{X a b} -> Δ* (a is mono ∪ X) ⊢ Δ b -> Δ* X ⊢ Δ (a :-> b)
lamδ dM = lam□ (lam (rename Δ*cons dM))

whenδ-DEC : ∀{X} a -> DEC a -> SL a -> X ⊢δ bool -> X ⊢δ a -> Δ* X ⊢ Δ a
whenδ-DEC {X} a dec sl (M , dM) (N , dN)
  = if (static-box M) dN
       (subst (λ a₁ → Δ* X ⊢ a₁) (sym (DEC∧SL⊃Δ=id a dec sl))
         (when sl dM {!vee ? N dN!}))

whenδ : ∀ {X} a -> SL a -> X ⊢δ bool -> X ⊢δ a -> Δ* X ⊢ Δ a
whenδ bool sl MdM NdN = whenδ-DEC bool tt tt MdM NdN
whenδ (a :-> b) sl (M , dM) (N , dN)
  = lamδ (whenδ b sl
            (weaken M , rename (Δ*/⊆ drop) dM)
            ( app (weaken N) (var mono refl (car eq))
            -- ugh, why do I need to write this. is there a better way?
            , {!!} ))
whenδ (a :x b) (ap , bp) M N = {!!}
whenδ (□ a) () M N


---------- δ itself ----------
δ : ∀{X a} -> X ⊢ a -> Δ* X ⊢ Δ a
δ (var o le x) = var o le (deriv x)
δ (lam M) = lamδ (δ M)
δ (app e e₁) = app (app (δ e) (static-box e₁)) (δ e₁)
δ (box e) = box (rename Δ*-wipe-xchg (δ e))
δ (letbox M N) = letbox (static M)
                   (letbox (weaken (δ M))
                      (rename Δ*cons (δ N)))
-- NB. if {a = a :-> b}, then is our derivative still eps? it is the derivative
-- of the constant zero function. is that also the constant zero function?
δ (eps {a} sl) = {!!}
δ (vee {a} sl M N) = vee (ΔSL∈SL a sl) (δ M) (δ N)
δ (bool x) = bool x
δ (if M N₁ N₂) = if (static M) (δ N₁) (δ N₂)
-- Here we need to induct on types!
δ {a = a} (when sl M N) = whenδ a sl (M , δ M) (N , δ N)
-- δ {a = bool}        (when tt M N) = whenδ-DEC bool tt tt M N
-- δ {a = a :-> b}     (when bp M N)
--   = lamδ (δ {a = b} (when bp (weaken M) (app (weaken N) (var mono refl (car eq)))))
-- δ {a = a :x b}      (when (ap , bp) M N) = {!!}
-- δ {a = □ a} (when () M N)
