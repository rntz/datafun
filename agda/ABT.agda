open import Data.Bool hiding (_∨_; _∧_)
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
data Tone : Set where
  mono : Tone
  disc : Tone

_≤?_ : Tone -> Tone -> Bool
disc ≤? _ = true
mono ≤? mono = true
_ ≤? disc = false

_≤_ : Tone -> Tone -> Set
x ≤ y = (x ≤? y) ≡ true

infixr 6 _:->_
infixr 7 _:x_ _:+_
data Type : Set where
  bool  : Type
  down  : (a : Type) -> Type
  _:x_  : (a b : Type) -> Type
  _:+_  : (a b : Type) -> Type
  _:->_ : (a b : Type) -> Type
  □ : (a : Type) -> Type

-- Type predicates
DEC : Type -> Set
DEC bool = ⊤
DEC (down a) = DEC a
DEC (_ :-> _) = ⊥
DEC (a :x b) = DEC a × DEC b
DEC (a :+ b) = DEC a × DEC b
DEC (□ a) = DEC a

SL : Type -> Set
SL bool = ⊤
SL (down _) = ⊤
SL (a :x b) = SL a × SL b
SL (a :+ b) = ⊥
SL (a :-> b) = SL b
SL (□ a) = ⊥

FIN : Type -> Set
FIN bool = ⊤
FIN (down a) = FIN a
FIN (a :x b) = FIN a × FIN b
FIN (a :+ b) = FIN a × FIN b
FIN (a :-> b) = ⊥
FIN (□ a) = FIN a

ACC : Type -> Set
ACC bool = ⊤
ACC (down a) = FIN a
ACC (a :x b) = ACC a × ACC b
ACC (a :+ b) = ACC a × ACC b
ACC (a :-> b) = ⊥
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
DEC? (a :x b) with DEC? a | DEC? b
... | just x | just y = just (x , y)
... | _ | _ = nothing
DEC? (a :+ b) with DEC? a | DEC? b
... | just x | just y = just (x , y)
... | _ | _ = nothing
DEC? (a :-> b) = nothing
DEC? (□ a) = DEC? a
DEC? (down a) = DEC? a


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
wipe X mono t = ⊥
wipe X disc t = X disc t

infix 4 _at_
_at_ : Cx -> Tone -> Cx
X at mono = X
X at disc = wipe X


---------- Terms, using a more strongly typed ABT-like abstraction ----------
infixr 4 _∧_
data Premise : Set where
  nil    : Premise
  _∧_    : (P Q : Premise) -> Premise
  ∙      : (a : Type) -> Premise
  _is_~_ : (a : Type) (o : Tone) (P : Premise) -> Premise
  □      : (P : Premise) -> Premise

-- Term formers.
infix 3 _⊃_
data _⊃_ : Premise -> Type -> Set where
  -- booleans
  bool : Bool   -> nil ⊃ bool
  if   : ∀{a}   -> ∙ (□ bool) ∧ ∙ a ∧ ∙ a ⊃ a
  when : ∀{a} (sl : SL a) -> ∙ bool ∧ ∙ a ⊃ a
  -- products
  pair : ∀{a b} -> ∙ a ∧ ∙ b ⊃ (a :x b)
  proj : ∀{a b} i -> ∙ (a :x b) ⊃ (if i then a else b)
  -- sums
  inj  : ∀{a b} i -> ∙ (if i then a else b) ⊃ a :+ b
  case : ∀{a b c} -> ∙ (a :+ b) ∧ (a is mono ~ ∙ c) ∧ (b is mono ~ ∙ c) ⊃ c
  splitsum : ∀{a b} -> ∙ (□ (a :+ b)) ⊃ □ a :+ □ b
  -- functions
  lam  : ∀{a b} -> (a is mono ~ ∙ b) ⊃ a :-> b
  app  : ∀{a b} -> ∙ (a :-> b) ∧ ∙ a ⊃ b
  -- boxes
  box  : ∀{a}   -> □ (∙ a) ⊃ (□ a)
  letbox : ∀{a b} -> ∙ (□ a) ∧ (a is disc ~ ∙ b) ⊃ b
  -- semilattices
  eps : ∀{a} -> SL a -> nil ⊃ a
  vee : ∀{a} -> SL a -> ∙ a ∧ ∙ a ⊃ a
  -- downsets
  single : ∀{a} -> (∙ a) ⊃ down a
  bigvee : ∀{a b} (dec : DEC a) (sl : SL b)
         -> ∙ (down a) ∧ (a is mono ~ ∙ b) ⊃ b
  -- fixed points
  fix : ∀{a} -> FIX a -> (a is mono ~ ∙ a) ⊃ a

mutual
  infix 3 _⊩_
  infixr 5 _~_
  data _⊩_ (X : Cx) : Premise -> Set where
    tt   : X ⊩ nil
    _,_  : ∀{P Q}   (p : X ⊩ P) (q : X ⊩ Q) -> X ⊩ P ∧ Q
    term : ∀{a}     (M : X ⊢ a)              -> X ⊩ ∙ a
    _~_  : ∀{P a} o (p : a is o ∪ X ⊩ P)     -> X ⊩ a is o ~ P
    -- Maybe we should instead have:
    --   ● : Tone -> Premise -> Premise
    --   at-tone : ∀ {P} o (p : X at o ⊩ P) -> X ⊩ ● o P
    disc : ∀{P}     (p : wipe X ⊩ P)         -> X ⊩ □ P

  infix 3 _⊢_
  infix 3 _!_
  data _⊢_ (X : Cx) (a : Type) : Set where
    var : ∀ o (p : o ≤ mono) (x : X o a) -> X ⊢ a
    _!_ : ∀{P} (form : P ⊃ a) (args : X ⊩ P) -> X ⊢ a


-- Pattern synonyms for terms.
pattern bool! b = bool b ! tt
pattern if! {a} M N₁ N₂ = if {a} ! term M , (term N₁ , term N₂)
pattern when! {a} sl M N = when {a} sl ! term M , term N
pattern pair! {a b} M N = pair {a}{b} ! term M , term N
pattern proj! {a b} i M = proj {a}{b} i ! term M
pattern inj! {a b} i M = inj {a}{b} i ! term M
pattern case! {a b c} M N₁ N₂ = case {a}{b}{c} ! term M , ((.mono ~ term N₁) , (.mono ~ term N₂))
pattern splitsum! {a b} M = splitsum {a}{b} ! term M
pattern lam! {a b} M = lam {a}{b} ! (.mono ~ term M)
pattern app! {a b} M N = app {a}{b} ! term M , term N
pattern box! {a} M = box {a} ! disc (term M)
pattern letbox! {a b} M N = letbox {a}{b} ! term M , (.disc ~ term N)
pattern eps! {a} sl = eps {a} sl ! tt
pattern vee! {a} sl M N = vee {a} sl ! term M , term N
pattern single! {a} M = single {a} ! term M
pattern bigvee! {a b} dec sl M N = bigvee {a}{b} dec sl ! term M , (.mono ~ term N)
pattern fix! {a} p M = fix {a} p ! (.mono ~ term M)


-- Extracting a ⊩ into an ordinary value.
-- TODO: is this useful for anything?
-- premise : Cx -> Premise -> Set
-- premise X nil = ⊤
-- premise X (P ∧ Q) = premise X P × premise X Q
-- premise X (∙ a) = X ⊢ a
-- premise X (a is o ~ P) = premise (a is o ∪ X) P
-- premise X (□ P) = premise (wipe X) P

-- un : ∀{X P} -> X ⊩ P -> premise X P
-- un tt = tt
-- un (p , q) = un p , un q
-- un (term M) = M
-- un (_ ~ p) = un p
-- un (disc p) = un p

-- into : ∀{X P} -> premise X P -> X ⊩ P
-- into {P = nil} tt = tt
-- into {P = P ∧ Q} (x , y) = into x , into y
-- into {P = ∙ a} x = term x
-- into {P = a is o ~ P} x = o ~ into x
-- into {P = □ P} x = disc (into x)


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
rename* f (o ~ p) = o ~ rename* (cons/⊆ f) p
rename* f (disc p) = disc (rename* (wipe/⊆ f) p)

rename-at : ∀{X Y} o {a} -> X ⊆ Y -> X at o ⊢ a -> Y at o ⊢ a
rename-at mono f M = rename f M
rename-at disc f M = rename (wipe/⊆ f) M

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

wipe/⇉ : ∀{X Y} -> X ⇉ Y -> wipe X ⇉ wipe Y
wipe/⇉ s disc x = rename wipe-idem (s disc x)
wipe/⇉ s mono ()

sub : ∀{X Y a} -> X ⇉ Y -> Y ⊢ a -> X ⊢ a
sub* : ∀{X Y P} -> X ⇉ Y -> Y ⊩ P -> X ⊩ P

sub σ (var mono refl x) = σ mono x
sub σ (var disc refl x) = rename wipe⊆ (σ disc x)
sub σ (form ! args) = form ! sub* σ args

sub* σ tt = tt
sub* σ (p , q) = sub* σ p , sub* σ q
sub* σ (term M) = term (sub σ M)
sub* σ (o ~ p) = o ~ sub* (cons/⇉ o σ) p
sub* σ (disc p) = disc (sub* (wipe/⇉ σ) p)


---------- Change types ----------
Δ : Type -> Type
Δ bool = bool
Δ (down a) = down a
Δ (a :x b) = Δ a :x Δ b
Δ (a :+ b) = Δ a :+ Δ b
Δ (a :-> b) = □ a :-> (Δ a :-> Δ b)
Δ (□ a) = □ (Δ a)

ΔSL∈SL : ∀ a -> SL a -> SL (Δ a)
ΔSL∈SL bool tt = tt
ΔSL∈SL (down a) tt = tt
ΔSL∈SL (a :x b) (asl , bsl) = ΔSL∈SL a asl , ΔSL∈SL b bsl
ΔSL∈SL (a :+ b) ()
ΔSL∈SL (a :-> b) sl = ΔSL∈SL b sl
ΔSL∈SL (□ a) ()

DEC∧SL⊃Δ=id : ∀ a -> DEC a -> SL a -> Δ a ≡ a
DEC∧SL⊃Δ=id bool dec sl = refl
DEC∧SL⊃Δ=id (down a) dec sl = refl
DEC∧SL⊃Δ=id (a :x b) (adec , bdec) (asl , bsl)
  rewrite DEC∧SL⊃Δ=id a adec asl
        | DEC∧SL⊃Δ=id b bdec bsl = refl
DEC∧SL⊃Δ=id (a :+ b) _ ()
DEC∧SL⊃Δ=id (a :-> b) () sl
DEC∧SL⊃Δ=id (□ a) dec ()


---------- Change environments ----------
data Δ* (X : Cx) : Cx where
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
_⊢δ_ : Cx -> Type -> Set
X ⊢δ a = X ⊢ a × Δ* X ⊢ Δ a

lam□ : ∀ {X a b} -> a is disc ∪ X ⊢ b -> X ⊢ (□ a) :-> b
lam□ M = lam! (letbox! (var mono refl (car eq))
                (rename (λ o -> [ car , cdr ∘ cdr ]) M))

static : ∀{X a} → X ⊢ a → Δ* X ⊢ a
static = sub Δ*X⇉X

static□ : ∀{X a} → X ⊢ a → Δ* X ⊢ □ a
static□ M = box! (sub wipeΔ*X⇉X M)

-- lamδ : ∀{X a b} -> Δ* (a is mono ∪ X) ⊢ Δ b -> Δ* X ⊢ Δ (a :-> b)
-- lamδ dM = lam□ (lam (rename Δ*cons dM))

-- whenδ-DEC : ∀{X} a -> DEC a -> SL a -> X ⊢δ bool -> X ⊢δ a -> Δ* X ⊢ Δ a
-- whenδ-DEC {X} a dec sl (M , dM) (N , dN)
--   = if (static-box M) dN
--        (subst (λ a₁ → Δ* X ⊢ a₁) (sym (DEC∧SL⊃Δ=id a dec sl))
--          (when sl dM {!vee ? N dN!}))

-- whenδ : ∀ {X} a -> SL a -> X ⊢δ bool -> X ⊢δ a -> Δ* X ⊢ Δ a
-- whenδ bool sl MdM NdN = whenδ-DEC bool tt tt MdM NdN
-- whenδ (a :-> b) sl (M , dM) (N , dN)
--   = lamδ (whenδ b sl
--             (weaken M , rename (Δ*/⊆ drop) dM)
--             ( app (weaken N) (var mono refl (car eq))
--             -- ugh, why do I need to write this. is there a better way?
--             , {!!} ))
-- whenδ (a :x b) (ap , bp) M N = {!!}
-- whenδ (□ a) () M N


---------- δ itself ----------
δ : ∀{X a} -> X ⊢ a -> Δ* X ⊢ Δ a
δ (var o p x) = var o p (deriv x)
δ (bool! x) = bool! x
δ (if! M N₁ N₂) = if! (static M) (δ N₁) (δ N₂)
δ (when! sl M N) = {!!}
δ (pair! M N) = pair! (δ M) (δ N)
δ (proj! true M) = proj! true (δ M)
δ (proj! false M) = proj! false (δ M)
δ (inj! true M) = inj! true (δ M)
δ (inj! false M) = inj! false (δ M)
δ (case! M N₁ N₂) = {!!}
δ (splitsum! M) = splitsum! (δ M)
δ (lam! M) = lam□ (lam! (rename Δ*cons (δ M)))
δ (app! M N) = app! (app! (δ M) (static□ N)) (δ N)
δ (box! M) = box! (rename Δ*-wipe-xchg (δ M))
δ (letbox! M N) = letbox! (static M) (letbox! (weaken (δ M)) (rename Δ*cons (δ N)))
-- At (eps : a :-> b), is our derivative still eps? it is the derivative of the
-- constant zero function. Is that also the constant zero function? Yes,
-- inductively. TODO: put proof of this into seminaive.tex.
δ (eps! {a} sl) = eps! (ΔSL∈SL a sl)
-- The critical overapproximation.
δ (vee! {a} sl M N) = vee! (ΔSL∈SL a sl) (δ M) (δ N)
δ (single! M) = eps! tt
-- The whopper.
δ (bigvee! dec sl M N) = {!!}
-- The purpose of the whole thing.
δ (fix! {a} p M) = {!!}
