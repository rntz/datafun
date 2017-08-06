open import Prelude hiding ([_,_])
open import Data.Sum hiding (map) renaming (inj₁ to car; inj₂ to cdr)

open Eq hiding ([_])

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

mutual
  infixr 6 _:->_
  infixr 7 _:x_ _:+_
  data Type : Set where
    bool : Type
    down : (a : Type) -> DEC a -> Type
    _:x_ _:+_ _:->_ : (a b : Type) -> Type
    □ : (a : Type) -> Type

  -- Type predicates
  DEC : Type -> Set
  DEC bool = ⊤
  DEC (down a _) = DEC a
  DEC (_ :-> _) = ⊥
  DEC (a :x b) = DEC a × DEC b
  DEC (a :+ b) = DEC a × DEC b
  DEC (□ a) = DEC a

SL : Type -> Set
SL bool = ⊤
SL (down _ _) = ⊤
SL (a :x b) = SL a × SL b
SL (a :+ b) = ⊥
SL (a :-> b) = SL b
SL (□ a) = ⊥

FIN : Type -> Set
FIN bool = ⊤
FIN (down a _) = FIN a
FIN (a :x b) = FIN a × FIN b
FIN (a :+ b) = FIN a × FIN b
FIN (a :-> b) = ⊥
FIN (□ a) = FIN a

ACC : Type -> Set
ACC bool = ⊤
ACC (down a _) = FIN a
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
DEC? (down a _) = DEC? a


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


---------- Context renamings ----------
infix 3 _⊆_
_⊆_ : (X Y : Cx) -> Set
X ⊆ Y = ∀ o {a} -> X o a -> Y o a

wipe/⊆ : ∀{X Y} -> X ⊆ Y -> wipe X ⊆ wipe Y
wipe/⊆ f mono ()
wipe/⊆ f disc = f disc

-- Is `wipe` a comonad in the category of contexts and renamings?
wipe⊆ : ∀{X} -> wipe X ⊆ X
wipe⊆ mono ()
wipe⊆ disc x = x

wipe-idem : ∀{X} -> wipe X ⊆ wipe (wipe X)
wipe-idem mono ()
wipe-idem disc x = x

drop : ∀{X Y} -> Y ⊆ X ∪ Y
drop o = cdr

drop2 : ∀{X Y Z} -> Z ⊆ X ∪ Y ∪ Z
drop2 o = cdr ∘ cdr

∪/⊆ : ∀{X Y Z} -> X ⊆ Y -> (Z ∪ X) ⊆ (Z ∪ Y)
∪/⊆ f _ = [ car , cdr ∘ f _ ]

drop-mid : ∀{X Y Z} -> X ∪ Z ⊆ X ∪ Y ∪ Z
drop-mid o = [ car , cdr ∘ cdr ]


---------- Terms, using a more strongly typed ABT-like abstraction ----------
infixr 4 _∧_
infixr 4 _~_
data Premise : Set₁ where
  nil    : Premise
  _∧_    : (P Q : Premise) -> Premise
  ∙      : (a : Type) -> Premise
  _~_    : (X : Cx) (P : Premise) -> Premise
  □      : (P : Premise) -> Premise

-- Term formers.
infix 3 _⊃_
data _⊃_ : Premise -> Type -> Set where
  -- booleans
  ⊃bool : Bool   -> nil ⊃ bool
  ⊃if   : ∀{a}   -> ∙ (□ bool) ∧ ∙ a ∧ ∙ a ⊃ a
  ⊃when : ∀{a} (sl : SL a) -> ∙ bool ∧ ∙ a ⊃ a
  -- products
  ⊃pair : ∀{a b} -> ∙ a ∧ ∙ b ⊃ (a :x b)
  ⊃proj : ∀{a b} i -> ∙ (a :x b) ⊃ (if i then a else b)
  -- sums
  ⊃inj  : ∀{a b} i -> ∙ (if i then a else b) ⊃ a :+ b
  ⊃case : ∀{a b c} -> ∙ (a :+ b) ∧ (a is mono ~ ∙ c) ∧ (b is mono ~ ∙ c) ⊃ c
  ⊃splitsum : ∀{a b} -> ∙ (□ (a :+ b)) ⊃ □ a :+ □ b
  -- functions
  ⊃lam  : ∀{a b} -> (a is mono ~ ∙ b) ⊃ a :-> b
  ⊃app  : ∀{a b} -> ∙ (a :-> b) ∧ ∙ a ⊃ b
  -- boxes
  ⊃box  : ∀{a}   -> □ (∙ a) ⊃ (□ a)
  ⊃letbox : ∀{a b} -> ∙ (□ a) ∧ (a is disc ~ (∙ b)) ⊃ b
  -- semilattices
  ⊃eps : ∀{a} -> SL a -> nil ⊃ a
  ⊃vee : ∀{a} -> SL a -> ∙ a ∧ ∙ a ⊃ a
  -- downsets
  ⊃single : ∀{a}{p : DEC a} -> (∙ a) ⊃ down a p
  ⊃bigvee : ∀{a b} {dec : DEC a} (sl : SL b)
          -> ∙ (down a dec) ∧ (a is mono ~ ∙ b) ⊃ b
  -- fixed points
  ⊃fix : ∀{a} -> FIX a -> (a is mono ~ ∙ a) ⊃ a

mutual
  infix 3 _⊩_
  data _⊩_ (X : Cx) : Premise -> Set₁ where
    tt   : X ⊩ nil
    _,_  : ∀{P Q}   (p : X ⊩ P) (q : X ⊩ Q) -> X ⊩ P ∧ Q
    term : ∀{a}     (M : X ⊢ a)              -> X ⊩ ∙ a
    bind : ∀{P Y}   (p : Y ∪ X ⊩ P)          -> X ⊩ Y ~ P
    -- Maybe we should instead have:
    --   ● : Tone -> Premise -> Premise
    --   at-tone : ∀ {P} o (p : X at o ⊩ P) -> X ⊩ ● o P
    box  : ∀{P}     (p : wipe X ⊩ P)         -> X ⊩ □ P

  infix 3 _⊢_
  infix 3 _!_
  data _⊢_ (X : Cx) (a : Type) : Set₁ where
    var : ∀ o (p : o ≤ mono) (x : X o a) -> X ⊢ a
    _!_ : ∀{P} (form : P ⊃ a) (args : X ⊩ P) -> X ⊢ a

-- Some conveniences
var-mono : ∀{X a} (x : X mono a) -> X ⊢ a
var-disc : ∀{X a} (x : X disc a) -> X ⊢ a
var-mono = var mono refl
var-disc = var disc refl

here : ∀{A : Set}{a o} -> (a is o) o a ⊎ A
here = car eq

v0 : ∀{X a} -> a is mono ∪ X ⊢ a
v0 = var-mono here


-- Pattern synonyms for terms.
pattern bool! b             = ⊃bool b ! tt
pattern if! {a} M N₁ N₂     = ⊃if {a} ! term M , (term N₁ , term N₂)
pattern when! {a} sl M N    = ⊃when {a} sl ! term M , term N
pattern pair! {a b} M N     = ⊃pair {a}{b} ! term M , term N
pattern proj! {a b} i M     = ⊃proj {a}{b} i ! term M
pattern inj! {a b} i M      = ⊃inj {a}{b} i ! term M
pattern case! {a b c} M N₁ N₂ =
  ⊃case {a}{b}{c} ! term M , (bind (term N₁) , bind (term N₂))
pattern splitsum! {a b} M   = ⊃splitsum {a}{b} ! term M
pattern lam! {a b} M        = ⊃lam {a}{b} ! bind (term M)
pattern app! {a b} M N      = ⊃app {a}{b} ! term M , term N
pattern box! {a} M          = ⊃box {a} ! box (term M)
pattern letbox! {a b} M N   = ⊃letbox {a}{b} ! term M , bind (term N)
pattern eps! {a} sl         = ⊃eps {a} sl ! tt
pattern vee! {a} sl M N     = ⊃vee {a} sl ! term M , term N
pattern single! {a}{p} M       = ⊃single {a}{p} ! term M
pattern bigvee! {a b dec} sl M N =
  ⊃bigvee {a}{b}{dec} sl ! term M , bind (term N)
pattern fix! {a} p M        = ⊃fix {a} p ! bind (term M)


-- -- Extracting a ⊩ into an ordinary value.
-- -- TODO: is this useful for anything?
-- premise : Cx -> Premise -> Set₁
-- premise X nil = Lift ⊤
-- premise X (P ∧ Q) = premise X P × premise X Q
-- premise X (∙ a) = X ⊢ a
-- premise X (Y ~ P) = premise (Y ∪ X) P
-- premise X (□ P) = premise (wipe X) P

-- un : ∀{X P} -> X ⊩ P -> premise X P
-- un tt = lift tt
-- un (p , q) = un p , un q
-- un (term M) = M
-- un (bind p) = un p
-- un (box p) = un p

-- into : ∀{X P} -> premise X P -> X ⊩ P
-- into {P = nil} (lift tt) = tt
-- into {P = P ∧ Q} (x , y) = into x , into y
-- into {P = ∙ a} x = term x
-- into {P = X ~ P} x = bind (into x)
-- into {P = □ P} x = box (into x)


---------- Applying context renamings to terms ----------
rename : ∀{X Y a} -> X ⊆ Y -> X ⊢ a -> Y ⊢ a
rename* : ∀{X Y P} -> X ⊆ Y -> X ⊩ P -> Y ⊩ P

rename f (var o le a) = var o le (f o a)
rename f (form ! x) = form ! rename* f x

rename* f tt = tt
rename* f (p , q) = rename* f p , rename* f q
rename* f (term M) = term (rename f M)
rename* f (bind p) = bind (rename* (∪/⊆ f) p)
rename* f (box p) = box (rename* (wipe/⊆ f) p)

rename-at : ∀{X Y} o {a} -> X ⊆ Y -> X at o ⊢ a -> Y at o ⊢ a
rename-at mono f M = rename f M
rename-at disc f M = rename (wipe/⊆ f) M

weaken : ∀{X Y a} -> X ⊢ a -> Y ∪ X ⊢ a
weaken = rename drop

weaken-at : ∀ o {X Y a} -> X at o ⊢ a -> (Y ∪ X) at o ⊢ a
weaken-at o = rename-at o drop


---------- Substitutions ----------
infix 4 _⇉_
_⇉_ : Cx -> Cx -> Set₁
X ⇉ Y = ∀ o {a} -> Y o a -> X at o ⊢ a

∪/⇉ : ∀{X Y Z} -> X ⇉ Y -> (Z ∪ X) ⇉ (Z ∪ Y)
∪/⇉ s mono (car x) = var-mono (car x)
∪/⇉ s disc (car x) = var-disc (car x)
∪/⇉ s o    (cdr x) = weaken-at o (s o x)

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
sub* σ (bind p) = bind (sub* (∪/⇉ σ) p)
sub* σ (box p) = box (sub* (wipe/⇉ σ) p)


---------- Term macros / admissible rules / syntax sugar forms ----------
unbox : ∀{X a} -> X ⊢ □ a -> X ⊢ a
unbox M = letbox! M (var-disc here)

box-bind : ∀{X a b} -> a is disc ∪ X ⊢ b -> □ a is mono ∪ X ⊢ b
box-bind M = letbox! v0 (rename drop-mid M)

lam□ : ∀ {X a b} -> a is disc ∪ X ⊢ b -> X ⊢ (□ a) :-> b
lam□ M = lam! (box-bind M)

case□ : ∀{X a b c} -> X ⊢ □ (a :+ b)
      -> (a is disc ∪ X) ⊢ c -> (b is disc ∪ X) ⊢ c
      -> X ⊢ c
case□ M N₁ N₂ = case! (splitsum! M) (box-bind N₁) (box-bind N₂)

let! : ∀{X a b} -> X ⊢ a -> a is mono ∪ X ⊢ b -> X ⊢ b
let! M N = app! (lam! N) M


---------- Change types ----------
Δ : Type -> Type
Δ bool = bool
Δ (down a p) = down a p
Δ (a :x b) = Δ a :x Δ b
Δ (a :+ b) = Δ a :+ Δ b
Δ (a :-> b) = □ a :-> (Δ a :-> Δ b)
Δ (□ a) = □ (Δ a)

ΔSL∈SL : ∀ a -> SL a -> SL (Δ a)
ΔSL∈SL bool tt = tt
ΔSL∈SL (down a p) tt = tt
ΔSL∈SL (a :x b) (asl , bsl) = ΔSL∈SL a asl , ΔSL∈SL b bsl
ΔSL∈SL (a :+ b) ()
ΔSL∈SL (a :-> b) sl = ΔSL∈SL b sl
ΔSL∈SL (□ a) ()

DEC∧SL⊃Δ=id : ∀ a -> DEC a -> SL a -> Δ a ≡ a
DEC∧SL⊃Δ=id bool dec sl = refl
DEC∧SL⊃Δ=id (down a p) dec sl = refl
DEC∧SL⊃Δ=id (a :x b) (adec , bdec) (asl , bsl)
  rewrite DEC∧SL⊃Δ=id a adec asl
        | DEC∧SL⊃Δ=id b bdec bsl = refl
DEC∧SL⊃Δ=id (a :+ b) _ ()
DEC∧SL⊃Δ=id (a :-> b) () sl
DEC∧SL⊃Δ=id (□ a) dec ()

ΔFIX∈FIX : ∀ a -> FIX a -> FIX (Δ a)
ΔFIX∈FIX a (acc , (dec , sl)) rewrite DEC∧SL⊃Δ=id a dec sl = acc , (dec , sl)


---------- Generating dummy values of a change type ----------
dummy : ∀{X} -> (a : Type) -> X ⊢ a -> X ⊢ Δ a
dummy bool x = bool! false
dummy (down a p) M = eps! tt
dummy (a :x b) M = pair! (dummy a (proj! true M)) (dummy b (proj! false M))
dummy (a :+ b) M = case! M (inj! true (dummy a v0)) (inj! false (dummy b v0))
dummy (a :-> b) M =
  -- (λx dx. dummy (M x))
  lam! (lam! (dummy b (app! (rename drop2 M)
                            (unbox (var-mono (cdr here))))))
dummy (□ a) M = letbox! M (box! (dummy a (var-disc here)))


---------- Change environments ----------
data Δ* (X : Cx) : Cx where
  orig  : ∀ o {a} -> X o a -> Δ* X disc a
  deriv : ∀ {o a} -> X o a -> Δ* X o (Δ a)

wipeΔ*X⇉X : ∀{X} -> wipe (Δ* X) ⇉ X
wipeΔ*X⇉X disc x = var-disc (orig disc x)
wipeΔ*X⇉X mono x = var-disc (orig mono x)

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

Δ*drop : ∀{X Y} -> Δ* X ⊆ Δ* (Y ∪ X)
Δ*drop = Δ*/⊆ drop

weakenδ : ∀{X Y a} -> Δ* X ⊢ a -> Δ* (Y ∪ X) ⊢ a
weakenδ = rename Δ*drop


---------- Helpers for δ ----------
-- A pair of a term and its derivative.
infix 3 _⊢δ_
_⊢δ_ : Cx -> Type -> Set₁
X ⊢δ a = X ⊢ a × Δ* X ⊢ Δ a

static : ∀{X a} → X ⊢ a → Δ* X ⊢ a
static = sub Δ*X⇉X

static□ : ∀{X a} → X ⊢ a → Δ* X ⊢ □ a
static□ M = box! (sub wipeΔ*X⇉X M)

lamδ : ∀{X a b} -> Δ* (a is mono ∪ X) ⊢ Δ b -> Δ* X ⊢ Δ (a :-> b)
lamδ dM = lam□ (lam! (rename Δ*cons dM))

-- I think DEC is in principle the wrong property;
-- (down (a :-> b)) should be fine, for example!
-- except we can't have (down (a :-> b)) b/c (a :-> b) not decidable!
whenδ-DEC : ∀{X} a -> DEC a -> SL a -> X ⊢δ bool -> X ⊢δ a -> Δ* X ⊢ Δ a
-- d(when e then f) = if [e] then df else when de then (f + df) - ε
-- note that at decidable semilattice type,
--  ((f + df) - ε) = f v df
whenδ-DEC {X} a dec sl (M , dM) (N , dN) =
  let Δsl = ΔSL∈SL a sl
  in if! (static□ M) dN
       (when! Δsl dM
         (vee! Δsl dN
           (subst (λ a₁ → Δ* X ⊢ a₁) (sym (DEC∧SL⊃Δ=id a dec sl))
             (sub Δ*X⇉X N))))

appδ : ∀{X a b} -> X ⊢δ a :-> b -> X ⊢δ a -> Δ* X ⊢ Δ b
appδ (M , dM) (N , dN) = app! (app! dM (static□ N)) dN

whenδ : ∀ {X} a -> SL a -> X ⊢δ bool -> X ⊢δ a -> Δ* X ⊢ Δ a
whenδ bool = whenδ-DEC bool tt
-- What would happen here if we lifted the requirement that `a` was decidable?
whenδ (down a p) = whenδ-DEC (down a p) p
-- Ideally we should put a guard using DEC? here, so that for decidable types we
-- use whenδ-DEC, since that's more efficient (we think).
whenδ (a :x b) (ap , bp) M (N , dN) =
  pair! (whenδ a ap M (proj! true N , proj! true dN))
        (whenδ b bp M (proj! false N , proj! false dN))
whenδ (a :+ b) ()
-- when M (N : a -> b) == \x. when M (N x)
whenδ (a :-> b) sl (M , dM) (N , dN)
  = lamδ (whenδ b sl
            (weaken M , weakenδ dM)
            -- ugh, why do I need to write this. is there a better way?
            ( app! (weaken N) v0
            , appδ (weaken N , weakenδ dN) (v0 , var-mono (deriv here)) ))
whenδ (□ a) ()

zeroδ : ∀{X} a -> DEC a -> X ⊢ a -> X ⊢ Δ a
zeroδ bool tt M = bool! false
zeroδ (down a x) dec M = eps! tt
zeroδ (a :x b) (adec , bdec) M = pair! (zeroδ a adec (proj! true M))
                                       (zeroδ b bdec (proj! false M))
zeroδ (a :+ b) (adec , bdec) M =
  case! M (inj! true (zeroδ a adec v0))
          (inj! false (zeroδ b bdec v0))
zeroδ (a :-> b) () M
zeroδ (□ a) dec M = letbox! M (box! (zeroδ a dec (var-disc here)))

bigveeδ-DEC : ∀{X a p} c -> DEC c -> SL c
            -> X ⊢δ down a p -> a is mono ∪ X ⊢δ c
            -> Δ* X ⊢ Δ c
bigveeδ-DEC {X}{a}{p} c dec sl (M , dM) (N , dN) =
  let Δsl = ΔSL∈SL c sl
  in vee! Δsl
       (bigvee! Δsl (static M)
         (let! (zeroδ a p v0) (rename {!Δ*cons!} dN)))
       (bigvee! Δsl dM {!!})

bigveeδ : ∀{X a p} c -> SL c
        -> X ⊢δ down a p -> a is mono ∪ X ⊢δ c
        -> Δ* X ⊢ Δ c
bigveeδ bool = bigveeδ-DEC bool tt
bigveeδ (down c p) = bigveeδ-DEC (down c p) p
-- Ideally we should put a guard using DEC? here, so that for decidable types we
-- use whenδ-DEC, since that's more efficient (we think).
bigveeδ (c :x d) (csl , dsl) MdM (N , dN) =
  pair! (bigveeδ c csl MdM (proj! true N , proj! true dN))
        (bigveeδ d dsl MdM (proj! false N , proj! false dN))
bigveeδ (c :+ d) ()
-- d(V(x in M) N)
-- == d(λy. V(x in M) N y)
-- == λ y dy. d(V(x in M) N y)
--
-- d(N y) = dN y dy
bigveeδ {X}{a}{p} (c :-> d) sl (M , dM) (N , dN) = lam□ (lam! (rename r O))
  where
    r : Δ* (c is mono ∪ X) ⊆ Δ c is mono ∪ c is disc ∪ Δ* X
    r .disc (orig .mono (car eq)) = cdr (car eq)
    r .disc (orig o (cdr y)) = cdr (cdr (orig o y))
    r .mono (deriv (car eq)) = car eq
    r o (deriv (cdr y)) = cdr (cdr (deriv y))
    O : Δ* (c is mono ∪ X) ⊢ Δ d
    O = bigveeδ d sl (weaken M , weakenδ dM)
          ( app! (rename drop-mid N) (var-mono (cdr here))
          , app! (app! (rename (Δ*/⊆ drop-mid) dN)
                       (box! (var-disc (orig mono (cdr here)))))
                 (var-mono (deriv (cdr here))))
bigveeδ (□ c) ()


---------- δ itself ----------
δ* : ∀{X a} -> X ⊢ a -> X ⊢δ a
δ : ∀{X a} -> X ⊢ a -> Δ* X ⊢ Δ a

δ* M = (M , δ M)

δ (var o p x) = var o p (deriv x)
δ (bool! x) = bool! x
δ (if! M N₁ N₂) = if! (static M) (δ N₁) (δ N₂)
δ (when! {a} sl M N) = whenδ a sl (δ* M) (δ* N)
δ (pair! M N) = pair! (δ M) (δ N)
δ (proj! true M) = proj! true (δ M)
δ (proj! false M) = proj! false (δ M)
δ (inj! true M) = inj! true (δ M)
δ (inj! false M) = inj! false (δ M)
δ (case!{b}{c} M N₁ N₂) =
  case□ (static□ M)
    (let! (case! (weaken (δ M)) v0 (dummy _ (var-disc (cdr here))))
          (rename Δ*cons (δ N₁)))
    (let! (case! (weaken (δ M)) (dummy _ (var-disc (cdr here))) v0)
          (rename Δ*cons (δ N₂)))
δ (splitsum! M) = splitsum! (δ M)
δ (lam! M) = lam□ (lam! (rename Δ*cons (δ M)))
δ (app! M N) = appδ (δ* M) (δ* N)
-- app! (app! (δ M) (static□ N)) (δ N)
δ (box! M) = box! (rename Δ*-wipe-xchg (δ M))
δ (letbox! M N) =
  letbox! (static M) (letbox! (weaken (δ M)) (rename Δ*cons (δ N)))
-- At (eps : a :-> b), is our derivative still eps? it is the derivative of the
-- constant zero function. Is that also the constant zero function? Yes,
-- inductively. TODO: put proof of this into seminaive.tex.
δ (eps! {a} sl) = eps! (ΔSL∈SL a sl)
-- The critical overapproximation.
δ (vee! {a} sl M N) = vee! (ΔSL∈SL a sl) (δ M) (δ N)
δ (single! M) = eps! tt
-- The whopper.
δ (bigvee! {b = b} sl M N) = bigveeδ b sl (δ* M) (δ* N)
-- The purpose of this whole thing.
δ (fix! {a} p M) = letbox! (static□ (fix! p M))
                     (fix! (ΔFIX∈FIX a p) (rename Δ*cons (δ M)))


---------- Leftovers ----------

-- ΔP : Premise -> Premise
-- ΔP nil = nil
-- ΔP (P ∧ Q) = ΔP P ∧ ΔP Q
-- -- -- Originally:
-- -- ΔP (∙ a) = ∙ (Δ a)
-- -- Alternatively:
-- ΔP (∙ a) = ∙ (□ a) ∧ ∙ (Δ a)
-- ΔP (X ~ P) = Δ* X ~ ΔP P
-- ΔP (□ P) = □ (ΔP P)

-- Δ*-distrib-∪ : ∀{X Y} -> Δ* (Y ∪ X) ⊆ Δ* Y ∪ Δ* X
-- Δ*-distrib-∪ .disc (orig o (car x)) = car (orig o x)
-- Δ*-distrib-∪ .disc (orig o (cdr y)) = cdr (orig o y)
-- Δ*-distrib-∪ o (deriv (car x)) = car (deriv x)
-- Δ*-distrib-∪ o (deriv (cdr y)) = cdr (deriv y)

-- δP : ∀{X P} -> X ⊩ P -> Δ* X ⊩ ΔP P
-- δP tt = tt
-- δP (p , q) = δP p , δP q
-- δP (term M) = term (static□ M) , term (δ M)
-- δP (bind p) = bind (rename* Δ*-distrib-∪ (δP p))
-- δP (box p) = box (rename* Δ*-wipe-xchg (δP p))

-- δ⊃ : ∀{X P a} -> P ⊃ a -> premise (Δ* X) (ΔP P) -> Δ* X ⊢ a
-- δ⊃ (⊃bool x) (lift tt) = bool! x
-- δ⊃ ⊃if ((M , dM) , ((N₁ , dN₁) , (N₂ , dN₂))) = {!!}
-- δ⊃ (⊃when sl) args = {!!}
-- δ⊃ ⊃pair args = {!!}
-- δ⊃ (⊃proj i) args = {!!}
-- δ⊃ (⊃inj i) args = {!!}
-- δ⊃ ⊃case args = {!!}
-- δ⊃ ⊃splitsum args = {!!}
-- δ⊃ ⊃lam args = {!!}
-- δ⊃ ⊃app args = {!!}
-- δ⊃ ⊃box args = {!!}
-- δ⊃ ⊃letbox args = {!!}
-- δ⊃ (⊃eps x) args = {!!}
-- δ⊃ (⊃vee x) args = {!!}
-- δ⊃ ⊃single args = {!!}
-- δ⊃ (⊃bigvee dec sl) args = {!!}
-- δ⊃ (⊃fix x) args = {!!}
