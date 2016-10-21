open import Data.List hiding ([_]; sum)
open import Data.Product hiding (map)
open import Data.Sum hiding (map)
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Function using (id; _∘_)
open import Data.Maybe hiding (map)
open import Data.Bool
open import Data.Unit
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Data.Empty

-- Tones
data Tone : Set where
  disc : Tone
  mono : Tone

untone : ∀{ℓ} {P : Tone → Set ℓ} → P disc → P mono → (t : Tone) → P t
untone if-disc if-mono disc = if-disc
untone if-disc if-mono mono = if-mono


-- Types
infixr 6 _:→_
infix 7 _:×_ _:+_

data Type : Set where
  bool : Type
  nat : Type
  set : Type → Type
  _:→_ : Type → Type → Type
  _:×_ : Type → Type → Type
  _:+_ : Type → Type → Type
  □ : Type → Type

Semilattice : Type → Set
Semilattice bool = ⊤
Semilattice nat = ⊤
Semilattice (set a) = ⊤
Semilattice (a :→ b) = Semilattice b
Semilattice (a :× b) = Semilattice a × Semilattice b
Semilattice (a :+ b) = ⊥
-- semantically (□ a) forms a semilattice iff a ≃ 1, but whatever
Semilattice (□ a) = ⊥

Finite : Type → Set
Finite bool = ⊤
Finite nat = ⊥
Finite (set t) = Finite t
Finite (□ t) = Finite t
Finite (a :→ b) = Finite a × Finite b
Finite (a :× b) = Finite a × Finite b
Finite (a :+ b) = Finite a × Finite b

Eqtype : Type → Set
Eqtype bool = ⊤
Eqtype nat = ⊤
Eqtype (set t) = Eqtype t
Eqtype (□ t) = Eqtype t
Eqtype (a :→ b) = ⊥
Eqtype (a :× b) = Eqtype a × Eqtype b
Eqtype (a :+ b) = Eqtype a × Eqtype b

ACC : Type → Set
ACC bool = ⊤
ACC nat = ⊥
ACC (set t) = Finite t
ACC (□ t) = ⊤
ACC (a :→ b) = Finite a × ACC b
ACC (a :× b) = ACC a × ACC b
ACC (a :+ b) = ACC a × ACC b

Fixtype : Type → Set
Fixtype a = Semilattice a × Eqtype a × ACC a


-- Environments
Env : Set
Env = Tone → List Type

∅ : Env
∅ _ = []

_#_∷_ : Tone → Type → Env → Env
(disc # a ∷ X) = untone (a ∷ X disc) (X mono)
(mono # a ∷ X) = untone (X disc) (a ∷ X mono)

wipe : Env → Env
wipe X = untone (X disc) []

wipe-for : Tone → Env → Env
wipe-for disc = wipe
wipe-for mono = λ x → x


-- Subsetting of lists of types
infix 4 _∈_ _⊆_

data _∈_ (a : Type) : List Type → Set where
  car : ∀ {as} → a ∈ (a ∷ as)
  cdr : ∀ {as} {b} → a ∈ as → a ∈ (b ∷ as)

_⊆_ : List Type → List Type → Set
X ⊆ Y = ∀ {h} → h ∈ X → h ∈ Y

_•⊆_ : ∀ {X Y Z} → X ⊆ Y → Y ⊆ Z → X ⊆ Z
(f •⊆ g) x = g (f x)

∷/⊆ : ∀ {X Y e} → X ⊆ Y → (e ∷ X) ⊆ (e ∷ Y)
∷/⊆ s car = car
∷/⊆ s (cdr x) = cdr (s x)

extend-l : ∀ {R} (L : _) → R ⊆ L ++ R
extend-l [] x = x
extend-l (_ ∷ L) x = cdr (extend-l L x)

-- extend-r is secretly the identity function
extend-r : ∀ {L} (R : _) → L ⊆ L ++ R
extend-r R car = car
extend-r R (cdr x) = cdr (extend-r R x)

-- and so is map/∈
map/∈ : ∀{a X f} → a ∈ X → f a ∈ map f X
map/∈ car = car
map/∈ (cdr e) = cdr (map/∈ e)

-- Renamings between environments
infix 4 _⊑_
_⊑_ : Env → Env → Set
X ⊑ Y = ∀ {a} (tone : Tone) → a ∈ X tone → a ∈ Y tone

⊑∷ : ∀ {X a} (tone : Tone) → X ⊑ (tone # a ∷ X)
⊑∷ disc = untone cdr id
⊑∷ mono = untone id cdr

∷/⊑ : ∀ {X Y a} (tone : Tone) → X ⊑ Y → (tone # a ∷ X) ⊑ (tone # a ∷ Y)
∷/⊑ disc f = untone (∷/⊆ (f disc)) (f mono)
∷/⊑ mono f = untone (f disc) (∷/⊆ (f mono))

wipe⊑ : ∀ {X} → wipe X ⊑ X
wipe⊑ = untone id (λ ())

wipe/⊑ : ∀ {X Y} → X ⊑ Y → wipe X ⊑ wipe Y
wipe/⊑ f = untone (f disc) (λ ())


-- Terms
-- FIXME: need to add fixed point!
infix 4 _⊢_
data _⊢_ (X : Env) : Type → Set where
  var : ∀ {a} (tone : Tone) → a ∈ X tone → X ⊢ a
  -- functions
  lam : ∀ {a b} → mono # a ∷ X ⊢ b → X ⊢ (a :→ b)
  app : ∀ {a b} → X ⊢ (a :→ b) → X ⊢ a → X ⊢ b
  -- box
  box : ∀ {a} → wipe X ⊢ a → X ⊢ □ a
  letbox : ∀ {a b} → X ⊢ □ a → disc # a ∷ X ⊢ b → X ⊢ b
  -- semilattices
  unit : ∀{a} → Semilattice a → X ⊢ a
  vee : ∀{a} → Semilattice a → X ⊢ a → X ⊢ a → X ⊢ a
  -- sets
  singleton : ∀{a} → wipe X ⊢ a → X ⊢ set a
  ⋁ : ∀{a b} → Semilattice b → X ⊢ set a → (disc # a ∷ X ⊢ b) → X ⊢ b
  -- booleans
  bool : Bool → X ⊢ bool
  when : ∀{a} → Semilattice a → X ⊢ bool → X ⊢ a → X ⊢ a
  if : ∀{a} → wipe X ⊢ bool → X ⊢ a → X ⊢ a → X ⊢ a
  -- sums
  inj : ∀{a b} → (i : Bool) → X ⊢ (if i then a else b) → X ⊢ a :+ b
  case : ∀{a b c} (tone : Tone)
       → wipe-for tone X ⊢ a :+ b
       → tone # a ∷ X ⊢ c → tone # b ∷ X ⊢ c
       → X ⊢ c
  -- products
  pair : ∀{a b} → X ⊢ a → X ⊢ b → X ⊢ a :× b
  proj : ∀{a b} (i : Bool) → X ⊢ a :× b → X ⊢ (if i then a else b)

infix 4 _⊢_#_
_⊢_#_ : Env → Tone → Type → Set
X ⊢ tone # a = wipe-for tone X ⊢ a

-- a generalized form of weakening
rename : ∀ {X Y a} → X ⊑ Y → X ⊢ a → Y ⊢ a
rename f (var _ e) = var _ (f _ e)
rename s (lam M) = lam (rename (∷/⊑ mono s) M)
rename s (app M M₁) = app (rename s M) (rename s M₁)
rename s (box M) = box (rename (wipe/⊑ s) M)
rename s (letbox M N) = letbox (rename s M) (rename (∷/⊑ disc s) N)
rename s (unit x) = unit x
rename s (vee x M M₁) = vee x (rename s M) (rename s M₁)
rename s (singleton M) = singleton (rename (wipe/⊑ s) M)
rename s (⋁ x M M₁) = ⋁ x (rename s M) (rename (∷/⊑ disc s) M₁)
rename s (bool x) = bool x
rename s (when x M M₁) = when x (rename s M) (rename s M₁)
rename s (if M N₁ N₂) = if (rename (wipe/⊑ s) M) (rename s N₁) (rename s N₂)
rename s (inj i M) = inj i (rename s M)
rename s (case disc M M₁ M₂)
  = case disc (rename (wipe/⊑ s) M) (rename (∷/⊑ disc s) M₁) (rename (∷/⊑ disc s) M₂)
rename s (case mono M M₁ M₂)
  = case mono (rename s M) (rename (∷/⊑ mono s) M₁) (rename (∷/⊑ mono s) M₂)
rename s (pair M M₁) = pair (rename s M) (rename s M₁)
rename s (proj i M) = proj i (rename s M)

weaken : ∀ {X a b} → (tone : Tone) → X ⊢ a → (tone # b ∷ X) ⊢ a
weaken disc = rename (untone cdr id)
weaken mono = rename (untone id cdr)


-- substitutions
infix 4 _⇉_
_⇉_ : Env → Env → Set
X ⇉ Y = ∀ {a} (tone : Tone) → (a ∈ Y tone) → (X ⊢ tone # a)

weaken⇉ : ∀ {X Y a} → (tone : Tone) → X ⇉ Y → (tone # a ∷ X) ⇉ Y
weaken⇉ mono s disc x = s disc x
weaken⇉ disc s disc x = weaken disc (s disc x)
weaken⇉ tone s mono x = weaken tone (s mono x)

infixr 5 _#_·_
_#_·_ : ∀ {X Y a} → (tone : Tone)
      → (X ⊢ tone # a) → (X ⇉ Y) → (X ⇉ (tone # a ∷ Y))
_#_·_ disc M s disc car = M
_#_·_ disc M s disc (cdr e) = s disc e
_#_·_ disc M s mono e = s mono e
_#_·_ mono M s disc e = s disc e
_#_·_ mono M s mono car = M
_#_·_ mono M s mono (cdr e) = s mono e

unwipe : ∀{X a} → wipe X ⊢ a → X ⊢ a
unwipe M = rename wipe⊑ M

lift : ∀{X Y a} (tone : Tone) → (X ⇉ Y) → (tone # a ∷ X) ⇉ (tone # a ∷ Y)
lift disc s = disc # var disc car · weaken⇉ disc s
lift mono s = mono # var mono car · weaken⇉ mono s

wipe⇉ : ∀{X Y} → X ⇉ Y → wipe X ⇉ wipe Y
wipe⇉ s disc e = s disc e
wipe⇉ s mono ()

sub : ∀ {X Y a} → (X ⇉ Y) → (Y ⊢ a) → (X ⊢ a)
sub s (var disc e) = unwipe (s disc e)
sub s (var mono e) = s mono e
sub s (lam M) = lam (sub (lift mono s) M)
sub s (app M M₁) = app (sub s M) (sub s M₁)
sub s (box M) = box (sub (wipe⇉ s) M)
sub s (letbox M N) = letbox (sub s M) (sub (lift disc s) N)
sub s (unit x) = unit x
sub s (vee x M M₁) = vee x (sub s M) (sub s M₁)
sub s (singleton M) = singleton (sub (wipe⇉ s) M)
sub s (⋁ x M M₁) = ⋁ x (sub s M) (sub (lift disc s) M₁)
sub s (bool x) = bool x
sub s (when x M M₁) = when x (sub s M) (sub s M₁)
sub s (if M N₁ N₂) = if (sub (wipe⇉ s) M) (sub s N₁) (sub s N₂)
sub s (inj i M) = inj i (sub s M)
sub s (case disc M M₁ M₂)
  = case disc (sub (wipe⇉ s) M) (sub (lift disc s) M₁) (sub (lift disc s) M₂)
sub s (case mono M M₁ M₂)
  = case mono (sub s M) (sub (lift mono s) M₁) (sub (lift mono s) M₂)
sub s (pair M M₁) = pair (sub s M) (sub s M₁)
sub s (proj i M) = proj i (sub s M)


-- Derivatives
Δ : Type → Type
Δ bool = bool
Δ nat = nat
Δ (set a) = set a
Δ (a :→ b) = □ a :→ Δ a :→ Δ b
Δ (a :× b) = Δ a :× Δ b
Δ (a :+ b) = Δ a :+ Δ b
Δ (□ a) = □ (Δ a)

Δ* : Env → Env
Δ* X = untone (X mono ++ X disc ++ map Δ (X disc)) (map Δ (X mono))

-- And now we need lots of lemmas.
unbox : ∀{X a} → X ⊢ □ a → X ⊢ a
unbox M = letbox M (var disc car)

Δ*-wipe-exchange : (X : _) → Δ* (wipe X) ⊑ wipe (Δ* X)
Δ*-wipe-exchange X = untone (extend-l (X mono)) (λ ())

Δ*-disc∷ : ∀{a} (X : _) → Δ* (disc # a ∷ X) ⊑ (disc # Δ a ∷ (disc # a ∷ Δ* X))
Δ*-disc∷ X mono x = x
Δ*-disc∷ X disc x = {!!}

-- have: X mono ++ (a ∷ X disc) ++ (Δ a ∷ map Δ (X disc))
-- goal: Δ a ∷ a ∷ (X mono ++ X disc ++ map Δ (X disc))

wipeΔ*X⇉X : ∀{X} → wipe (Δ* X) ⇉ X
wipeΔ*X⇉X {X} disc = var disc ∘ extend-l (X mono) ∘ extend-r _
wipeΔ*X⇉X mono = var disc ∘ extend-r _

Δ*X⇉X : ∀{X} → Δ* X ⇉ X
Δ*X⇉X {X} disc = var disc ∘ extend-l (X mono) ∘ extend-r _
Δ*X⇉X mono = var disc ∘ extend-r _

static : ∀{X a} → X ⊢ a → Δ* X ⊢ a
static = sub Δ*X⇉X

static-box : ∀{X a} → X ⊢ a → Δ* X ⊢ □ a
static-box M = box (sub wipeΔ*X⇉X M)

lam□ : ∀ {X a b} → disc # a ∷ X ⊢ b → X ⊢ (□ a :→ b)
lam□ M = lam (letbox (var mono car) (weaken mono M))

δ-unit : ∀{X} (a : Type) → Semilattice a → X ⊢ Δ a
δ-unit bool tt = bool false
δ-unit nat tt = unit tt
δ-unit (set a) tt = unit tt
δ-unit (a :→ b) x = lam (lam (δ-unit b x))
δ-unit (a :× b) (x , y) = pair (δ-unit a x) (δ-unit b y)
δ-unit (_ :+ _) ()
δ-unit (□ a) ()

δ : ∀{X a} → X ⊢ a → Δ* X ⊢ Δ a
-- What if I pass in a function as a discrete argument, f, to another function,
-- and try to take the derivative of this thing? Then despite the function
-- argument f being a discrete variable, I *will* want a df, variable because I
-- want the derivative of f, and I don't want to have to compute it
-- inefficiently at runtime! Try this argument on Neel.
δ {X} (var disc x) = var disc (extend-l (X mono) (extend-l (X disc) (map/∈ x)))
δ (var mono x) = var mono (map/∈ x)
δ (lam M) = lam□ (lam (δ M))
δ (app M N) = app (app (δ M) (static-box N)) (δ N)
δ {X} (box M) = box (rename (Δ*-wipe-exchange X) (δ M))
δ (letbox M M₁) = letbox (static M)
                    (letbox (weaken disc (δ M))
                      (rename {!!} (δ M₁)))
δ {a = a} (unit x) = δ-unit a x
δ (vee x M M₁) = {!!}
δ (singleton _) = unit tt
δ (⋁ x M M₁) = {!!}
δ (bool x) = bool false
δ (when x M M₁) = {!!}
δ (if M N₁ N₂) = {!!}
δ (inj i M) = {!!}
δ (case tone M M₁ M₂) = {!!}
δ (pair M M₁) = {!!}
δ (proj i M) = {!!}

-- vee-func : ∀{a} → Semilattice a → ∅ ⊢ a :→ a :→ a
-- vee-func p = lam (lam (vee p (var mono car) (var mono (cdr car))))

-- record ChangeType (t : Type) : Set where
--   field
--     Δt : Type
--     nil : ∅ ⊢ t :→ Δt
--     apply : ∅ ⊢ Δt :→ t :→ t
--     -- is this right?
--     vee′ : if semilattice? t
--            then (∅ ⊢ (Δt :× Δt) :→ (t :× t) :→ (t :× t))
--            else ⊤

-- change : (t : Type) → ChangeType t
-- change bool = record
--   { Δt = bool
--   ; nil = lam (bool false)
--   ; apply = vee-func refl
--   ; vee′ = lam (lam {!!}) }
-- change nat = record
--   { Δt = nat
--   ; nil = lam (var mono car)
--   ; apply = vee-func refl
--   ; vee′ = {!!} }
-- change (set t) = record
--   { Δt = set t
--   ; nil = lam (unit refl)
--   ; apply = vee-func refl
--   ; vee′ = {!!} }
-- change (a :→ b) = record
--   { Δt = □ a :→ ChangeType.Δt Δa :→ ChangeType.Δt Δb
--   -- uh-oh, I think I can't implement this; I need difference (-)!
--   --
--   -- hm, perhaps nil here should be performed statically rather than
--   -- dynamically? by static differentiation?
--   ; nil = lam (lam (letbox (var mono car) (lam {!!})))
--   ; apply = {!!}
--   ; vee′ = {!!} }
--   where Δa = change a
--         Δb = change b
-- change (a :× b) = {!!}
-- change (a :+ b) = {!!}
-- change (□ a) = record
--   { Δt = {!!}
--   ; nil = {!!}
--   ; apply = {!!}
--   ; vee′ = tt }
