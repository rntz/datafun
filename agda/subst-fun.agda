open import Data.List hiding ([_])
open import Data.Product
open import Data.Sum
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Function using (id)
open import Data.Maybe
open import Data.Bool

data Tone : Set where
  disc : Tone
  mono : Tone

untone : ∀{ℓ} {P : Tone → Set ℓ} → P disc → P mono → (t : Tone) → P t
untone if-disc if-mono disc = if-disc
untone if-disc if-mono mono = if-mono

data Type : Set where
  Arr : Type → Type → Type
  Pair : Type → Type → Type
  Disc : Type → Type

-- Subsetting of lists of types
infix 4 _∈_ _⊆_

data _∈_ (a : Type) : List Type → Set where
  car : ∀ {as} → a ∈ (a ∷ as)
  cdr : ∀ {as} {b} → a ∈ as → a ∈ (b ∷ as)

_⊆_ : List Type → List Type → Set
X ⊆ Y = ∀ {h} → h ∈ X → h ∈ Y

_•⊆_ : ∀ {X Y Z} → X ⊆ Y → Y ⊆ Z → X ⊆ Z
(f •⊆ g) x = g (f x)

cons⊆ : ∀ {X Y e} → X ⊆ Y → (e ∷ X) ⊆ (e ∷ Y)
cons⊆ s car = car
cons⊆ s (cdr x) = cdr (s x)


-- Environments
Env : Set
Env = Tone → List Type

env : List Type → List Type → Env
env = untone

∅ : Env
∅ _ = []

_#_∷_ : Tone → Type → Env → Env
(disc # a ∷ X) = env (a ∷ X disc) (X mono)
(mono # a ∷ X) = env (X disc) (a ∷ X mono)

wipe : Env → Env
wipe X = env (X disc) []

wipe-for : Tone → Env → Env
wipe-for disc = wipe
wipe-for mono = λ x → x

_⊑_ : Env → Env → Set
X ⊑ Y = ∀ {a} (tone : Tone) → a ∈ X tone → a ∈ Y tone

⊑∷ : ∀ {X a} (tone : Tone) → X ⊑ (tone # a ∷ X)
⊑∷ disc = untone cdr id
⊑∷ mono = untone id cdr

∷/⊑ : ∀ {X Y a} (tone : Tone) → X ⊑ Y → (tone # a ∷ X) ⊑ (tone # a ∷ Y)
∷/⊑ disc f = untone (cons⊆ (f disc)) (f mono)
∷/⊑ mono f = untone (f disc) (cons⊆ (f mono))

wipe⊑ : ∀ {X} → wipe X ⊑ X
wipe⊑ = untone id (λ ())

wipe/⊑ : ∀ {X Y} → X ⊑ Y → wipe X ⊑ wipe Y
wipe/⊑ f = untone (f disc) (λ ())


-- Terms
infix 4 _⊢_
data _⊢_ (X : Env) : Type → Set where
  var : ∀ {a} (tone : Tone) → a ∈ X tone → X ⊢ a
  lam : ∀ {a b} → mono # a ∷ X ⊢ b → X ⊢ (Arr a b)
  app : ∀ {a b} → X ⊢ (Arr a b) → X ⊢ a → X ⊢ b
  box : ∀ {a} → wipe X ⊢ a → X ⊢ Disc a
  letbox : ∀ {a b} → X ⊢ Disc a → disc # a ∷ X ⊢ b → X ⊢ b

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

-- -- -- Now we can define all our explicit-substition-style operators
-- -- ↑ : {X : Env} {a : Type} → (a ∷ X ⇉ X)
-- -- ↑ x = var (there x)

-- -- _•_ : {X Y Z : Env} → (X ⇉ Y) → (Y ⇉ Z) → (X ⇉ Z)
-- -- (s • t) x = sub s (t x)
