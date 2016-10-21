open import Data.List hiding ([_])
open import Data.Product
open import Data.Sum
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Function using (id)
open import Data.Maybe

data Tone : Set where
  disc : Tone
  mono : Tone

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
Env = List Type × List Type

_#_∷_ : Tone → Type → Env → Env
disc # a ∷ (D , M) = (a ∷ D , M)
mono # a ∷ (D , M) = (D , a ∷ M)

wipe : Env → Env
wipe (D , M) = (D , [])

wipe-for : Tone → Env → Env
wipe-for disc = wipe
wipe-for mono = λ x → x

_⊑_ : Env → Env → Set
(D₁ , M₁) ⊑ (D₂ , M₂) = (D₁ ⊆ D₂) × (M₁ ⊆ M₂)

∷/⊑ : ∀ {X Y a} (tone : Tone) → X ⊑ Y → (tone # a ∷ X) ⊑ (tone # a ∷ Y)
∷/⊑ disc (δ , γ) = cons⊆ δ , γ
∷/⊑ mono (δ , γ) = δ , cons⊆ γ

wipe⊑ : ∀ {X} → wipe X ⊑ X
wipe⊑ = id , λ ()

wipe/⊑ : ∀ {X Y} → X ⊑ Y → wipe X ⊑ wipe Y
wipe/⊑ (δ , γ) = δ , λ ()

infix 4 _∋_#_
_∋_#_ : Env → Tone → Type → Set
(D , M) ∋ disc # a = a ∈ D
(D , M) ∋ mono # a = a ∈ M


-- Terms
infix 4 _⊢_
data _⊢_ (X : Env) : Type → Set where
  var : ∀ {a} (tone : Tone) → X ∋ tone # a → X ⊢ a
  lam : ∀ {a b} → mono # a ∷ X ⊢ b → X ⊢ (Arr a b)
  app : ∀ {a b} → X ⊢ (Arr a b) → X ⊢ a → X ⊢ b
  box : ∀ {a} → wipe X ⊢ a → X ⊢ Disc a
  letbox : ∀ {a b} → X ⊢ Disc a → disc # a ∷ X ⊢ b → X ⊢ b

infix 4 _⊢_#_
_⊢_#_ : Env → Tone → Type → Set
X ⊢ tone # a = wipe-for tone X ⊢ a

-- a generalized form of weakening
rename : ∀ {X Y a} → Y ⊑ X → Y ⊢ a → X ⊢ a
rename (δ , γ) (var disc e) = var disc (δ e)
rename (δ , γ) (var mono e) = var mono (γ e)
rename s (lam M) = lam (rename (∷/⊑ mono s) M)
rename s (app M M₁) = app (rename s M) (rename s M₁)
rename s (box M) = box (rename (wipe/⊑ s) M)
rename s (letbox M N) = letbox (rename s M) (rename (∷/⊑ disc s) N)


-- substitutions
infix 4 _⊢*_
_⊢*_ : Env → Env → Set
X ⊢* Y = ∀ {a} (tone : Tone) → Y ∋ tone # a → X ⊢ tone # a

weaken : ∀ {X a b} → (tone : Tone) → X ⊢ a → (tone # b ∷ X) ⊢ a
weaken disc = rename (cdr , id)
weaken mono = rename (id , cdr)

weaken* : ∀ {X Y a} → (tone : Tone) → X ⊢* Y → (tone # a ∷ X) ⊢* Y
weaken* mono s disc x = s disc x
weaken* disc s disc x = weaken disc (s disc x)
weaken* tone s mono x = weaken tone (s mono x)

_#_·_ : ∀ {X Y a} → (tone : Tone)
      → (X ⊢ tone # a) → (X ⊢* Y) → (X ⊢* (tone # a ∷ Y))
_#_·_ disc M s disc car = M
_#_·_ disc M s disc (cdr e) = s disc e
_#_·_ disc M s mono e = s mono e
_#_·_ mono M s disc e = s disc e
_#_·_ mono M s mono car = M
_#_·_ mono M s mono (cdr e) = s mono e

unwipe : ∀{X a} → wipe X ⊢ a → X ⊢ a
unwipe M = rename wipe⊑ M

lift : ∀{X Y a} (tone : Tone) → (X ⊢* Y) → (tone # a ∷ X) ⊢* (tone # a ∷ Y)
lift disc s = disc # var disc car · weaken* disc s
lift mono s = mono # var mono car · weaken* mono s

wipe⊢* : ∀{X Y} → X ⊢* Y → wipe X ⊢* wipe Y
wipe⊢* s disc e = s disc e
wipe⊢* s mono ()

sub : ∀ {X Y a} → (X ⊢* Y) → (Y ⊢ a) → (X ⊢ a)
sub s (var disc e) = unwipe (s disc e)
sub s (var mono e) = s mono e
sub s (lam M) = lam (sub (lift mono s) M)
sub s (app M M₁) = app (sub s M) (sub s M₁)
sub s (box M) = box (sub (wipe⊢* s) M)
sub s (letbox M N) = letbox (sub s M) (sub (lift disc s) N)

-- -- Now we can define all our explicit-substition-style operators
-- ↑ : {X : Env} {a : Type} → (a ∷ X ⊢* X)
-- ↑ x = var (there x)

-- _•_ : {X Y Z : Env} → (X ⊢* Y) → (Y ⊢* Z) → (X ⊢* Z)
-- (s • t) x = sub s (t x)


-- Interesting alternative possibility:
--
--      X ⊢* Y = ∀ {tone a} → wipe-for tone Y ⊢ a → wipe-for tone X ⊢ a
--
-- would maybe want to notate it the other way around?


-- data _⊢*_ (Γ : Env) : Env → Set where
--   nil : Γ ⊢* []
--   cons : {a : Type}{Γ′ : Env} → Γ ⊢ a → Γ ⊢* Γ′ → Γ ⊢* (a ∷ Γ′)

-- -- substitutions
-- data Subst : Env → Env → Set where
--   id : {Γ : Env} → Subst Γ Γ
--   _•_ : {Γa Γb Γc : Env} → Subst Γb Γc → Subst Γa Γb → Subst Γa Γc
--   ↑ : {Γ : Env} {a : Type} → Subst (a ∷ Γ) Γ
--   _·_ : {Γ Γ′ : Env} {a : Type} → Γ ⊢ a → Subst Γ Γ′ → Subst Γ (a ∷ Γ′)

-- postulate
--   X Y : Env
--   a : Type
--   s : Subst X (a ∷ Y)

-- {-# NON_TERMINATING #-}
-- sub : {Γ Γ′ : Env}{a : Type} → Subst Γ′ Γ → Γ ⊢ a → Γ′ ⊢ a
-- sub id M = M
-- sub (s • t) M = sub t (sub s M)
-- sub ↑ (var x) = var (there x)
-- sub (M · s) (var (here refl)) = M
-- sub (M · s) (var (there x)) = sub s (var x)
-- sub s (lam M) = lam (sub (var (here refl) · (s • ↑)) M)
-- sub s (app M N) = app (sub s M) (sub s N)
