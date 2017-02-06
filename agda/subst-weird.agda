open import Data.List as List hiding ([_])
open import Data.Product as Product
open import Data.Sum as Sum
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Function using (id; _∘_)
open import Data.Maybe as Maybe
open import Data.Bool
open import Data.Empty

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
Hyp : Set
Hyp = Tone × Type

Env : Set₁
Env = Hyp → Set

∅ : Env
∅ _ = ⊥

infixr 5 _&_
_&_ : Hyp → Env → Env
(h & X) h′ = (h ≡ h′) ⊎ X h′

wipe : Env → Env
wipe X (mono , _) = ⊥
wipe X h = X h

wipe-for : Tone → Env → Env
wipe-for disc = wipe
wipe-for mono = λ x → x

infix 4 _⊑_
_⊑_ : Env → Env → Set
X ⊑ Y = {hyp : Hyp} → X hyp → Y hyp

∷/⊑ : ∀ {X Y hyp} → X ⊑ Y → hyp & X ⊑ hyp & Y
∷/⊑ f = Sum.map id f

wipe⊑ : ∀ {X} → wipe X ⊑ X
wipe⊑ {hyp = disc , A} x = x
wipe⊑ {hyp = mono , A} ()

wipe/⊑ : ∀ {X Y} → X ⊑ Y → wipe X ⊑ wipe Y
wipe/⊑ f {hyp = disc , A} x = f x
wipe/⊑ f {hyp = mono , A} ()


-- Terms
infix 4 _⊢_
data _⊢_ (X : Env) : Type → Set where
  var : ∀ {tone type} → X (tone , type) → X ⊢ type
  lam : ∀ {a b} → (mono , a) & X ⊢ b → X ⊢ (Arr a b)
  app : ∀ {a b} → X ⊢ (Arr a b) → X ⊢ a → X ⊢ b
  box : ∀ {a} → wipe X ⊢ a → X ⊢ Disc a
  letbox : ∀ {a b} → X ⊢ Disc a → (disc , a) & X ⊢ b → X ⊢ b

infix 4 _⊢_#_
_⊢_#_ : Env → Tone → Type → Set
X ⊢ tone # a = wipe-for tone X ⊢ a

-- a generalized form of weakening
rename : ∀ {X Y a} → X ⊑ Y → X ⊢ a → Y ⊢ a
rename f (var e) = var (f e)
--rename s (lam M) = lam (rename (∷/⊑ {hyp = mono , _} s) M)
rename {X} s (lam {a = a} M) = lam (rename (∷/⊑ {X} {hyp = mono , a} s) M)
rename s (app M M₁) = app (rename s M) (rename s M₁)
--rename s (box M) = box (rename (wipe/⊑ s) M)
rename s (box M) = box (rename {!!} M)
--rename s (letbox M N) = letbox (rename s M) (rename (∷/⊑ disc s) N)
rename s (letbox M N) = letbox (rename s M) (rename {!!} N)

-- weaken : ∀ {X a b} → (tone : Tone) → X ⊢ a → (tone # b ∷ X) ⊢ a
-- weaken disc = rename (untone cdr id)
-- weaken mono = rename (untone id cdr)

-- 
-- -- substitutions
-- infix 4 _⇉_
-- _⇉_ : Env → Env → Set
-- X ⇉ Y = ∀ {a} (tone : Tone) → (a ∈ Y tone) → (X ⊢ tone # a)

-- weaken⇉ : ∀ {X Y a} → (tone : Tone) → X ⇉ Y → (tone # a ∷ X) ⇉ Y
-- weaken⇉ mono s disc x = s disc x
-- weaken⇉ disc s disc x = weaken disc (s disc x)
-- weaken⇉ tone s mono x = weaken tone (s mono x)

-- _#_·_ : ∀ {X Y a} → (tone : Tone)
--       → (X ⊢ tone # a) → (X ⇉ Y) → (X ⇉ (tone # a ∷ Y))
-- _#_·_ disc M s disc car = M
-- _#_·_ disc M s disc (cdr e) = s disc e
-- _#_·_ disc M s mono e = s mono e
-- _#_·_ mono M s disc e = s disc e
-- _#_·_ mono M s mono car = M
-- _#_·_ mono M s mono (cdr e) = s mono e

-- unwipe : ∀{X a} → wipe X ⊢ a → X ⊢ a
-- unwipe M = rename wipe⊑ M

-- lift : ∀{X Y a} (tone : Tone) → (X ⇉ Y) → (tone # a ∷ X) ⇉ (tone # a ∷ Y)
-- lift disc s = disc # var disc car · weaken⇉ disc s
-- lift mono s = mono # var mono car · weaken⇉ mono s

-- wipe⇉ : ∀{X Y} → X ⇉ Y → wipe X ⇉ wipe Y
-- wipe⇉ s disc e = s disc e
-- wipe⇉ s mono ()

-- sub : ∀ {X Y a} → (X ⇉ Y) → (Y ⊢ a) → (X ⊢ a)
-- sub s (var disc e) = unwipe (s disc e)
-- sub s (var mono e) = s mono e
-- sub s (lam M) = lam (sub (lift mono s) M)
-- sub s (app M M₁) = app (sub s M) (sub s M₁)
-- sub s (box M) = box (sub (wipe⇉ s) M)
-- sub s (letbox M N) = letbox (sub s M) (sub (lift disc s) N)

-- -- -- -- Now we can define all our explicit-substition-style operators
-- -- -- ↑ : {X : Env} {a : Type} → (a ∷ X ⇉ X)
-- -- -- ↑ x = var (there x)

-- -- -- _•_ : {X Y Z : Env} → (X ⇉ Y) → (Y ⇉ Z) → (X ⇉ Z)
-- -- -- (s • t) x = sub s (t x)
