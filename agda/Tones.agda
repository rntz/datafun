module Tones where

open import Prelude
open import Cat
open import Prosets

data Tone : Set where
  ID OP ISOS PATHS : Tone

instance
  tone=? : (x y : Tone) -> Dec (x ≡ y)
  -- this is completely boring.
  tone=? = λ { ID ID → yes refl ; ID OP → no (λ ()) ; ID ISOS → no (λ ()) ; ID PATHS → no (λ ()) ; OP ID → no (λ ()) ; OP OP → yes refl ; OP ISOS → no (λ ()) ; OP PATHS → no (λ ()) ; ISOS ID → no (λ ()) ; ISOS OP → no (λ ()) ; ISOS ISOS → yes refl ; ISOS PATHS → no (λ ()) ; PATHS ID → no (λ ()) ; PATHS OP → no (λ ()) ; PATHS ISOS → no (λ ()) ; PATHS PATHS → yes refl }

data _≺_ : (o p : Tone) -> Set where
  ≺refl : ∀{o} -> o ≺ o
  ISOS≺ : ∀{o} -> ISOS ≺ o
  ≺PATHS : ∀{o} -> o ≺ PATHS

tone-lub : ∀ x y -> Σ[ z ∈ Tone ] (x ≺ z × y ≺ z × (∀ q → x ≺ q → y ≺ q → z ≺ q))
tone-lub ID ID = ID , ≺refl , ≺refl , λ q x _ → x
tone-lub OP OP = OP , ≺refl , ≺refl , λ q x _ → x
tone-lub ID OP = PATHS , ≺PATHS , ≺PATHS , λ { _ ≺refl () ; _ ≺PATHS ≺PATHS → ≺refl }
tone-lub OP ID = PATHS , ≺PATHS , ≺PATHS , λ { _ ≺refl () ; _ ≺PATHS ≺PATHS → ≺refl }
tone-lub x ISOS = x , ≺refl , ISOS≺ , λ q y≺q ISOS≺q → y≺q
tone-lub x PATHS = PATHS , ≺PATHS , ≺refl , λ q x₁ x₂ → x₂
tone-lub ISOS y = y , ISOS≺ , ≺refl , λ q ISOS≺q y≺q → y≺q
tone-lub PATHS y = PATHS , ≺refl , ≺PATHS , λ q PATHS≺q y≺q → PATHS≺q

instance
  tones : Cat _ _
  Obj tones = Tone
  Hom tones = _≺_
  ident tones = ≺refl
  compo tones ≺refl g = g
  compo tones ISOS≺ g = ISOS≺
  compo tones ≺PATHS ≺refl = ≺PATHS
  compo tones ≺PATHS ≺PATHS = ≺PATHS

  tone-sums : Sums tones
  Either tone-sums s t = tone-lub s t .proj₁
  Sums.in₁ tone-sums = tone-lub _ _ .proj₂ .proj₁
  Sums.in₂ tone-sums {s}{t} = tone-lub s t .proj₂ .proj₂ .proj₁
  either tone-sums = tone-lub _ _ .proj₂ .proj₂ .proj₂ _
  Sums.bot tone-sums = ISOS
  Sums.bot≤ tone-sums = ISOS≺

opp : ∀{i j} -> Cat i j -> Cat i j
opp C = Cat: (Obj C) (λ a b → Hom C b a) (ident C) (λ f g → compo C g f)

Opp : ∀{i j} -> cats {i}{j} ≤ cats
Opp = Fun: opp (λ { (Fun: F f) → Fun: F f })

module _  {i j} (C : Cat i j) where
  data Path : (a b : Obj C) -> Set (i ⊔ j) where
    path-by : ∀{a b} -> Hom C a b -> Path a b
    path⁻¹ : ∀{a b} -> Path a b -> Path b a
    path-• : ∀{a b c} -> Path a b -> Path b c -> Path a c

module _ {i j k} {C : Cat i j}
         (F : (a b : Obj C) -> Set k)
         (hom→F : ∀{a b} -> Hom C a b -> F a b)
         (F-symm : Symmetric F)
         (F-trans : Transitive F) where
  path-fold : ∀{a b} -> Path C a b -> F a b
  path-fold (path-by x) = hom→F x
  path-fold (path⁻¹ p) = F-symm (path-fold p)
  path-fold (path-• p q) = F-trans (path-fold p) (path-fold q)

paths : ∀{i j} -> Cat i j -> Cat i (i ⊔ j)
paths C = Cat: (Obj C) (Path C) (path-by (ident C)) path-•

Paths : ∀{i j} -> cats {i}{j} ≤ cats {i}{i ⊔ j}
Paths = Fun: paths (λ { (fun f) → fun (path-fold _ (path-by ∘ f) path⁻¹ path-•) })

den : Fun tones (proset→ prosets prosets)
ap den ID = id
ap den OP = Opp
ap den ISOS = Isos
ap den PATHS = Paths
-- if (a ⇒ b), then (F_s a ⇒ F_s b), where F_s is the functor associated with
-- the tone s. this is just functoriality!
map den {i} ≺refl = map (ap den i)
-- if (a ⇒ b), then (isos a ⇒ F_t b). initiality?
--
-- oh shit, I need that (ap den t .ap) == id!
map den {.ISOS} {t} ISOS≺ {A} {B} A⇒B = Fun: (λ a → {!!}) {!!}
-- if (a ⇒ b), then (F_s a ⇒ paths b). finality?
map den {s} {.PATHS} ≺PATHS A⇒B = {!!} • map Paths A⇒B
