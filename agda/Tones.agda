module Tones where

open import Prelude
open import Cat
open import Prosets

data Tone : Set where
  ID OP □ ◇ : Tone

data _≺_ : (T U : Tone) -> Set where
  ≺refl : ∀{T} -> T ≺ T
  □≺ : ∀{T} -> □ ≺ T
  ≺◇ : ∀{T} -> T ≺ ◇

instance
  -- Completely tedious decidability procedures.
  tone=? : (T U : Tone) -> Dec (T ≡ U)
  tone=? = λ { ID ID → yes refl ; ID OP → no (λ ()) ; ID □ → no (λ ()) ; ID ◇ → no (λ ()) ; OP ID → no (λ ()) ; OP OP → yes refl ; OP □ → no (λ ()) ; OP ◇ → no (λ ()) ; □ ID → no (λ ()) ; □ OP → no (λ ()) ; □ □ → yes refl ; □ ◇ → no (λ ()) ; ◇ ID → no (λ ()) ; ◇ OP → no (λ ()) ; ◇ □ → no (λ ()) ; ◇ ◇ → yes refl }
  _≺?_ : (T U : Tone) -> Dec (T ≺ U)
  _≺?_ = λ { ID ID → yes ≺refl ; ID OP → no λ () ; ID □ → no λ () ; ID ◇ → yes ≺◇ ; OP ID → no λ () ; OP OP → yes ≺refl ; OP □ → no λ () ; OP ◇ → yes ≺◇ ; □ y → yes □≺ ; ◇ ID → no λ () ; ◇ OP → no λ () ; ◇ □ → no λ () ; ◇ ◇ → yes ≺refl }

  tones : Cat _ _
  tones = Cat: Tone _≺_ ≺refl λ { ≺refl g → g ; □≺ g → □≺ ; ≺◇ ≺refl → ≺◇ ; ≺◇ ≺◇ → ≺◇ }

instance
  tone-joins : Joins tones
  Joins.join tone-joins ID ID = ID / ≺refl / ≺refl / λ x _ → x
  Joins.join tone-joins OP OP = OP / ≺refl / ≺refl / λ x _ → x
  Joins.join tone-joins ID OP = ◇ / ≺◇ / ≺◇ / λ { ≺refl () ; ≺◇ ≺◇ → ≺◇ }
  Joins.join tone-joins OP ID = ◇ / ≺◇ / ≺◇ / λ { ≺refl () ; ≺◇ ≺◇ → ≺◇ }
  Joins.join tone-joins □ U = U / □≺ / ≺refl / λ _ x → x
  Joins.join tone-joins ◇ U = ◇ / ≺refl / ≺◇ / λ x _ → x
  Joins.join tone-joins T □ = T / ≺refl / □≺ / λ x _ → x
  Joins.join tone-joins T ◇ = ◇ / ≺◇ / ≺refl / λ _ x → x
  Joins.bottom tone-joins = □ , □≺ 

-- tone-lub : ∀ T U -> Σ[ V ∈ Tone ] (T ≺ V × U ≺ V × (∀ {W} → T ≺ W → U ≺ W → V ≺ W))
-- tone-lub ID ID = ID , ≺refl , ≺refl , λ x _ → x
-- tone-lub OP OP = OP , ≺refl , ≺refl , λ x _ → x
-- tone-lub ID OP = ◇ , ≺◇ , ≺◇ , λ { ≺refl () ; ≺◇ ≺◇ → ≺refl }
-- tone-lub OP ID = ◇ , ≺◇ , ≺◇ , λ { ≺refl () ; ≺◇ ≺◇ → ≺refl }
-- tone-lub □ y = y , □≺ , ≺refl , λ □≺q y≺q → y≺q
-- tone-lub ◇ y = ◇ , ≺refl , ≺◇ , λ ◇≺q y≺q → ◇≺q
-- tone-lub x □ = x , ≺refl , □≺ , λ y≺q □≺q → y≺q
-- tone-lub x ◇ = ◇ , ≺◇ , ≺refl , λ x₁ x₂ → x₂

-- instance
--   tone-sums : Sums tones
--   Either tone-sums s t = tone-lub s t .proj₁
--   Sums.in₁ tone-sums = tone-lub _ _ .proj₂ .proj₁
--   Sums.in₂ tone-sums {s}{t} = tone-lub s t .proj₂ .proj₂ .proj₁
--   either tone-sums = tone-lub _ _ .proj₂ .proj₂ .proj₂
--   Sums.bot tone-sums = □
--   Sums.bot≤ tone-sums = □≺

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

-- -- FIXME: Need to capture the fact that we don't actually change the set, just the ordering.
-- den : Fun tones (proset→ prosets prosets)
-- ap den ID = id
-- ap den OP = Opp
-- ap den □ = Isos
-- ap den ◇ = Paths
-- -- if (a ⇒ b), then (F_s a ⇒ F_s b), where F_s is the functor associated with
-- -- the tone s. this is just functoriality!
-- map den {i} ≺refl = map (ap den i)
-- -- if (a ⇒ b), then (isos a ⇒ F_t b). initiality?
-- --
-- -- oh shit, I need that (ap den t .ap) == id!
-- map den {.□} {t} □≺ {A} {B} A⇒B = Fun: (λ a → {!!}) {!!}
-- -- if (a ⇒ b), then (F_s a ⇒ paths b). finality?
-- map den {s} {.◇} ≺◇ A⇒B = {!!} • map Paths A⇒B
