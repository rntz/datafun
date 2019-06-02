{-# OPTIONS --postfix-projections #-}
module Changes where

open import Prelude
open import Cat
import Data.Product
open import Lambdas
open Fun!%

record ΔProset : Set1 where
  no-eta-equality
  constructor ΔProset:
  field 𝕍 Δ : Proset
  private instance -𝕍 = 𝕍; -Δ = Δ
  𝕍₀ = Obj 𝕍
  Δ₀ = Obj Δ

  field ok : Δ₀ → 𝕍₀ → 𝕍₀ → Set
  -- -- Do I need that `ok` is functional? Let's assume no for now.
  -- field functional : ∀{dx₁ x₁ y₁} → ok dx₁ x₁ y₁
  --                  → ∀{dx₂ x₂ y₂} → ok dx₂ x₂ y₂
  --                  → dx₁ ≈ dx₂ → x₁ ≈ x₂ → y₁ ≈ y₂

  Δ₁ = λ x y → ∃[ dx ] ok dx x y

  field sound : ∀{dx x y} → ok dx x y → x ≤ y
  -- argh! If I want to use "iso" as my comonad, then I'm going to have to show
  -- that completeness is actually _invariant_ (respects the iso-ordering) in x
  -- & y. or, I could use discreteness, but then I lose extensional function
  -- equality in (disc (A ⇒ B)). this may or may not be relevant; if it is, I
  -- can postulate function extensionality.
  field complete : ∀{x y} → x ≤ y → Δ₁ x y

  field compo : Δ ∧ Δ ⇒ Δ
  field compok : ∀{dx x y} → ok dx x y → ∀{dy z} → ok dy y z
               → ok (compo ! dx , dy) x z

  change : ∀{x y} → x ≤ y → Δ₀
  change-ok : ∀{x y} (p : x ≤ y) → ok (change p) x y
  change = proj₁ ∘ complete; change-ok = proj₂ ∘ complete

  𝟎 : 𝕍₀ → Δ₀;  𝟎-ok : ∀ x → ok (𝟎 x) x x
  𝟎 x = complete {x} id .proj₁; 𝟎-ok _ = complete id .proj₂

open ΔProset public

record ΔFun (A B : ΔProset) : Set where
  constructor ΔFun:
  field
    𝕍 : 𝕍 A ⇒ 𝕍 B
    Δ : iso (ΔProset.𝕍 A) ∧ Δ A ⇒ Δ B
    ok : ∀{dx x y} → ok A dx x y → ok B (Δ ! x , dx) (𝕍 ! x) (𝕍 ! y)

open ΔFun public

-- Almost but not quite the category ΔPoset from seminaive/semantics.pdf.
instance
  Δprosets : Cat (suc zero) zero
  Obj Δprosets = ΔProset
  Hom Δprosets = ΔFun
  ident Δprosets = ΔFun: id π₂ id
  compo Δprosets f g .𝕍 = 𝕍 f ∙ 𝕍 g
  -- (f ∙ g)' x dx = g' (f x) (f' x dx)
  compo Δprosets f g .Δ = Δ g $ ⟨ Iso % (𝕍 f) $ π₁ , Δ f ⟩
  compo Δprosets f g .ok = ok g ∘ ok f


-- Categorical structures (cartesian etc.)
⊤-Δproset ⊥-Δproset : ΔProset
⊤-Δproset = ΔProset: ⊤ ⊤ (λ { TT TT TT → ⊤ }) _ _ ≤⊤ λ { TT TT → TT }
⊥-Δproset = ΔProset: ⊥ ⊥ (λ{()}) (λ { {()} }) (λ { {()} }) (π₁ ∙ ⊥≤) λ { {()} }

module _ (A B : ΔProset) where
  -- private instance -A = A; -B = B
  Δproset× : ΔProset
  Δproset× .𝕍 = 𝕍 A ∧ 𝕍 B
  Δproset× .Δ = Δ A ∧ Δ B
  Δproset× .ok (da , db) (a , b) (a₂ , b₂) = ok A da a a₂ × ok B db b b₂
  Δproset× .complete = map∧ (complete A) (complete B) ∙ juggle
  Δproset× .sound = map∧ (sound A) (sound B)
  Δproset× .compo = fun juggle ∙ map∧ (compo A) (compo B)
  Δproset× .compok (da₁ , db₁) (da₂ , db₂) = compok A da₁ da₂ , compok B db₁ db₂

  data Δproset+ok : Δ₀ A ∨ Δ₀ B → 𝕍₀ A ∨ 𝕍₀ B → 𝕍₀ A ∨ 𝕍₀ B → Set where
    inj₁ : ∀{dx x y} → ok A dx x y → Δproset+ok (inj₁ dx) (inj₁ x) (inj₁ y)
    inj₂ : ∀{dx x y} → ok B dx x y → Δproset+ok (inj₂ dx) (inj₂ x) (inj₂ y)

  Δproset+ : ΔProset
  Δproset+ .𝕍 = 𝕍 A ∨ 𝕍 B
  Δproset+ .Δ = Δ A ∨ Δ B
  Δproset+ .ok = Δproset+ok
  Δproset+ .complete (inj₁ x) = Data.Product.map inj₁ inj₁ (complete A x)
  Δproset+ .complete (inj₂ x) = Data.Product.map inj₂ inj₂ (complete B x) 
  Δproset+ .sound (inj₁ x) = inj₁ (sound A x)
  Δproset+ .sound (inj₂ x) = inj₂ (sound B x)
  Δproset+ .compo = casesₗ (casesᵣ (inl (compo A)) (inl π₁))
                           (casesᵣ (inr π₁) (inr (compo B)))
  Δproset+ .compok (inj₁ ok₁) (inj₁ ok₂) = inj₁ (compok A ok₁ ok₂)
  Δproset+ .compok (inj₂ ok₁) (inj₂ ok₂) = inj₂ (compok B ok₁ ok₂)

  Δproset⇒ : ΔProset
  𝕍 Δproset⇒ = 𝕍 A ⇨ 𝕍 B
  Δ Δproset⇒ = (iso (𝕍 A) ∧ Δ A) ⇨ Δ B
  ok Δproset⇒ df f g = ∀{dx x y} → ok A dx x y → ok B (df ! x , dx) (f ! x) (g ! y)
  -- (f ⇝ g) x dx = (f x ⇝ g x) · g' x dx
  complete Δproset⇒ {f} {g} f≤g .proj₁ = compo B $ ⟨ {!complete B ?!} , {!!} ⟩
  complete Δproset⇒ {f} {g} f≤g .proj₂ = {!!}
  sound Δproset⇒ = {!!}
  compo Δproset⇒ = {!!}
  compok Δproset⇒ = {!!}

-- instance
--   products:Δproset : Products Δprosets
--   top products:Δproset = ⊤-Δproset , ΔFun: ≤⊤ (const ≤⊤) λ _ → TT
--   glb products:Δproset A B .a∧b = Δproset× A B
--   glb products:Δproset A B .∧E₁ = ΔFun: π₁ (const π₁) π₁
--   glb products:Δproset A B .∧E₂ = ΔFun: π₂ (const π₂) π₂
--   glb products:Δproset A B .∧I f g .𝕍 = ⟨ 𝕍 f , 𝕍 g ⟩
--   glb products:Δproset A B .∧I f g .Δ x = ⟨ Δ f x , Δ g x ⟩
--   glb products:Δproset A B .∧I f g .ok = ⟨ ok f , ok g ⟩

--   sums:Δproset : Sums Δprosets
--   bottom sums:Δproset = ⊥-Δproset , ΔFun: ⊥≤ (const ⊥≤) λ { {()} }
--   lub sums:Δproset A B .a∧b = Δproset+ A B
--   lub sums:Δproset A B .∧E₁ = ΔFun: in₁ (const in₁) inj₁
--   lub sums:Δproset A B .∧E₂ = ΔFun: in₂ (const in₂) inj₂
--   lub sums:Δproset A B .∧I f g .𝕍 = [ 𝕍 f , 𝕍 g ]
--   lub sums:Δproset A B .∧I f g .Δ (inj₁ x) = [ Δ f x , constant (Δ f x ! (𝟎 A x)) ]
--   lub sums:Δproset A B .∧I f g .Δ (inj₂ y) = [ constant (Δ g y ! 𝟎 B y) , Δ g y ]
--   lub sums:Δproset A B .∧I f g .ok (inj₁ x) = ok f x
--   lub sums:Δproset A B .∧I f g .ok (inj₂ y) = ok g y

--   cc:Δproset : CC Δprosets
--   cc:Δproset .hom = {!!}
--   cc:Δproset .CC.apply = {!!}
--   cc:Δproset .CC.curry = {!!}
