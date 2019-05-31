{-# OPTIONS --postfix-projections #-}
module Changes where

open import Prelude
open import Cat
import Data.Product

record ΔProset : Set1 where
  no-eta-equality
  constructor ΔProset:
  field 𝕍 Δ : Proset
  private instance -𝕍 = 𝕍; -Δ = Δ
  𝕍₀ = Obj 𝕍
  Δ₀ = Obj Δ

  field valid : Δ₀ → 𝕍₀ → 𝕍₀ → Set
  -- -- Do I need that `valid` is functional? Let's assume no for now.
  -- field functional : ∀{dx₁ x₁ y₁} → valid dx₁ x₁ y₁
  --                  → ∀{dx₂ x₂ y₂} → valid dx₂ x₂ y₂
  --                  → dx₁ ≈ dx₂ → x₁ ≈ x₂ → y₁ ≈ y₂

  -- Wait, shit. These shouldn't need to be computable! Will this be an issue?
  field complete : ∀{x y} → x ≤ y → ∃[ dx ] valid dx x y
  field sound : ∀{dx x y} → valid dx x y → x ≤ y

  𝟎 : 𝕍₀ → Δ₀
  𝟎 x = complete {x} id .proj₁
  is𝟎 : ∀ x → valid (𝟎 x) x x
  is𝟎 x = complete {x} id .proj₂

open ΔProset public using (𝕍; Δ; valid; complete; sound; 𝟎; is𝟎; 𝕍₀; Δ₀)

record ΔFun (A B : ΔProset) : Set where
  constructor ΔFun:
  field 𝕍 : 𝕍 A ⇒ 𝕍 B
  field Δ : 𝕍₀ A → Δ A ⇒ Δ B
  field valid : ∀{dx x y}
              → valid A dx x y
              → valid B (Δ x .ap dx) (ap 𝕍 x ) (ap 𝕍 y)

open ΔFun public

-- Almost but not quite the category ΔPoset from seminaive/semantics.pdf.
instance
  Δprosets : Cat (suc zero) zero
  Obj Δprosets = ΔProset
  Hom Δprosets = ΔFun
  ident Δprosets = record { 𝕍 = id ; Δ = λ x → id ; valid = id }
  compo Δprosets f g .𝕍 = 𝕍 f ∙ 𝕍 g
  compo Δprosets f g .Δ x .ap dx = Δ g (𝕍 f .ap x) .ap (Δ f x .ap dx)
  compo Δprosets f g .Δ a .map dx≤dy = Δ g (𝕍 f .ap a) .map (Δ f a .map dx≤dy)
  compo Δprosets f g .valid dx:x→y = valid g (valid f dx:x→y)


-- Categorical structures (cartesian etc.)
⊤-Δproset ⊥-Δproset : ΔProset
⊤-Δproset = ΔProset: ⊤ ⊤ (λ { TT TT TT → ⊤ }) _ _
⊥-Δproset = ΔProset: ⊥ ⊥ (λ{()}) (λ { {()} }) λ { {()} }

module _ (A B : ΔProset) where
  private instance -A = A; -B = B
  Δproset× : ΔProset
  Δproset× .𝕍 = 𝕍 A ∧ 𝕍 B
  Δproset× .Δ = Δ A ∧ Δ B
  Δproset× .valid (da , db) (a , b) (a₂ , b₂) = valid A da a a₂ × valid B db b b₂
  Δproset× .complete = map∧ (complete A) (complete B) ∙ juggle
  Δproset× .sound = map∧ (sound A) (sound B)

  data Δproset+valid : Δ₀ A ∨ Δ₀ B → 𝕍₀ A ∨ 𝕍₀ B → 𝕍₀ A ∨ 𝕍₀ B → Set where
    inj₁ : ∀{dx x y} → valid A dx x y → Δproset+valid (inj₁ dx) (inj₁ x) (inj₁ y)
    inj₂ : ∀{dx x y} → valid B dx x y → Δproset+valid (inj₂ dx) (inj₂ x) (inj₂ y)

  Δproset+ : ΔProset
  Δproset+ .𝕍 = 𝕍 A ∨ 𝕍 B
  Δproset+ .Δ = Δ A ∨ Δ B
  Δproset+ .valid = Δproset+valid
  Δproset+ .complete (inj₁ x) = Data.Product.map inj₁ inj₁ (complete A x)
  Δproset+ .complete (inj₂ x) = Data.Product.map inj₂ inj₂ (complete B x) 
  Δproset+ .sound (inj₁ x) = inj₁ (sound A x)
  Δproset+ .sound (inj₂ x) = inj₂ (sound B x)

  open Fun!%
  Δproset⇒ : ΔProset
  𝕍 Δproset⇒ = 𝕍 A ⇨ 𝕍 B
  Δ Δproset⇒ = iso (𝕍 A) ⇨ (Δ A ⇨ Δ B)
  valid Δproset⇒ df f g = ∀{dx x y} → valid A dx x y
                        → valid B (df ! x ! dx) (f ! x) (g ! y)
  -- uh-oh, this just doesn't hold in general. back to the drawing board.
  complete Δproset⇒ {f} {g} f≤g .proj₁ = {!!}
  complete Δproset⇒ {f} {g} f≤g .proj₂ = {!!}
  sound Δproset⇒ = {!!}

instance
  products:Δproset : Products Δprosets
  top products:Δproset = ⊤-Δproset , ΔFun: ≤⊤ (const ≤⊤) λ _ → TT
  glb products:Δproset A B .a∧b = Δproset× A B
  glb products:Δproset A B .∧E₁ = ΔFun: π₁ (const π₁) π₁
  glb products:Δproset A B .∧E₂ = ΔFun: π₂ (const π₂) π₂
  glb products:Δproset A B .∧I f g .𝕍 = ⟨ 𝕍 f , 𝕍 g ⟩
  glb products:Δproset A B .∧I f g .Δ x = ⟨ Δ f x , Δ g x ⟩
  glb products:Δproset A B .∧I f g .valid = ⟨ valid f , valid g ⟩

  sums:Δproset : Sums Δprosets
  bottom sums:Δproset = ⊥-Δproset , ΔFun: ⊥≤ (const ⊥≤) λ { {()} }
  lub sums:Δproset A B .a∧b = Δproset+ A B
  lub sums:Δproset A B .∧E₁ = ΔFun: in₁ (const in₁) inj₁
  lub sums:Δproset A B .∧E₂ = ΔFun: in₂ (const in₂) inj₂
  lub sums:Δproset A B .∧I f g .𝕍 = [ 𝕍 f , 𝕍 g ]
  lub sums:Δproset A B .∧I f g .Δ (inj₁ x) = [ Δ f x , constant (Δ f x .ap (𝟎 A x)) ]
  lub sums:Δproset A B .∧I f g .Δ (inj₂ y) = [ constant (Δ g y .ap (𝟎 B y)) , Δ g y ]
  lub sums:Δproset A B .∧I f g .valid (inj₁ x) = valid f x
  lub sums:Δproset A B .∧I f g .valid (inj₂ y) = valid g y

  cc:Δproset : CC Δprosets
  cc:Δproset .hom = {!!}
  cc:Δproset .CC.apply = {!!}
  cc:Δproset .CC.curry = {!!}
