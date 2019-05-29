{-# OPTIONS --postfix-projections #-}
module Changes where

open import Prelude
open import Cat

record ΔProset : Set1 where
  field {{𝕍}} {{Δ}} : Proset
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
  compo Δprosets F G .𝕍 = 𝕍 F ∙ 𝕍 G
  compo Δprosets F G .Δ x .ap dx = Δ G (𝕍 F .ap x) .ap (Δ F x .ap dx)
  compo Δprosets F G .Δ a .map dx≤dy = Δ G (𝕍 F .ap a) .map (Δ F a .map dx≤dy)
  compo Δprosets F G .valid dx:x→y = valid G (valid F dx:x→y)


-- Categorical structures (cartesian etc.)
