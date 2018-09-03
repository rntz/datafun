{-# OPTIONS --postfix-projections #-}
module DepChanges where

open import Cat
open import Prelude
open import Tones
open import TreeSet
open import Booleans

 -- Prosets equipped with dependent change structures
record Change : Set1 where
  constructor Change:
  field {{𝑶}} : Proset               -- O for objects
  field 𝑫 : Rel (Obj 𝑶) zero

  -- isn't this just
  field path : ∀{a b : Obj 𝑶} -> (a ≤ b) ≈ 𝑫 a b

open Change public

 -- Constructions on change structures
⊤-change ⊥-change : Change
⊤-change = Change: {{⊤}} (λ _ _ → ⊤) ((λ _ → TT) , (λ _ → TT))
⊥-change = Change: {{⊥}} (λ { () }) (λ { {()} })

module _ (P : Proset) (S : Sums P) where
  private instance pp = P; ss = S
  change-SL : Change
  𝑶 change-SL = P
  𝑫 change-SL a b = Σ[ da ∈ Obj P ] (a ∨ da ≈ b)
  path change-SL .proj₁ a≤b = _ , [ a≤b , id ] , in₂
  path change-SL .proj₂ (da , a∨da≈b) = in₁ • proj₁ a∨da≈b
  -- path change-SL {a}{b} a≤b = b , [ a≤b , id ] , in₂
  -- path≤ change-SL (da , a∨da≈b) = in₁ • proj₁ a∨da≈b

change-bool : Change
change-bool = change-SL bools bool-sums

change-tree : Change -> Change
change-tree A = change-SL (trees (𝑶 A)) (tree-sums (𝑶 A))

change□ : Change -> Change
change□ A .𝑶 = iso (𝑶 A)
change□ A .𝑫 a b = 𝑫 A a b × 𝑫 A b a
change□ A .path = ∧≈ (path A) (path A)

module _ (A B : Change) where
  change× change+ : Change
  change× = Change: {{𝑶 A ∧ 𝑶 B}} (rel× (𝑫 A) (𝑫 B)) (∧≈ (path A) (path B))

  change+ .𝑶 = 𝑶 A ∨ 𝑶 B
  change+ .𝑫 = rel+ (𝑫 A) (𝑫 B)
  change+ .path = {!!}
  -- change+ .path .proj₁ (rel₁ x) = rel₁ (path A .proj₁ x)
  -- change+ .path .proj₁ (rel₂ x) = rel₂ (path B .proj₁ x)
  -- change+ .path .proj₂ = {!!}

  -- change+ .path (rel₁ a≤b) = rel₁ (path A a≤b)
  -- change+ .path (rel₂ a≤b) = rel₂ (path B a≤b)
  -- change+ .path≤ (rel₁ x) = rel₁ (path≤ A x)
  -- change+ .path≤ (rel₂ x) = rel₂ (path≤ B x)

--   change→ : Change
--   change→ .𝑶 = 𝑶 A ⇨ 𝑶 B
--   change→ .𝑫 f g = ∀{a b} (da : 𝑫 A a b) -> 𝑫 B (ap f a) (ap g b)
--   change→ .path f≤g = path≤ A • f≤g • path B
--   change→ .path≤ da x≤y = {!path≤ B (da (path A x≤y))!}
