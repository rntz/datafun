{-# OPTIONS --postfix-projections #-}
module Changes2 where

open import Cat
open import Prelude
open import Prosets
open import TreeSet

import Data.Product as Product


-- Prosets equipped with change structures
record Change : Set1 where
  constructor Change:
  field {{𝑶}} : Proset          -- O for objects
  field 𝑫 : Proset              -- D for deltas

  -- this needs to respect equivalence of objects & deltas, doesn't it? I think
  -- for all the ones we actually construct this will be the case; I'm not sure
  -- if we need it for any of the proofs we're doing.
  field Path : (da : Obj 𝑫) (a b : Obj 𝑶) -> Set

  field path : ∀{a b} (a≤b : a ≤ b) -> ∃ λ da -> Path da a b

open Change public

 -- Constructions on change structures
data rel3+ {A A' B B' C C' : Set} (R : A -> B -> C -> Set) (S : A' -> B' -> C' -> Set)
           : A ⊎ A' -> B ⊎ B' -> C ⊎ C' -> Set where
  rel₁ : ∀{a b c} -> R a b c -> rel3+ R S (inj₁ a) (inj₁ b) (inj₁ c)
  rel₂ : ∀{a b c} -> S a b c -> rel3+ R S (inj₂ a) (inj₂ b) (inj₂ c)

⊤-change ⊥-change : Change
⊤-change = Change: {{⊤-cat}} ⊤-cat (λ da a b → ⊤) (λ _ → lift tt , tt)
⊥-change = Change: {{⊥-cat}} ⊤-cat (λ { _ (lift ()) }) (λ { {lift ()} })

change-SL : (P : Proset) (S : Sums P) -> Change
change-SL P S = Change: {{P}} P (λ da a b → a ∨ da ≈ b) (λ {a}{b} a≤b → b , [ a≤b , id ] , in₂)
  where instance p = P; s = S

change-bool : Change
change-bool = change-SL bools bool-sums

change-tree : Change -> Change
change-tree A = change-SL (trees (𝑶 A)) (tree-sums (𝑶 A))

changeΠ : (A : Set) (B : A -> Change) -> Change
changeΠ A B .𝑶 = catΠ A (λ a -> B a .𝑶)
changeΠ A B .𝑫 = catΠ A (λ a -> B a .𝑫)
changeΠ A B .Path df f g = ∀ a -> Path (B a) (df a) (f a) (g a)
changeΠ A B .path f≤g = (λ a → path (B a) (f≤g a) .proj₁) , (λ a → path (B a) (f≤g a) .proj₂)

module _ (A : Change) where
  change□ : Change
  𝑶 change□ = isos (𝑶 A)
  𝑫 change□ = isos (𝑫 A)
  -- could I weaken a ≈ b to b ≤ a? probably, if I had (path A da a b -> a ≤ b)!
  -- if I had that, I could also make this (Path A da a b × Path A da b a).
  Path change□ da a b = Path A da a b ∧ (a ≈ b)
  path change□ a≈b@(a≤b , _) with path A a≤b
  ... | (da , da-ok) = da , da-ok , a≈b

module _ (A B : Change) where
  change× change+ change→ : Change
  change× = Change: {{𝑶 A ∧ 𝑶 B}} (𝑫 A ∧ 𝑫 B) paths (map∧ (path A) (path B) • juggle)
    where paths = λ { (da , db) → rel× (Path A da) (Path B db) }

  change+ = Change: {{𝑶 A ∨ 𝑶 B}} (𝑫 A ∨ 𝑫 B) (rel3+ (Path A) (Path B))
                    (λ { (rel₁ x) → Product.map inj₁ rel₁ (path A x)
                       ; (rel₂ x) → Product.map inj₂ rel₂ (path B x) })

  𝑶 change→ = 𝑶 A ⇨ 𝑶 B
  𝑫 change→ = (isos (𝑶 A) ∧ 𝑫 A) ⇨ 𝑫 B
  Path change→ df f g = ∀{da a b} (da:a→b : Path A da a b)
                      -> Path B (ap df (a , da)) (ap f a) (ap g b)
  -- and here, we have the problem.
  path change→ f≤g .proj₁ .ap (a , da) = {!!}
  path change→ f≤g .proj₁ .map = {!!}
  path change→ f≤g .proj₂ = {!!}

--  -- Morphisms between change structures.
-- record Deriv (A B : Change) (F : 𝑶 A ⇒ 𝑶 B) : Set where
--   constructor Deriv:
--   field δ : isos (𝑶 A) ∧ 𝑫 A ⇒ 𝑫 B
--   field isδ : Path (change→ A B) δ F F

-- record ChangeFun (A B : Change) : Set where
--   constructor cfun
--   field func  : 𝑶 A ⇒ 𝑶 B
--   field deriv : isos (𝑶 A) ∧ 𝑫 A ⇒ 𝑫 B
--   field is-id : Path (change→ A B) deriv func func

--   func&deriv : isos (𝑶 A) ∧ 𝑫 A ⇒ isos (𝑶 B) ∧ 𝑫 B
--   func&deriv = ⟨ π₁ • map Isos func , deriv ⟩

--   to-deriv : Deriv A B func
--   to-deriv = Deriv: deriv is-id

-- open Deriv public
-- open ChangeFun public
