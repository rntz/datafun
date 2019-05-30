module Decidability where

open import Prelude
open import Cat
import Data.Sum

-- Decidability of the hom-sets of a proset/category.
Decidable≤ : ∀{i j} -> Cat i j -> Set _
Decidable≤ P = Decidable (Hom P)

dec¬ : ∀{i}{A : Set i} -> Dec A -> Dec (¬ A)
dec¬ (yes p) = no (λ x → x p)
dec¬ (no ¬p) = yes ¬p

dec× : ∀{i j P Q} -> Dec {i} P -> Dec {j} Q -> Dec (P × Q)
dec× (yes p) (yes q) = yes (p , q)
dec× (no ¬p) _ = no (λ { (x , y) -> ¬p x })
dec× _ (no ¬p) = no (λ { (x , y) -> ¬p y })

dec+ : ∀{i j P Q} → Dec {i} P → Dec {j} Q → Dec (P ⊎ Q)
dec+ (yes p) q = yes (inj₁ p)
dec+ (no ¬p) (yes p) = yes (inj₂ p)
dec+ (no ¬p) (no ¬q) = no Data.Sum.[ ¬p , ¬q ]

instance
  decidable× : ∀{i j k l A B} {R : Rel {i} A j} {S : Rel {k} B l}
             -> Decidable R -> Decidable S -> Decidable (rel× R S)
  decidable× P Q (a₁ , b₁) (a₂ , b₂) = dec× (P a₁ a₂) (Q b₁ b₂)

  decidable+ : ∀{i j k l A B} {R : Rel {i} A j} {S : Rel {k} B l}
             -> Decidable R -> Decidable S -> Decidable (rel+ R S)
  decidable+ P Q (inj₁ x) (inj₁ y) with P x y
  ... | yes p = yes (inj₁ p)
  ... | no ¬p = no (λ { (inj₁ x) → ¬p x })
  decidable+ P Q (inj₂ x) (inj₂ y) with Q x y
  ... | yes p = yes (inj₂ p)
  ... | no ¬p = no (λ { (inj₂ x) → ¬p x })
  decidable+ P Q (inj₁ x) (inj₂ y) = no λ {()}
  decidable+ P Q (inj₂ y) (inj₁ x) = no λ {()}
