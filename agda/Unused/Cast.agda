module Unused.Cast where

open import Level

record Convert {i j} (A : Set i) (B : Set j) : Set (i ⊔ j) where
  field convert : A -> B

open Convert public
open Convert {{...}} public using () renaming (convert to cast)

instance
  convert-id : ∀{i a} -> Convert {i} a a
  convert-id .convert x = x

-- Use Cast and Cast: to define casts which compose automatically.
Cast : ∀{i j} k (A : Set i) (B : Set j) -> Set (i ⊔ j ⊔ suc k)
Cast k A B = ∀{src : Set k} {{C : Convert src A}} -> Convert src B

Cast: : ∀{i j k A B} -> (A -> B) -> Cast {i}{j} k A B
Cast: f .convert x = f (cast x)

-- A common use-case: turning things into sets.
obj : ∀{i j A} {{C : Convert {i} A (Set j)}} -> A -> Set j
obj = cast

 -- Examples
private
  module Examples where
    postulate
      ℕ ℤ ℝ : Set
      nat->int : ℕ -> ℤ
      int->real : ℤ -> ℝ

    instance
      cast:nat->int : ∀{i} -> Cast i ℕ ℤ
      cast:nat->int = Cast: nat->int

      cast:int->real : ∀{i} -> Cast i ℤ ℝ
      cast:int->real = Cast: int->real

    nop : ℕ -> ℕ
    duh : ℕ -> ℤ
    nat->real : ℕ -> ℝ
    nop = cast; duh = cast; nat->real = cast
