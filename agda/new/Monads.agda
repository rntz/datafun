module Monads where

open import Prelude
open import Cat

-- TODO: Monadic.

record Comonadic {i j} (C : Cat i j) (□ : Fun C C) : Set (i ⊔ j) where
  private instance cc = C
  field dup : ∀{x : Obj C} -> ap □ x ≤ ap □ (ap □ x)
  field extract : ∀{x} -> ap □ x ≤ x

  extend : ∀{a b} -> ap □ a ≤ b -> ap □ a ≤ ap □ b
  extend f = dup • map □ f

-- Make □/dup/extract instance methods.
open Comonadic {{...}} public
