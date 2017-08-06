module Monads where

open import Prelude

-- TODO: Monadic.

record Comonadic {i j} (C : Cat i j) (□ : Functor C C) : Set (i ⊔ j) where
  private instance cc = C
  field dup : ∀{x : Obj C} -> ap □ x ⇨ ap □ (ap □ x)
  field extract : ∀{x} -> ap □ x ⇨ x

  extend : ∀{a b} -> (ap □ a ⇨ b) -> ap □ a ⇨ ap □ b
  extend f = dup • cov □ f

-- Make □/dup/extract instance methods.
open Comonadic {{...}} public
