module Monads where

open import Prelude

-- TODO: Monadic.

record Comonadic {i j} (C : Cat i j) (□ : Functor C C) : Set (i ⊔ j) where
  field dup : ∀{x} -> ap □ x ⇨ ap □ (ap □ x)
  field extract : ∀{x} -> ap □ x ⇨ x

-- Make □/dup/extract instance methods.
open Comonadic {{...}} public
