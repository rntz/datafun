module Monads where

open import Prelude
open import Cat

-- TODO: do we need this?
record Monad {i j C} (□ : Fun {i}{j} C C) : Set (i ⊔ j) where
  constructor Monad:
  private instance cc = C
  field join : ∀{x} -> ap □ (ap □ x) ≤ ap □ x
  field pure : ∀{x} -> x ≤ ap □ x

  infixr 3 bind
  bind : ∀{a b} -> a ≤ ap □ b -> ap □ a ≤ ap □ b
  bind f = map □ f • join

record Comonad {i j C} (□ : Fun {i}{j} C C) : Set (i ⊔ j) where
  constructor Comonad:
  private instance cc = C
  field dup : ∀{x} -> ap □ x ≤ ap □ (ap □ x)
  field extract : ∀{x} -> ap □ x ≤ x

  extend : ∀{a b} -> ap □ a ≤ b -> ap □ a ≤ ap □ b
  extend f = dup • map □ f

module _ {i j} {{C}} (□ : Fun {i}{j} C C) {{Com : Comonad □}} where
  dup : ∀{a} -> ap □ a ≤ ap □ (ap □ a); dup = Comonad.dup Com
  extract : ∀{a} -> ap □ a ≤ a;         extract = Comonad.extract Com
  open Comonad Com public using (extend)


private
  module Tests where
    data Tone : Set where mono disc : Tone
    postulate Type : Set
    open import Contexts (Tone × Type)

    -- Wipe is a comonad on contexts that removes all non-discrete variables.
    Wipe : cxs ≤ cxs
    ap Wipe X (mono , _) = ⊥
    ap Wipe X (disc , a) = X (disc , a)
    map Wipe f (mono , _) ()
    map Wipe f (disc , a) = f (disc , a)

    Wipe-comonad : Comonad Wipe
    -- dup : wipe X ⊆ wipe (wipe X)
    -- extract : wipe X ⊆ X
    Comonad.dup Wipe-comonad (mono , _) ()
    Comonad.dup Wipe-comonad (disc , a) = id
    Comonad.extract Wipe-comonad (mono , _) ()
    Comonad.extract Wipe-comonad (disc , a) = id

