module Monads where

open import Prelude
open import Cat

-- TODO: do we need this?
record Monad {i j C} (◇ : Fun {i}{j} C C) : Set (i ⊔ j) where
  constructor Monad:
  private instance cc = C
  field join : ∀{x} -> ap ◇ (ap ◇ x) ≤ ap ◇ x
  field pure : ∀{x} -> x ≤ ap ◇ x

  infixr 3 bind
  bind : ∀{a b} -> a ≤ ap ◇ b -> ap ◇ a ≤ ap ◇ b
  bind f = map ◇ f • join

-- TODO: define (Comonad F) as (Monad (map Op F))
record Comonad {i j C} (□ : Fun {i}{j} C C) : Set (i ⊔ j) where
  constructor Comonad:
  private instance cc = C
  field dup : ∀{x} -> ap □ x ≤ ap □ (ap □ x)
  field extract : ∀{x} -> ap □ x ≤ x

  extend : ∀{a b} -> ap □ a ≤ b -> ap □ a ≤ ap □ b
  extend f = dup • map □ f

module _ {i j} {{C}} (◇ : Fun {i}{j} C C) {{Mon : Monad ◇}} where
  join : ∀{a} -> ap ◇ (ap ◇ a) ≤ ap ◇ a; join = Monad.join Mon
  pure : ∀{a} -> a ≤ ap ◇ a;             pure = Monad.pure Mon

module _ {i j} {{C}} (□ : Fun {i}{j} C C) {{Com : Comonad □}} where
  dup : ∀{a} -> ap □ a ≤ ap □ (ap □ a); dup = Comonad.dup Com
  extract : ∀{a} -> ap □ a ≤ a;         extract = Comonad.extract Com
  open Comonad Com public using (extend)
