module Monads where

open import Prelude
open import Cat

record Monad {i j C} (◇ : Fun {i}{j} C C) : Set (i ⊔ j) where
  constructor Monad:
  private instance cc = C
  field join : ∀{x} -> ap ◇ (ap ◇ x) ≤ ap ◇ x
  field pure : ∀{x} -> x ≤ ap ◇ x

  infixr 3 bind
  bind : ∀{a b} -> a ≤ ap ◇ b -> ap ◇ a ≤ ap ◇ b
  bind f = map ◇ f ∙ join

-- Comonads are the dual of Monads, ie. Monads on the opposite category.
Comonad : ∀{i j C} (□ : Fun {i}{j} C C) → Set (i ⊔ j)
Comonad F = Monad (map Op F)

module Comonad {i j C} (□ : Fun {i}{j} C C) (Com : Monad (map Op □)) where
  open Monad Com public using ()
    renaming (join to dup; pure to extract; bind to extend)

-- Autoconversion. The other direction is true definitionally.
instance
  auto:monad→comonad : ∀{i j} {{C}} {◇ : Fun {i}{j} C C} → Monad ◇ → Comonad (map Op ◇)
  auto:monad→comonad m = Monad: (Monad.join m) (Monad.pure m)

-- A functor is a (co)monad in at most one way, so if you make the (co)Monad an
-- instance, you can call join, pure, &c by only supplying the functor.
module _ {i j} {{C}} (◇ : Fun {i}{j} C C) {{Mon : Monad ◇}} where
  join : ∀{a} -> ap ◇ (ap ◇ a) ≤ ap ◇ a; join = Monad.join Mon
  pure : ∀{a} -> a ≤ ap ◇ a;             pure = Monad.pure Mon

module _ {i j} {{C}} (□ : Fun {i}{j} C C) {{Com : Comonad □}} where
  dup : ∀{a} → ap □ a ≤ ap □ (ap □ a);  dup = Comonad.dup Com
  extract : ∀{a} → ap □ a ≤ a;          extract = Comonad.extract Com


module Tests where
  postulate C : Proset

  module Com→Mon where
    postulate □ : C ⇒ C; instance shub : Comonad □
    blub : Monad (map Op □); blub = shub

  module Mon→Com where
    postulate ◇ : C ⇒ C; instance blub : Monad ◇
    □ : op C ⇒ op C; □ = map Op ◇
    shub : Comonad □; shub = it
    instance opc = op C
    □-extend : ∀{a b} → ap □ a ≤ b → ap □ a ≤ ap □ b
    □-extend f = dup □ ∙ map □ f
