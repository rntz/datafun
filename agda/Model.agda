module Model where

open import Cat
open import Prelude
open import Monads

-- A model of Datafun.
-- Argh, need to think about semantics of type-classes :(.
--
-- I guess I need notion of "semilattice in a category", which is annoying.
record Model : Set2 where
  field types : Cat (suc zero) zero
  field {{products}} : Products types
  field {{sums}} : Sums types
  field {{cc}} : CC types

  -- Discreteness.
  field □ : Fun types types
  field {{□-comonad}} : Comonad □

  -- TODO: typeclasses, DEC SL FIN ACC ACC≤
  -- that's a lot of structure, argh.
  --
  -- How do I semantically represent these properties, though?
  -- - decidability of equality
  -- - semilattice-ness
  -- - finiteness?! (probably not at all, I only care about this wrt ACC)
  -- - ACC
