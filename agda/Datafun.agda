module Datafun where

open import Prelude
open import Cat

mutual
  data Type : Set where
    □ : Type → Type
    set : (a : Type) (p : Eq! a) → Type
    unit : Type
    _*_ _+_ _⊃_ : Type → Type → Type

  data Eq! : Type -> Set where
    set  : ∀{a} p -> Eq! (set a p)
    unit : Eq! unit
    _*_  : ∀{a} (p : Eq! a) {b} (q : Eq! b) -> Eq! (a * b)
    _+_  : ∀{a} (p : Eq! a) {b} (q : Eq! b) -> Eq! (a + b)
    -- Case for □ causes problems for seminaive evaluation.

data Fin! : Type -> Set where
  set  : ∀{a p} -> Fin! a -> Fin! (set a p)
  _*_  : ∀{a} (p : Fin! a) {b} (q : Fin! b) -> Fin! (a * b)
  _+_  : ∀{a} (p : Fin! a) {b} (q : Fin! b) -> Fin! (a + b)
  -- could add a case for (a ⊃ b) here, but would never use it.

data SL! : Type -> Set where
  set  : ∀{a} p -> SL! (set a p)
  unit : SL! unit
  _*_  : ∀{a} (p : SL! a) {b} (q : SL! b) -> SL! (a * b)
  -- Case for _⊃_ causes problems for seminaive evaluation.

data Fix! : Type -> Set where
  set  : ∀{a p} -> Fin! a -> Fix! (set a p)
  unit : Fix! unit
  _*_  : ∀{a} (p : Fix! a) {b} (q : Fix! b) -> Fix! (a * b)

-- -- TODO: remove if unneeded.
-- data Class : Set where
--   _,_ : (A B : Class) → Class
--   Eq Fin SL Fix : Class

-- Is : Class → Type → Set
-- Is (C , D) a = Is C a × Is D a
-- Is Eq = Eq!; Is Fin = Fin!; Is SL = SL!; Is Fix = Fix!


-- Modes and contexts
data Mode : Set where Id □ : Mode
