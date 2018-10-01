module Examples.Monoid where

open import Cat
open import Prelude
open import Action

-- record Monoid i j : Set (suc (i ⊔ j)) where
--   field {{elems}} : Cat i j
--   Elem = Obj elems
--   field empty : Elem
--   field Append : Fun (elems ∧ elems) elems
--   append = ap Append
--   field idl : ∀{x} → x ≈ append (empty , x)
--   field idr : ∀{x} → x ≈ append (x , empty)
--   field assoc : ∀{x y z} →
--                 append (append (x , y) , z)
--                 ≈ append (x , append (y , z))

-- monoids : ∀{i j} → Cat _ _
-- monoids {i}{j} .Obj = Monoid i j
-- Hom monoids A B = {!!}
-- ident monoids = {!!}
-- compo monoids = {!!}

-- -- TODO
-- record MonoidAction {i j} (M : Monoid {i}{j})

-- instance
--   monoid-action : ∀{i j} (m : Monoid {i}{j}) → Action (Monoid.Elem m) (Monoid.Elem m)
--   monoid-action = {!!}
