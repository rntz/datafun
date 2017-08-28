{-# OPTIONS --postfix-projections #-}
module CatOmega where

open import Prelude

open import Relation.Binary hiding (_⇒_)

mutual
  record Catω i : Set (suc i) where
    coinductive
    constructor Cat:
    infix  1 Hom
    infixr 9 compo
    field Obj : Set i
    field Hom : (a b : Obj) -> Catω i

    Arr : (a b : Obj) -> Set i
    Arr a b = O (Hom a b)

    field ident : ∀{a} -> Arr a a
    field compo : ∀{a b c} -> Arr a b -> Arr b c -> Arr a c

    record Iso (a b : Obj) : Set i where
      coinductive
      field a→b : Arr a b
      field b→a : Arr b a
      field ida : I (Hom a a) (ident) (compo a→b b→a)
      field idb : I (Hom b b) (ident) (compo b→a a→b)

  private
    O : ∀{i} -> Catω i -> Set i; O = Catω.Obj
    I : ∀{i} -> (C : Catω i) -> Rel (O C) i; I = Catω.Iso

open Catω public
open Catω {{...}} public using ()
  renaming (Iso to ≅; Arr to _≤_; ident to id; compo to _∙_)
open Iso public

infix 4 _≈_
_≈_ : ∀{i} {{C : Catω i}} {a b} (f g : a ≤ b) -> Set i
f ≈ g = Iso (Hom it _ _) f g

record Lawful {i} (C : Catω i) : Set i where
  private instance cc = C
  field idl : ∀{a b} (f : Arr C a b) -> f ≈ id ∙ f
  field idr : ∀{a b} (f : Arr C a b) -> f ≈ f ∙ id
  field assoc : ∀{a b c d} -> (f : a ≤ b) (g : b ≤ c) (h : c ≤ d) -> f ∙ (g ∙ h) ≈ (f ∙ g) ∙ h


-- -- Top category.
-- pattern TT = lift tt

-- mutual
--   ⊤-cat : ∀{i} -> Catω i
--   ⊤-cat .Obj = Lift ⊤
--   ⊤-cat .Hom TT TT = ⊤-cat
--   ⊤-cat .ident = TT
--   ⊤-cat .compo TT TT = TT
--   ⊤-cat .idl TT = ⊤-iso
--     where ⊤-iso : Iso ⊤-cat TT TT
--           ⊤-iso .a→b = TT
--           ⊤-iso .b→a = TT
--           ⊤-iso .ida = ⊤-iso
--           ⊤-iso .idb = ⊤-iso
--   -- ⊤-cat .idl TT .a→b = TT
--   -- ⊤-cat .idl TT .b→a = TT
--   -- ⊤-cat .idl TT .ida = {!!}
--   -- ⊤-cat .idl TT .idb = {!!}
--   ⊤-cat .idr TT = {!!}
--   ⊤-cat .assoc = {!!}

--   ⊤-iso : Iso ⊤-cat TT TT
--   ⊤-iso = {!!}

-- -- Indiscrete Catω, where every object is connected to every other by a unique
-- -- morphism.
-- Indiscrete : ∀{i} -> Set i -> Catω _
-- Indiscrete A .Obj = A
-- Indiscrete A .Hom = {!!}
-- Indiscrete A .ident = {!!}
-- Indiscrete A .compo = {!!}
-- Indiscrete A .idl = {!!}
-- Indiscrete A .idr = {!!}
-- Indiscrete A .assoc = {!!}

-- -- Given a setoid, we can make a category?
-- setoid→cat : ∀{i j} -> Setoid i j -> Catω _
-- setoid→cat S .Obj = Setoid.Carrier S
-- setoid→cat S .Hom = {!!}
-- setoid→cat S .ident = {!!}
-- setoid→cat S .compo = {!!}
-- setoid→cat S .idl = {!!}
-- setoid→cat S .idr = {!!}
-- setoid→cat S .assoc = {!!}

-- -- -- Sets and functions form Catω.
-- -- sets : ∀ i -> Catω _
-- -- sets i .Obj = Set i
-- -- sets i .Hom a b .Obj = Lift (a -> b)
-- -- sets i .Hom a b .Hom = {!!}
-- -- sets i .Hom a b .ident = {!!}
-- -- sets i .Hom a b .compo = {!!}
-- -- sets i .Hom a b .idl = {!!}
-- -- sets i .Hom a b .idr = {!!}
-- -- sets i .Hom a b .assoc = {!!}
-- -- sets i .ident = {!!}
-- -- sets i .compo = {!!}
-- -- sets i .idl = {!!}
-- -- sets i .idr = {!!}
-- -- sets i .assoc = {!!}

-- 
-- -- Holy shit.
