{-# OPTIONS --postfix-projections #-}
module ToneSem where

open import Prelude
open import Cat
open import Prosets

-- A tone is...
record Tone : Set1 where
  constructor Tone:
  -- (1) ... A transformation on preorders...
  field at : Proset -> Proset

  -- (2) ... which preserves their elements...
  field {{id/Obj}} : ∀{A} -> Obj A ≡ at A .Obj
  at-map : ∀{A B} -> (Obj A -> Obj B) -> Obj (at A) -> Obj (at B)
  at-map f = coerce (Eq.cong₂ Function id/Obj id/Obj) f

  -- (3) ... and is functorial.
  field functorial : ∀{A B} (f : A ⇒ B) -> Hom (at A) =[ at-map (ap f) ]⇒ Hom (at B)
  functor : prosets ≤ prosets
  ap functor = at
  map functor f = fun (functorial f)

open Tone


-- Infrastructure for some actual tones. This should perhaps go in Cat.agda.
opp : ∀{i j} -> Cat i j -> Cat i j
opp C = Cat: (Obj C) (λ a b → Hom C b a) (ident C) (λ f g → compo C g f)

module _  {i j} (C : Cat i j) where
  data Path : (a b : Obj C) -> Set (i ⊔ j) where
    path-by : ∀{a b} -> Hom C a b -> Path a b
    path⁻¹ : ∀{a b} -> Path a b -> Path b a
    path-• : ∀{a b c} -> Path a b -> Path b c -> Path a c

module _ {i j k} {C : Cat i j}
         (F : (a b : Obj C) -> Set k)
         (hom→F : ∀{a b} -> Hom C a b -> F a b)
         (F-symm : Symmetric F)
         (F-trans : Transitive F) where
  path-fold : ∀{a b} -> Path C a b -> F a b
  path-fold (path-by x) = hom→F x
  path-fold (path⁻¹ p) = F-symm (path-fold p)
  path-fold (path-• p q) = F-trans (path-fold p) (path-fold q)

paths : ∀{i j} -> Cat i j -> Cat i (i ⊔ j)
paths C = Cat: (Obj C) (Path C) (path-by (ident C)) path-•


-- Datafun's four tones: id, op, iso, and path.
t-id t-op t-iso t-path : Tone
t-id = Tone: id map
t-op = Tone: opp (λ f → map f)
t-iso = Tone: isos (map ∘ map Isos)
t-path = Tone: paths (λ f → path-fold _ (path-by ∘ map f) path⁻¹ path-•)

-- TODO: the category of tones!
instance
  tones : Cat _ _
  Obj tones = Tone
  Hom tones = {!!}
  ident tones = {!!}
  compo tones = {!!}
