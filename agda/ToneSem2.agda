{-# OPTIONS --postfix-projections #-}
module ToneSem2 where

open import Prelude
open import Cat

-- A tone is...
record Tone i j : Set (suc (i ⊔ j)) where
  constructor Tone:

  -- (1) A parametric transformation on orderings of a set...
  field rel : (A : Cat i j) → Rel (Obj A) j
  field rel-id : ∀{{A : Cat i j}} {a} → rel A a a
  field rel• : ∀{{A : Cat i j}} {a b c} → rel A a b → rel A b c → rel A a c

  -- (2) ... which is functorial, without changing function behavior.
  field functorial : ∀{A B} (f : Fun A B) -> rel A =[ ap f ]⇒ rel B

  at : Cat i j -> Cat i j
  at A .Obj = Obj A
  at A .Hom = rel A
  at A .ident = rel-id
  at A .compo = rel•

  functor : cats ≤ cats
  ap functor = at
  map functor f = fun (functorial f)

open Tone


-- Bidirectional paths in a category.
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


-- Datafun's four tones: id, op, iso, and path.
tone-id tone-op tone-iso : ∀{i j} → Tone i j
tone-id = Tone: Hom id _•_ map

tone-op .rel A x y = Hom A y x
tone-op .rel-id = id
tone-op .rel• f g = g • f
tone-op .functorial f = map f

-- This is the same as _≈_ from Cat.agda.
tone-iso .rel A x y = Hom A x y × Hom A y x
tone-iso .rel-id = id , id
tone-iso .rel• (f₁ , f₂) (g₁ , g₂) = f₁ • g₁ , g₂ • f₂
tone-iso .functorial f (i≤j , j≤i) = map f i≤j , map f j≤i

tone-path : ∀{i} → Tone i i
tone-path .rel = Path
tone-path .rel-id = path-by id
tone-path .rel• = path-•
tone-path .functorial f = path-fold _ (path-by ∘ map f) path⁻¹ path-•

-- If necessary, I could add discreteness & indiscreteness.


-- Tone transformations & functors
iso op : ∀{i j} → Cat i j → Cat i j
iso = at tone-iso; op = at tone-op

Iso Op : ∀{i j} → cats {i}{j} ≤ cats
Iso = functor tone-iso; Op = functor tone-op

-- TODO: derive Iso, Path, isos, paths, etc. from these. Then remove those from
-- Cat & Prosets and put them here. Rename this to Tones.agda, and rename
-- "tones" (the syntactic things) to "modes".
--
-- 1. rename "isos" to "iso"
-- 2. rename "Isos" to "Iso"

-- t-id t-op t-iso t-path : Tone
-- t-id = Tone: id map
-- t-op = Tone: opp (λ f → map f)
-- t-iso = Tone: isos (map ∘ map Isos)
-- t-path = Tone: paths (λ f → path-fold _ (path-by ∘ map f) path⁻¹ path-•)

-- -- The top & bottom tones, semantically: discreteness & indiscreteness
-- t-disc t-indisc : Tone
-- t-disc = Tone: (discrete ∘ Obj) λ { _ refl → refl }
-- t-indisc = Tone: (indiscrete ∘ Obj) λ { _ tt → tt }

-- instance
--   tones : Cat _ _
--   Obj tones = Tone
--   Hom tones T U = ∀{A} → at T A ≤ at U A
--   ident tones = id
--   compo tones T≤U U≤V = T≤U • U≤V

--   -- tone-sums : Sums tones
--   -- bottom tone-sums .proj₁ = t-disc
--   -- bottom tone-sums .proj₂ {T} {A} .ap rewrite id/Obj T {A} = id
--   -- bottom tone-sums .proj₂ {T} {A} .map refl = ident (at T A)
--   -- lub tone-sums T U .a∨b .at A .Obj = Obj A
--   -- lub tone-sums T U .a∨b .at A .Hom a b = rel T A a b ⊎ rel U A a b
--   -- lub tone-sums T U .a∨b .at A .ident = inj₁ {!ident (at T A)!}
--   -- lub tone-sums T U .a∨b .at A .compo = {!!}
--   -- lub tone-sums T U .a∨b .id/Obj = refl
--   -- lub tone-sums T U .a∨b .functorial = {!!}
--   -- lub tone-sums T U .∨I₁ = {!!}
--   -- lub tone-sums T U .∨I₂ = {!!}
--   -- lub tone-sums T U .∨E = {!!}
