---------- Tones ----------
open import Prelude
open import Cat.Base

module Cat.Tones where

-- NB. Without eta-equality on categories, (Tone.at tone-id C) isn't
-- definitionally equal to C!
--
-- This could be fixed by making (at : Cat i j → Cat i j) a field rather than a
-- defined function, and adding a field requiring that the at field agrees with
-- its definition. However, this still won't get (op (op C)) to be
-- definitionally equal to C!
record Tone i j : Set (suc (i ⊔ j)) where
  constructor Tone:

  -- A tone is...
  -- (1) A parametric transformation on orderings of a set...
  field rel : (A : Cat i j) → Rel (Obj A) j
  field rel-id : ∀{{A : Cat i j}} {a} → rel A a a
  field rel∙ : ∀{{A : Cat i j}} {a b c} → rel A a b → rel A b c → rel A a c

  -- (2) ... which is functorial, without changing function behavior.
  field covary : ∀{A B} (f : Fun A B) -> rel A =[ ap f ]⇒ rel B

  at : Cat i j -> Cat i j
  at A .Obj = Obj A
  at A .Hom = rel A
  at A .ident = rel-id
  at A .compo = rel∙

  functor : cats i j ≤ cats _ _
  ap functor = at
  map functor f = fun (covary f)


-- Four tones.
tone-id tone-op tone-iso : ∀{i j} → Tone i j
tone-id = Tone: Hom id _∙_ map

Tone.rel tone-op A x y = Hom A y x
Tone.rel-id tone-op = id
Tone.rel∙ tone-op f g = g ∙ f
Tone.covary tone-op f = map f

-- The "equivalence quotient" of a proset. Not actually a category of
-- isomorphisms, since we don't require that the arrows be inverses. But *if* we
-- were gonna put equations on arrows, that's what we'd require.
Tone.rel tone-iso A x y = Hom A x y × Hom A y x -- Same as _≈_.
Tone.rel-id tone-iso = id , id
Tone.rel∙ tone-iso (f₁ , f₂) (g₁ , g₂) = f₁ ∙ g₁ , g₂ ∙ f₂
Tone.covary tone-iso f (i≤j , j≤i) = map f i≤j , map f j≤i

tone-path : ∀{i} → Tone i i
Tone.rel tone-path = Connected
Tone.rel-id tone-path = path-by id
Tone.rel∙ tone-path = path∙
Tone.covary tone-path f = path-fold _ (path-by ∘ map f) path⁻¹ path∙

-- Tone functors.
iso op : ∀{i j} → Cat i j → Cat i j
iso = Tone.at tone-iso; op = Tone.at tone-op

Iso Op : ∀{i j} → cats i j ≤ cats _ _
Iso = Tone.functor tone-iso; Op = Tone.functor tone-op

instance -- The category of tones.
  tones : ∀{i j} → Cat (suc (i ⊔ j)) (suc (i ⊔ j))
  Obj (tones {i}{j}) = Tone i j
  Hom tones T U = ∀{A} → Tone.at T A ≤ Tone.at U A
  ident tones = id
  compo tones T≤U U≤V = T≤U ∙ U≤V
