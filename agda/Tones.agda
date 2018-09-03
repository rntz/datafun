{-# OPTIONS --postfix-projections #-}
module Tones where

open import Prelude
open import Cat
open import Monads
open import Decidability

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
  data Pathto : (a b : Obj C) -> Set (i ⊔ j) where
    path-by : ∀{a b} -> Hom C a b -> Pathto a b
    path⁻¹ : ∀{a b} -> Pathto a b -> Pathto b a
    path-• : ∀{a b c} -> Pathto a b -> Pathto b c -> Pathto a c

module _ {i j k} {C : Cat i j}
         (F : (a b : Obj C) -> Set k)
         (hom→F : ∀{a b} -> Hom C a b -> F a b)
         (F-symm : Symmetric F)
         (F-trans : Transitive F) where
  path-fold : ∀{a b} -> Pathto C a b -> F a b
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

-- The "equivalence quotient" of a proset. Not actually a category of
-- isomorphisms, since we don't require that the arrows be inverses. But *if* we
-- were gonna put equations on arrows, that's what we'd require.
tone-iso .rel A x y = Hom A x y × Hom A y x
tone-iso .rel-id = id , id -- Same as _≈_ from Cat.agda.
tone-iso .rel• (f₁ , f₂) (g₁ , g₂) = f₁ • g₁ , g₂ • f₂
tone-iso .functorial f (i≤j , j≤i) = map f i≤j , map f j≤i

tone-path : ∀{i} → Tone i i
tone-path .rel = Pathto
tone-path .rel-id = path-by id
tone-path .rel• = path-•
tone-path .functorial f = path-fold _ (path-by ∘ map f) path⁻¹ path-•

-- If necessary, I could add discreteness & indiscreteness.


-- Tone transformations & functors
iso op : ∀{i j} → Cat i j → Cat i j
iso = at tone-iso; op = at tone-op

Iso Op : ∀{i j} → cats {i}{j} ≤ cats
Iso = functor tone-iso; Op = functor tone-op


-- TODO: Is this necessary? Remove if not.
instance
  tones : ∀{i j} → Cat _ _
  Obj (tones {i}{j}) = Tone i j
  Hom tones T U = ∀{A} → at T A ≤ at U A
  ident tones = id
  compo tones T≤U U≤V = T≤U • U≤V

 -- Some lemmas about iso.
instance
  -- This comonad factors into an adjunction to groupoids, I believe.
  Iso-comonad : ∀{i j} -> Comonad (Iso {i}{j})
  Comonad.dup Iso-comonad = fun ⟨ id , swap ⟩
  Comonad.extract Iso-comonad = fun proj₁

iso≤? : ∀{i j} (A : Cat i j) -> Decidable≤ A -> Decidable≤ (iso A)
iso≤? _ test x y = dec× (test x y) (test y x)

⊤⇒iso : ⊤ ⇒ iso ⊤
⊤⇒iso = fun (λ {TT  → TT , TT})

juggle : ∀{i j k l} {A B C D}
       -> Σ {i}{j} A C × Σ {k}{l} B D
       -> Σ (A × B) λ { (a , b) -> C a × D b }
juggle ((a , c) , (b , d)) = (a , b) , (c , d)

∧/iso : ∀{A B} -> iso A ∧ iso B ⇒ iso (A ∧ B)
∧/iso = fun juggle

iso/∧ : ∀{A B} -> iso (A ∧ B) ⇒ iso A ∧ iso B
iso/∧ = fun juggle

iso/∨ : ∀{A B} -> iso (A ∨ B) ⇒ iso A ∨ iso B
iso/∨ .ap = id
iso/∨ .map (rel₁ p , rel₁ q) = rel₁ (p , q)
iso/∨ .map (rel₂ p , rel₂ q) = rel₂ (p , q)

isojuggle : ∀{A B C D} -> (iso A ∧ B) ∧ (iso C ∧ D) ⇒ iso (A ∧ C) ∧ (B ∧ D)
isojuggle = fun juggle • map∧ ∧/iso id

module _ {i j} {{A : Cat i j}} {{Prod : Products A}} where
  ∧≈ : ∀{a b a' b' : Obj A} -> a ≈ a' -> b ≈ b' -> (a ∧ b) ≈ (a' ∧ b')
  ∧≈ f g = map Iso functor∧ .map (juggle (f , g))

module _ {i j} {{A : Cat i j}} {{Sum : Sums A}} where
  juggle∨≈ : ∀{a b c d : Obj A} -> (a ∨ b) ∨ (c ∨ d) ≈ (a ∨ c) ∨ (b ∨ d)
  juggle∨≈ = juggle∨ , juggle∨

  -- Used in ChangeSem/Types*.agda
  ∨≈ : ∀{a b a' b' : Obj A} -> a ≈ a' -> b ≈ b' -> (a ∨ b) ≈ (a' ∨ b')
  ∨≈ f g = map Iso functor∨ .map (juggle (f , g))

-- Lifts an arbitrary function over an antisymmetric domain into a monotone map
-- over its preorder of isomorphisms.
antisym⇒ : ∀{A B} -> Antisymmetric _≡_ (Hom A) -> (Obj A -> Obj B) -> iso A ⇒ B
antisym⇒ {A}{B} antisym f = Fun: f helper
  where helper : ∀{x y} -> Hom (iso A) x y -> Hom B (f x) (f y)
        helper (x , y) with antisym x y
        ... | refl = ident B
