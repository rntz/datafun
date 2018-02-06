module ComposeTest where

open import Level

-- A "quiver", or directed multigraph.
record Quiv i j : Set (suc (i ⊔ j)) where
  constructor quiv
  eta-equality
  field Obj : Set i
  field Arr : (a b : Obj) -> Set j

open Quiv public

-- Categorical structure (without laws), defined directly.
record Cat i j (A : Set i) (R : A -> A -> Set j) : Set (i ⊔ j) where
  field ident : ∀{a} -> R a a
  field compo : ∀{a b c} -> R a b -> R b c -> R a c

-- Categorical structure (without laws), defined on quivers.
record QuivCat i j (Q : Quiv i j) : Set (i ⊔ j) where
  field q-ident : ∀{a} -> Arr Q a a
  field q-compo : ∀{a b c} -> Arr Q a b -> Arr Q b c -> Arr Q a c

open QuivCat public; open Cat public

record Homo {i j k l} (A : Set i) (R : A -> A -> Set j)
                      (B : Set k) (S : B -> B -> Set l)
       : Set (i ⊔ j ⊔ k ⊔ l) where
  constructor Homo:
  field app : A -> B
  field cov : ∀{a b} -> R a b -> S (app a) (app b)

pattern homo {F} f = Homo: F f


-- Let's set up some instance machinery to make using categories convenient.
compose : ∀{i j A R} {{C : Cat i j A R}} {a b c} -> R a b -> R b c -> R a c
compose {{C}} = compo C

-- This is "naive" because it requires a quiver to be in context when we invoke it.
q-compose-naive : ∀{i j Q} {{C : QuivCat i j Q}} {a b c} -> Arr Q a b -> Arr Q b c -> Arr Q a c
q-compose-naive {{C}} = q-compo C

-- A less naive version, that feels like it should be equivalent to `compose`.
q-compose : ∀{i j A R} {{C : QuivCat i j (quiv A R)}} {a b c} -> R a b -> R b c -> R a c
q-compose {{C}} = q-compo C


-- Sets with functions form a category:
instance
  cat:Set : ∀{i} -> Cat _ _ (Set i) (λ a b -> a -> b)
  ident cat:Set x = x
  compo cat:Set f g x = g (f x)

  quivcat:Set : ∀{i} -> QuivCat _ _ (quiv (Set i) (λ a b -> a -> b))
  q-ident quivcat:Set x = x
  q-compo quivcat:Set f g x = g (f x)

  quivcat:Cat : ∀{i j} -> QuivCat _ _ (quiv (Quiv i j) (λ a b -> Homo (Obj a) (Arr a) (Obj b) (Arr b)))
  q-ident quivcat:Cat = homo (λ x → x)
  q-compo quivcat:Cat (homo f) (homo g) = homo (compose f g)


-- Okay, now let's try using this instance machinery we've set up:
_∘_ : ∀{a b c : Set} -> (b -> c) -> (a -> b) -> a -> c
f ∘ g = compose g f

-- -- So far so good.
-- _∘1_ : ∀{a b c : Set} -> (b -> c) -> (a -> b) -> a -> c
-- f ∘1 g = q-compose-naive g f

-- Uh-oh, that didn't work.
-- Maybe it's just because q-compose-naive is naive?
_∘2_ : ∀{a b c : Set} -> (b -> c) -> (a -> b) -> a -> c
_∘2_ {a} f g = q-compose {{_}} {a} g f

-- Huh. What went wrong? I'm stumped.
