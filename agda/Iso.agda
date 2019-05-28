-- Some lemmas about Tones.iso
open import Prelude
open import Cat
open import Monads
open import Decidability

module Iso where

instance
  -- This comonad factors into an adjunction to groupoids, I believe.
  Iso-comonad : ∀{i j} -> Comonad (Iso {i}{j})
  Comonad.dup Iso-comonad = fun ⟨ id , swap ⟩
  Comonad.extract Iso-comonad = fun proj₁

-- Comonads as monads on the opposite category.
-- TODO FIXME: remove this, it's how I define comonads anyway.
Com : ∀{i j C} (□ : Fun {i}{j} C C) → Set (i ⊔ j)
Com □ = Monad (map Op □)

instance
  Iso-com : ∀{i j} → Com (Iso {i}{j})
  Monad.join Iso-com = fun ⟨ id , swap ⟩
  Monad.pure Iso-com = fun proj₁

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
isojuggle = fun juggle ∙ map∧ ∧/iso id

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
