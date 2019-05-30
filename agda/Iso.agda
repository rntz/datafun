-- Some lemmas about Tones.iso
open import Prelude
open import Cat
open import Monads
open import Decidability

module Iso where

instance
  -- This comonad factors into an adjunction to groupoids.
  Iso-comonad : ∀{i j} -> Comonad (Iso {i}{j})
  Comonad.dup Iso-comonad = fun ⟨ id , swap ⟩
  Comonad.extract Iso-comonad = fun proj₁

iso≤? : ∀{i j} (A : Cat i j) -> Decidable≤ A -> Decidable≤ (iso A)
iso≤? _ test x y = dec× (test x y) (test y x)

⊤⇒iso : ⊤ ⇒ iso ⊤
⊤⇒iso = fun (λ {TT  → TT , TT})

∧/iso : ∀{A B} -> iso A ∧ iso B ⇒ iso (A ∧ B)
∧/iso = fun juggle

iso/∧ : ∀{A B} -> iso (A ∧ B) ⇒ iso A ∧ iso B
iso/∧ = fun juggle

iso/∨ : ∀{A B} -> iso (A ∨ B) ⇒ iso A ∨ iso B
iso/∨ .ap = id
iso/∨ .map (inj₁ p , inj₁ q) = inj₁ (p , q)
iso/∨ .map (inj₂ p , inj₂ q) = inj₂ (p , q)

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
