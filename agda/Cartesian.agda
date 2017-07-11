module Cartesian where

open import Level
open import Data.Product hiding (curry; uncurry; swap)
open import Data.Sum hiding ([_,_])

open import Cat

-- Technically, none of this needs Cat. It just needs SetRel/Graph/Quiv! Hm...

cat:× : ∀{i j} (A B : Cat i j) -> Cat i j
Obj (cat:× A B) = Obj A × Obj B
Hom (cat:× A B) (a₁ , b₁) (a₂ , b₂) = (a₁ ⇨ a₂) × (b₁ ⇨ b₂)
identity (isCat (cat:× (cat A) (cat B))) = id , id
compose (isCat (cat:× (cat A) (cat B))) (f₁ , f₂) (g₁ , g₂) = f₁ • g₁ , f₂ • g₂

-- TODO: check that instance search for these things will actually work and not
-- blow up and produce horrible error messages.
record Products {i}{j} (C : Cat i j) (_⊗_ : Obj C -> Obj C -> Obj C) : Set (i ⊔ j) where
  constructor Products:
  -- maybe these should be fst/snd rather than π₁/π₂?
  field π₁ : ∀{a b} -> a ⊗ b ⇨ a
  field π₂ : ∀{a b} -> a ⊗ b ⇨ b
  infix 4 ⟨_,_⟩
  field ⟨_,_⟩ : ∀{a b c} -> a ⇨ b -> a ⇨ c -> a ⇨ b ⊗ c

  swap : ∀{a b} -> a ⊗ b ⇨ b ⊗ a
  swap = ⟨ π₂ , π₁ ⟩

  ×-map : ∀{a₁ b₁ a₂ b₂} -> a₁ ⇨ a₂ -> b₁ ⇨ b₂ -> a₁ ⊗ b₁ ⇨ a₂ ⊗ b₂
  ×-map f g = let x = isCat C in ⟨ π₁ • f , π₂ • g ⟩

  ∇ : ∀{a} -> a ⇨ a ⊗ a
  ∇ = let x = isCat C in ⟨ id , id ⟩

record Sums {i j} (C : Cat i j) (_⊕_ : Obj C -> Obj C -> Obj C) : Set (i ⊔ j) where
  constructor Sums:
  -- maybe these should be left/rite rather than in₁/in₂?
  field in₁ : ∀{A B} -> A ⇨ A ⊕ B
  field in₂ : ∀{A B} -> B ⇨ A ⊕ B
  field [_,_] : ∀{A B C} -> A ⇨ C -> B ⇨ C -> A ⊕ B ⇨ C

-- TODO: maybe I should call this "Exponentials"?
record Closed {i}{j} (C : Cat i j)
              (_⊗_ : (a b : Obj C) -> Obj C)
              (hom : (a b : Obj C) -> Obj C)
              : Set (i ⊔ j) where
  constructor Closed:
  field apply : ∀{A B} -> hom A B ⊗ A ⇨ B
  field curry : ∀{A B C} -> A ⊗ B ⇨ C -> A ⇨ hom B C

  module _ {{Prod : Products C _⊗_}} where
    private open Products Prod; instance comp = isCat C

    -- swapply : ∀{a b} -> a ⊗ hom a b ⇨ b
    -- swapply = swap • apply

    uncurry : ∀{A B C} -> A ⇨ hom B C -> A ⊗ B ⇨ C
    uncurry f = ×-map f id • apply

    flip : ∀ {A B C} -> A ⇨ hom B C -> B ⇨ hom A C
    flip f = curry (swap • uncurry f)

open Products {{...}} public
open Sums {{...}} public
open Closed {{...}} public


-- Instances for cat:Set.
instance
  products:Set : ∀{i} -> Products (cat:Set i) _×_
  products:Set = Products: proj₁ proj₂ <_,_>

  sums:Set : ∀{i} -> Sums (cat:Set i) _⊎_
  sums:Set = Sums: inj₁ inj₂ Data.Sum.[_,_]

  closed:Set : ∀{i} -> Closed (cat:Set i) _×_ (λ a b -> a -> b)
  apply {{closed:Set}} (f , x) = f x
  curry {{closed:Set}} f x y = f (x , y)


-- XXX REMOVE
-- why does this work here but not in Cat3.agda?
private
  open import Data.Product
  postulate
    ℕ : Set
    wub : ℕ × ℕ
  x : ℕ
  x = π₁ wub
