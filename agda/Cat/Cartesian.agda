---------- Cartesian products & sums ----------
open import Prelude
open import Cat.Base
open import Cat.Tones using (op)

module Cat.Cartesian where

---------- Products ----------
module _ {i j} (C : Cat i j) where
  private instance the-cat = C

  infix 0 _/_/_/_
  record ProductOf (a b : Obj C) : Set (i ⊔ j) where
    constructor _/_/_/_
    -- TODO: ∧/∨ should have distinct precedences.
    infixr 2 a∧b
    field a∧b : Obj C
    field ∧E₁ : a∧b ≤ a
    field ∧E₂ : a∧b ≤ b
    field ∧I : ∀{Γ} → Γ ≤ a → Γ ≤ b → Γ ≤ a∧b

  open ProductOf public

  record Products : Set (i ⊔ j) where
    constructor Products:
    field top : Σ[ ⊤ ∈ _ ] ∀{a} → a ≤ ⊤
    field glb : ∀ a b → ProductOf a b

    open Σ top public using () renaming (proj₁ to ⊤; proj₂ to ≤⊤)
    module _ (a b : Obj C) where open ProductOf (glb a b) public using () renaming (a∧b to _∧_)
    module _ {a b : Obj C} where open ProductOf (glb a b) public using () renaming (∧I to ⟨_,_⟩; ∧E₁ to π₁; ∧E₂ to π₂)

    ∇ : ∀{a} -> a ≤ a ∧ a
    ∇ = ⟨ id , id ⟩

    a∧⊤≈a : ∀{a} → a ∧ ⊤ ≈ a
    a∧⊤≈a = π₁ , ⟨ id , ≤⊤ ⟩

    swap : ∀{a b} -> a ∧ b ≤ b ∧ a
    swap = ⟨ π₂ , π₁ ⟩

    -- Maybe factor out associativity into a separate structure?
    assoc∧r : ∀{a b c} -> (a ∧ b) ∧ c ≤ a ∧ (b ∧ c)
    assoc∧r = ⟨ π₁ ∙ π₁ , ⟨ (π₁ ∙ π₂) , π₂ ⟩ ⟩

    map∧ : ∀{a b c d} -> a ≤ c -> b ≤ d -> a ∧ b ≤ c ∧ d
    map∧ f g = ⟨ π₁ ∙ f , π₂ ∙ g ⟩

    map∧₂ : ∀{a b₁ b₂} → b₁ ≤ b₂ → a ∧ b₁ ≤ a ∧ b₂
    map∧₂ = map∧ id

    functor∧ : Fun (cat× C C) C
    functor∧ = fun λ { (f , g) -> map∧ f g }

    juggle∧ : ∀{a b c d} -> (a ∧ b) ∧ (c ∧ d) ≤ (a ∧ c) ∧ (b ∧ d)
    juggle∧ = ⟨ map∧ π₁ π₁ , map∧ π₂ π₂ ⟩

 ---------- Sums ----------
-- Sums are the dual of products, ie. products in the opposite category.
Sums : ∀{i j} (C : Cat i j) → Set (i ⊔ j)
Sums C = Products (op C)

module Sums {i j C} (S : Sums {i}{j} C) where
  open Products S public using () renaming
    ( top to bottom; glb to lub
    ; ⊤ to ⊥; ≤⊤ to ⊥≤
    ; _∧_ to _∨_; ⟨_,_⟩ to [_,_]; π₁ to in₁; π₂ to in₂
    ; ∇ to idem∨ ; a∧⊤≈a to a∨⊥≈a ; swap to comm∨ ; assoc∧r to assoc∨r
    ; map∧ to map∨ ; map∧₂ to map∨₂
    ; juggle∧ to juggle∨ )

  functor∨ : Fun (cat× C C) C
  functor∨ = fun (Products.functor∧ S .map)


---------- Namespacing etc. ----------
open Products public using (top; glb)
open Sums public using (bottom; lub)

module _ {i j} {{C : Cat i j}} where
  module _ {{P : Products C}} where open Products P public
  module _ {{S : Sums C}} where open Sums S public
