module Cartesian where

open import Level
open import Data.Product hiding (curry; uncurry; swap)
open import Data.Sum hiding ([_,_])

open import Cat

cat× : ∀{i j} (A B : Cat i j) -> Cat i j
cat× A B .Obj = Obj A × Obj B
cat× A B .Arr (a₁ , b₁) (a₂ , b₂) = Arr A a₁ a₂ × Arr B b₁ b₂
cat× (cat A) (cat B) .isCat .ident = ident A , ident B
cat× (cat A) (cat B) .isCat .compo (f₁ , f₂) (g₁ , g₂) = compo A f₁ g₁ , compo B f₂ g₂

-- FIXME
-- record Prod {i j} (C : Cat i j) (_⊗_ : Obj C -> Obj C -> Obj C) : Set (i ⊔ j) where
--   constructor Prod:
--   private instance cc = C
--   field π₁ : ∀{a b} -> a ⊗ b ≤ a
--   field π₂ : ∀{a b} -> a ⊗ b ≤ b
--   infix 4 ⟨_,_⟩
--   field ⟨_,_⟩ : ∀{a b c} -> a ≤ b -> a ≤ c -> a ≤ b ⊗ c

record Products {i j} Obj Arr (_⊗_ : Obj -> Obj -> Obj)
       {{C : Compose {i}{j} Obj Arr}} : Set (i ⊔ j) where
  constructor Products:
  private instance cc = cat C
  field π₁ : ∀{a b} -> a ⊗ b ≤ a
  field π₂ : ∀{a b} -> a ⊗ b ≤ b
  infix 4 ⟨_,_⟩
  field ⟨_,_⟩ : ∀{a b c} -> a ≤ b -> a ≤ c -> a ≤ b ⊗ c

  swap : ∀{a b} -> a ⊗ b ≤ b ⊗ a
  swap = ⟨ π₂ , π₁ ⟩

  ×-map : ∀{a₁ b₁ a₂ b₂} -> a₁ ≤ a₂ -> b₁ ≤ b₂ -> a₁ ⊗ b₁ ≤ a₂ ⊗ b₂
  ×-map f g = ⟨ π₁ • f , π₂ • g ⟩

  ∇ : ∀{a} -> a ≤ a ⊗ a
  ∇ = ⟨ id , id ⟩

record Sums {i j} Obj Arr (_⊕_ : Obj -> Obj -> Obj)
       {{C : Compose {i}{j} Obj Arr}} : Set (i ⊔ j) where
  constructor Sums:
  -- maybe these should be left/rite rather than in₁/in₂?
  private instance cc = cat C
  field in₁ : ∀{A B} -> A ≤ A ⊕ B
  field in₂ : ∀{A B} -> B ≤ A ⊕ B
  field [_,_] : ∀{A B C} -> A ≤ C -> B ≤ C -> A ⊕ B ≤ C

record Closed {i j} Obj Arr (_⊗_ arr : Obj -> Obj -> Obj)
              {{C : Compose {i}{j} Obj Arr}} : Set (i ⊔ j) where
  constructor Closed:
  private instance cc = cat C
  field apply : ∀{A B} -> arr A B ⊗ A ≤ B
  field curry : ∀{A B C} -> A ⊗ B ≤ C -> A ≤ arr B C

  module _ {{Prod : Products Obj Arr _⊗_}} where
    open Products Prod

    -- swapply : ∀{a b} -> a ⊗ arr a b ≤ b
    -- swapply = swap • apply

    uncurry : ∀{A B C} -> A ≤ arr B C -> A ⊗ B ≤ C
    uncurry f = ×-map f id • apply

    flip : ∀ {A B C} -> A ≤ arr B C -> B ≤ arr A C
    flip f = curry (swap • uncurry f)


-- does making these instances work at all?!
open Products {{...}} public
open Sums {{...}} public
open Closed {{...}} public

Products~ Sums~ : ∀{i j} (C : Cat i j) _⊗_ -> Set _
Closed~ : ∀{i j} (C : Cat i j) _⊗_ arr -> Set _
Products~ C _⊗_ = Products (Obj C) (Arr C) _⊗_ {{isCat C}}
Sums~ C _⊕_ = Sums (Obj C) (Arr C) _⊕_ {{isCat C}}
Closed~ C _⊗_ arr = Closed (Obj C) (Arr C) _⊗_ arr {{isCat C}}

module _ {i j A R _⊗_ arr} {{C : Compose {i}{j} A R}}
         {{P : Products A R _⊗_}} {{Cl : Closed A R _⊗_ arr}} where
  private instance cc = cat C
  swapply : ∀{a b} -> (a ⊗ arr a b) ≤ b
  swapply = swap • apply {{_}} {{Cl}}


-- Instances for cat:Set (and cat:Cat?)
instance
  products:Set : ∀{i} -> Products~ (cat:set i) _×_
  products:Set = Products: proj₁ proj₂ <_,_>

  sums:Set : ∀{i} -> Sums~ (cat:set i) _⊎_
  sums:Set = Sums: inj₁ inj₂ Data.Sum.[_,_]

  closed:Set : ∀{i} -> Closed~ (cat:set i) _×_ (λ a b -> a -> b)
  apply {{closed:Set}} (f , x) = f x
  curry {{closed:Set}} f x y = f (x , y)

  products:Cat : ∀{i j} -> Products~ (cat:cat i j) cat×
  π₁ {{products:Cat}} = homo proj₁
  π₂ {{products:Cat}} = homo proj₂
  ⟨_,_⟩ {{products:Cat}} (homo f) (homo g) = homo ⟨ f , g ⟩


-- a test FIXME: remove
private
  postulate
    ℕ : Set
  foo : ℕ × ℕ -> ℕ
  -- arghghhhgh.
  foo x = π₁ {Arr = Func} x
  -- but this works?
  -- foo = π₁

  postulate
    C : Cat zero zero
  bar : cat× C C ≤ C
  bar = π₂
