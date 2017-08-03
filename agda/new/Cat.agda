module Cat where

open import Level
open import Relation.Binary using (Rel)
open import Data.Product using (Σ; Σ-syntax; _,_; proj₁; proj₂; _×_; <_,_>; ,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)

Op : ∀{i} -> Set i -> Set i
Op A = A -> A -> A

Function : ∀{i j} -> Set i -> Set j -> Set _
Function A B = A -> B

record Cat i j : Set (suc (i ⊔ j)) where
  infix  1 Hom
  infixr 9 compo
  field Obj : Set i
  field Hom : Rel Obj j
  field ident : ∀{a} -> Hom a a
  field compo : ∀{a b c} -> Hom a b -> Hom b c -> Hom a c

open Cat public
open Cat {{...}} public using () renaming (Hom to _≤_; ident to id; compo to _•_)

-- Functors
record Fun {i j k l} (C : Cat i j) (D : Cat k l) : Set (i ⊔ j ⊔ k ⊔ l) where
  constructor Fun:
  field ap : Obj C -> Obj D
  field cov : ∀{a b} -> Hom C a b -> Hom D (ap a) (ap b)

open Fun public
pattern fun {F} f = Fun: F f


-- Constructions on relations & categories
data rel+ {i j k l A B} (R : Rel {i} A j) (S : Rel {k} B l) : Rel (A ⊎ B) (j ⊔ l) where
  rel₁ : ∀{a b} -> R a b -> rel+ R S (inj₁ a) (inj₁ b)
  rel₂ : ∀{a b} -> S a b -> rel+ R S (inj₂ a) (inj₂ b)

cat× cat+ : ∀{i j k l} (C : Cat i j) (D : Cat k l) -> Cat _ _
cat× C D .Obj = Obj C × Obj D
cat× C D .Hom (a , x) (b , y) = Hom C a b × Hom D x y
cat× C D .ident = ident C , ident D
cat× C D .compo (f₁ , g₁) (f₂ , g₂) = compo C f₁ f₂ , compo D g₁ g₂

cat+ C D .Obj = Obj C ⊎ Obj D
cat+ C D .Hom = rel+ (Hom C) (Hom D)
cat+ C D .ident {inj₁ _} = rel₁ (ident C)
cat+ C D .ident {inj₂ _} = rel₂ (ident D)
cat+ C D .compo (rel₁ x) (rel₁ y) = rel₁ (compo C x y)
cat+ C D .compo (rel₂ x) (rel₂ y) = rel₂ (compo D x y)

-- "Indexed product of categories"?
catΠ : ∀{i j k} (A : Set i) (B : A -> Cat j k) -> Cat _ _
catΠ A B .Obj     = ∀ x -> B x .Obj
catΠ A B .Hom f g = ∀ x -> B x .Hom (f x) (g x)
catΠ A B .ident x     = B x .ident
catΠ A B .compo f g x = B x .compo (f x) (g x)


-- Cartesian structure.
record Products i j : Set (suc (i ⊔ j)) where
  constructor Products:
  field overlap {{cat}} : Cat i j
  infixr 2 _∧_
  field _∧_ : Op (Obj cat)
  field π₁ : ∀{a b} -> (a ∧ b) ≤ a
  field π₂ : ∀{a b} -> (a ∧ b) ≤ b
  field ⟨_,_⟩ : ∀{a b x} -> x ≤ a -> x ≤ b -> x ≤ (a ∧ b)

  ∇ : ∀{a} -> a ≤ a ∧ a
  ∇ = ⟨ id , id ⟩

  swap : ∀{a b} -> a ∧ b ≤ b ∧ a
  swap = ⟨ π₂ , π₁ ⟩

  ∧-map : ∀{a b c d} -> a ≤ c -> b ≤ d -> a ∧ b ≤ c ∧ d
  ∧-map f g = ⟨ π₁ • f , π₂ • g ⟩

record Sums i j : Set (suc (i ⊔ j)) where
  constructor Sums:
  field overlap {{cat}} : Cat i j
  infixr 3 _∨_
  field _∨_ : Op (Obj cat)
  field in₁ : ∀{a b} -> a ≤ a ∨ b
  field in₂ : ∀{a b} -> b ≤ a ∨ b
  field [_,_] : ∀{a b c} -> a ≤ c -> b ≤ c -> a ∨ b ≤ c

-- CCC means "cartesian closed category".
record CCC i j : Set (suc (i ⊔ j)) where
  constructor CCC:
  field overlap {{products}} : Products i j
  open Products products
  infixr 4 _⇨_
  field _⇨_ : Op (Obj cat)
  field apply : ∀{a b} -> (a ⇨ b) ∧ a ≤ b
  field curry : ∀{a b c} -> a ∧ b ≤ c -> a ≤ b ⇨ c

  uncurry : ∀{a b c} -> a ≤ b ⇨ c -> a ∧ b ≤ c
  uncurry f = ∧-map f id • apply

  flip : ∀{a b c} -> a ≤ b ⇨ c -> b ≤ a ⇨ c
  flip f = curry (swap • uncurry f)

open Products {{...}} public hiding (cat)
open Sums {{...}} public hiding (cat)
open CCC {{...}} public hiding (products)


-- Some useful categories
instance
  sets : ∀{i} -> Cat (suc i) i
  Obj (sets {i}) = Set i
  Hom sets a b = a -> b
  ident sets x = x
  compo sets f g x = g (f x)

  set-products : ∀{i} -> Products (suc i) i
  set-products = Products: _×_ proj₁ proj₂ <_,_>

  set-sums : ∀{i} -> Sums (suc i) i
  set-sums = Sums: _⊎_ inj₁ inj₂ Data.Sum.[_,_]

  set-exponentials : ∀{i} -> CCC (suc i) i
  set-exponentials = CCC: Function (λ { (f , a) -> f a }) (λ f x y -> f (x , y))

  cats : ∀{i j} -> Cat (suc (i ⊔ j)) (i ⊔ j)
  Obj (cats {i}{j}) = Cat i j
  Hom cats = Fun
  ident cats = fun id
  compo cats (fun f) (fun g) = fun (f • g)

  cat-products : ∀{i j} -> Products (suc (i ⊔ j)) (i ⊔ j)
  cat-products {i}{j} = Products: {{cats {i}{j}}} cat× (fun π₁) (fun π₂)
                        λ where (fun f) (fun g) → fun ⟨ f , g ⟩

  cat-sums : ∀{i j} -> Sums (suc (i ⊔ j)) (i ⊔ j)
  cat-sums {i}{j} = Sums: {{cats {i}{j}}} cat+ (fun rel₁) (fun rel₂)
    λ where F G .ap -> [ ap F , ap G ]
            F G .cov (rel₁ x) -> cov F x
            F G .cov (rel₂ x) -> cov G x
