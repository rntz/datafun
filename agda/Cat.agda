module Cat where

open import Prelude

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
  field map : ∀{a b} -> Hom C a b -> Hom D (ap a) (ap b)

open Fun public
pattern fun {F} f = Fun: F f

auto-map : ∀{i j k l} {{C D}} {{F : Fun {i}{j}{k}{l} C D}} {a b}
           -> Hom C a b -> Hom D (ap F a) (ap F b)
auto-map {{F = F}} = map F


-- Constructions on relations & categories
data rel+ {i j k l A B} (R : Rel {i} A j) (S : Rel {k} B l) : Rel (A ⊎ B) (j ⊔ l) where
  rel₁ : ∀{a b} -> R a b -> rel+ R S (inj₁ a) (inj₁ b)
  rel₂ : ∀{a b} -> S a b -> rel+ R S (inj₂ a) (inj₂ b)

-- I would really like to make these instances but that makes Agda loooooooop.
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
  field overlap {{C}} : Cat i j
  infixr 2 _∧_
  field _∧_ : Op (Obj C)
  field π₁ : ∀{a b} -> (a ∧ b) ≤ a
  field π₂ : ∀{a b} -> (a ∧ b) ≤ b
  field ⟨_,_⟩ : ∀{a b x} -> x ≤ a -> x ≤ b -> x ≤ (a ∧ b)

  ∧-map : ∀{a b c d} -> a ≤ c -> b ≤ d -> a ∧ b ≤ c ∧ d
  ∧-map f g = ⟨ π₁ • f , π₂ • g ⟩

  ∇ : ∀{a} -> a ≤ a ∧ a
  ∇ = ⟨ id , id ⟩

  swap : ∀{a b} -> a ∧ b ≤ b ∧ a
  swap = ⟨ π₂ , π₁ ⟩

  -- This *could* be useful if cat× were an instance, but it's not.
  -- instance
  ∧-functor : Fun (cat× C C) C
  ∧-functor = fun λ { (f , g) -> ∧-map f g }

record Sums i j : Set (suc (i ⊔ j)) where
  constructor Sums:
  field overlap {{C}} : Cat i j
  infixr 2 _∨_
  field _∨_ : Op (Obj C)
  field in₁ : ∀{a b} -> a ≤ a ∨ b
  field in₂ : ∀{a b} -> b ≤ a ∨ b
  field [_,_] : ∀{a b c} -> a ≤ c -> b ≤ c -> a ∨ b ≤ c

  ∨-map : ∀{a b c d} -> a ≤ c -> b ≤ d -> a ∨ b ≤ c ∨ d
  ∨-map f g = [ f • in₁ , g • in₂ ]

-- CCC means "cartesian closed category".
record CCC i j : Set (suc (i ⊔ j)) where
  constructor CCC:
  field overlap {{products}} : Products i j
  open Products products
  infixr 4 _⇨_
  field _⇨_ : Op (Obj C)
  field apply : ∀{a b} -> (a ⇨ b) ∧ a ≤ b
  field curry : ∀{a b c} -> a ∧ b ≤ c -> a ≤ b ⇨ c

  uncurry : ∀{a b c} -> a ≤ b ⇨ c -> a ∧ b ≤ c
  uncurry f = ∧-map f id • apply

  flip : ∀{a b c} -> a ≤ b ⇨ c -> b ≤ a ⇨ c
  flip f = curry (swap • uncurry f)

open Products {{...}} public using (_∧_; π₁; π₂; ⟨_,_⟩; ∧-map; ∇; swap)
open Sums {{...}} public using (_∨_; in₁; in₂; [_,_]; ∨-map)
open CCC {{...}} public using (_⇨_; apply; curry; uncurry; flip)


-- Some convenient conversions
instance
  cast-cat->set : ∀{i j k} -> Cast k (Cat i j) (Set i)
  cast-cat->set = Cast: Obj

  cast-products->cat : ∀{i j k} -> Cast k (Products i j) (Cat i j)
  cast-products->cat = Cast: Products.C

  cast-ccc->products : ∀{i j k} -> Cast k (CCC i j) (Products i j)
  cast-ccc->products = Cast: CCC.products


-- Some useful categories
instance
  sets : ∀{i} -> Cat (suc i) i
  Obj (sets {i}) = Set i
  Hom sets a b = a -> b
  ident sets x = x
  compo sets f g x = g (f x)

  set-products : ∀{i} -> Products (suc i) i
  set-products = Products: _×_ proj₁ proj₂ <_,_>
    where open import Data.Product

  set-sums : ∀{i} -> Sums (suc i) i
  set-sums = Sums: _⊎_ inj₁ inj₂ Data.Sum.[_,_]
    where open import Data.Sum

  set-cc : ∀{i} -> CCC (suc i) i
  set-cc = CCC: Function (λ { (f , a) -> f a }) (λ f x y -> f (x , y))

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
            F G .map (rel₁ x) -> map F x
            F G .map (rel₂ x) -> map G x
