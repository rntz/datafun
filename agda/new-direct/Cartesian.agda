module Cartesian where

open import Level
open import Data.Product using (_×_; _,_; proj₁; proj₂; <_,_>)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary using (Rel)

open import Cat


---------- Constructions on "relations" & categories ----------
rel× : ∀{i j k l A B} (R : Rel {i} A j) (S : Rel {k} B l) -> Rel (A × B) _
rel× R S (a , x) (b , y) = R a b × S x y

data rel+ {i j k l A B} (R : Rel {i} A j) (S : Rel {k} B l) : Rel (A ⊎ B) (j ⊔ l) where
  rel₁ : ∀{a b} -> R a b -> rel+ R S (inj₁ a) (inj₁ b)
  rel₂ : ∀{a b} -> S a b -> rel+ R S (inj₂ a) (inj₂ b)

cat× cat+ : ∀{i j k l} -> Cat i j -> Cat k l -> Cat _ _
Obj (cat× C D) = Obj C × Obj D
Arr (cat× C D) = rel× (Arr C) (Arr D)
ident (cat× C D) = ident C , ident D
compo (cat× C D) (f1 , g1) (f2 , g2) = compo C f1 f2 , compo D g1 g2

Obj (cat+ C D) = Obj C ⊎ Obj D
Arr (cat+ C D) = rel+ (Arr C) (Arr D)
ident (cat+ C D) {inj₁ _} = rel₁ (ident C)
ident (cat+ C D) {inj₂ _} = rel₂ (ident D)
compo (cat+ C D) (rel₁ x) (rel₁ y) = rel₁ (compo C x y)
compo (cat+ C D) (rel₂ x) (rel₂ y) = rel₂ (compo D x y)


---------- Properties of / structures on categories ----------
record Products {i j} (C : Cat i j) : Set (i ⊔ j) where
  constructor Products:
  private instance cc = C
  infixr 2 _∧_
  field _∧_ : (a b : Obj C) -> Obj C
  field π₁ : ∀{a b} -> a ∧ b ≤ a
  field π₂ : ∀{a b} -> a ∧ b ≤ b
  field ⟨_,_⟩ : ∀{a b c} -> a ≤ b -> a ≤ c -> a ≤ b ∧ c

  swap : ∀{a b} -> a ∧ b ≤ b ∧ a; swap = ⟨ π₂ , π₁ ⟩
  ∇ : ∀{a} -> a ≤ a ∧ a; ∇ = ⟨ id , id ⟩

  ×-map : ∀{a₁ b₁ a₂ b₂} -> a₁ ≤ a₂ -> b₁ ≤ b₂ -> a₁ ∧ b₁ ≤ a₂ ∧ b₂
  ×-map f g = ⟨ π₁ • f , π₂ • g ⟩

  -- instance
  --   -- this makes (map (f , g) a == ×-map f g a), in theory.
  --   -- in practice instance resolution doesn't seem to notice it :(
  --   ×-homo : Homo (cat× C C) C
  --   ×-homo = homo (λ { (f , g) → ×-map f g })

  -- ×-map₁ : ∀{a₁ a₂ b} -> a₁ ≤ a₂ -> a₁ ∧ b ≤ a₂ ∧ b
  -- ×-map₂ : ∀{b₁ b₂ a} -> b₁ ≤ b₂ -> a ∧ b₁ ≤ a ∧ b₂
  -- ×-map₁ f = ×-map f id; ×-map₂ f = ×-map id f

record Sums {i j} (C : Cat i j) : Set (i ⊔ j) where
  constructor Sums:
  private instance cc = C
  infixr 3 _∨_
  field _∨_ : (a b : Obj C) -> Obj C
  field in₁ : ∀{a b} -> a ≤ a ∨ b
  field in₂ : ∀{a b} -> b ≤ a ∨ b
  -- TODO: since we can no longer get this to work automatically when used with
  -- sets and functions, should we rename [_,_]?
  field [_,_] : ∀{a b c} -> a ≤ c -> b ≤ c -> a ∨ b ≤ c

record Exponentials {i j} (C : Cat i j) {{Prod : Products C}} : Set (i ⊔ j) where
  constructor Exponentials:
  private instance cc = C; open Products Prod
  infixr 4 _⇨_
  field _⇨_ : (a b : Obj C) -> Obj C
  -- TODO: we should probably rename `curry`.
  field apply : ∀{a b} -> (a ⇨ b) ∧ a ≤ b
  field curry : ∀{a b c} -> a ∧ b ≤ c -> a ≤ b ⇨ c

-- Bring the fields of Products, Sums, Exponentials into scope with appropriate
-- arguments solved by instance resolution.
module _ {i j} {{C : Cat i j}} where
  module _ {{Prod : Products C}} where
    open Products Prod public
    module _ {{Exp : Exponentials C}} where open Exponentials Exp public
  module _ {{Sum : Sums C}} where open Sums Sum public


-- FIXME: These seem to be taking a while to compile. :(
module _ {i j} {{C : Cat i j}} {{Prod : Products C}} {{Exp : Exponentials C}} where
  uncurry : ∀{a b c : Obj C} -> a ≤ b ⇨ c -> a ∧ b ≤ c
  uncurry f = ×-map f id • apply
  -- uncurry f = cov ×-homo (f , id) • apply

  flip : ∀{a b c} -> a ≤ b ⇨ c -> b ≤ a ⇨ c
  flip f = curry (swap • uncurry f)


-- Just a convenience for defining products, sums, and exponentials together.
record BiCC {i j} (C : Cat i j) : Set (i ⊔ j) where
  field instance pros : Products C
  field instance sums : Sums C
  field instance exps : Exponentials C {{pros}}

-- Sets is bicartesian closed. Cat is, too, but since our Cats are lawless we're
-- ignoring naturality, so we only define products and sums.
instance
  -- I'm not sure this is working!
  bicc:set : ∀{i} -> BiCC (cat:set {i})
  BiCC.pros bicc:set = Products: _×_ proj₁ proj₂ <_,_>
  BiCC.sums bicc:set = Sums: _⊎_ inj₁ inj₂ Data.Sum.[_,_]
  _⇨_ {{BiCC.exps bicc:set}} = Function
  apply {{BiCC.exps bicc:set}} (f , a) = f a
  curry {{BiCC.exps bicc:set}} f a b = f (a , b)

  products:cat : ∀{i j} -> Products (cat:cat {i} {j})
  products:cat = Products: cat× (homo π₁) (homo π₂)
                           (λ where (homo f) (homo g) → homo ⟨ f , g ⟩)

  sums:cat : ∀{i j} -> Sums (cat:cat {i} {j})
  sums:cat = Sums: cat+ (homo rel₁) (homo rel₂) λ where
    F G .app → [ app F , app G ]
    F G .cov (rel₁ x) → cov F x
    F G .cov (rel₂ x) → cov G x
