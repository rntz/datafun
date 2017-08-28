module Cat where

open import Prelude
import Data.Sum

record Cat i j : Set (suc (i ⊔ j)) where
  no-eta-equality
  constructor Cat:
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
  field ap  : Obj C -> Obj D
  field map : Hom C =[ ap ]⇒ Hom D

open Fun public
pattern fun {F} f = Fun: F f

constant : ∀{i j k l C D} -> Obj D -> Fun {i}{j}{k}{l} C D
constant {D = D} x = Fun: (λ _ -> x) (λ _ -> ident D)

 -- Constructions on relations & categories
rel× : ∀{a b c d r s} {A : Set a} {B : Set b} {C : Set c} {D : Set d}
     -> (R : A -> C -> Set r) (S : B -> D -> Set s)
     -> (A × B) -> (C × D) -> Set _
rel× R S (a , x) (b , y) = R a b × S x y

-- data rel+ {a b c d r s} {A : Set a} {B : Set b} {C : Set c} {D : Set d}
--           (R : A -> C -> Set r) (S : B -> D -> Set s)
--      : (A ⊎ B) -> (C ⊎ D) -> Set (r ⊔ s) where
data rel+ {i j k l A B} (R : Rel {i} A j) (S : Rel {k} B l) : Rel (A ⊎ B) (j ⊔ l) where
  rel₁ : ∀{a b} -> R a b -> rel+ R S (inj₁ a) (inj₁ b)
  rel₂ : ∀{a b} -> S a b -> rel+ R S (inj₂ a) (inj₂ b)

-- I would really like to make these instances but that makes Agda loooooooop.
cat× cat+ : ∀{i j k l} (C : Cat i j) (D : Cat k l) -> Cat _ _
cat× C D .Obj = Obj C × Obj D
cat× C D .Hom = rel× (Hom C) (Hom D)
cat× C D .ident = ident C , ident D
cat× C D .compo (f₁ , g₁) (f₂ , g₂) = compo C f₁ f₂ , compo D g₁ g₂

cat+ C D .Obj = Obj C ⊎ Obj D
cat+ C D .Hom = rel+ (Hom C) (Hom D)
cat+ C D .ident {inj₁ _} = rel₁ (ident C)
cat+ C D .ident {inj₂ _} = rel₂ (ident D)
cat+ C D .compo (rel₁ x) (rel₁ y) = rel₁ (compo C x y)
cat+ C D .compo (rel₂ x) (rel₂ y) = rel₂ (compo D x y)

-- "Indexed product of categories"?
-- Does this deserve to be its own typeclass, like Sums and Products?
catΠ : ∀{i j k} (A : Set i) (B : A -> Cat j k) -> Cat (j ⊔ i) (k ⊔ i)
catΠ A B .Obj     = ∀ x -> B x .Obj
catΠ A B .Hom f g = ∀ x -> B x .Hom (f x) (g x)
catΠ A B .ident x     = B x .ident
catΠ A B .compo f g x = B x .compo (f x) (g x)

 -- Cartesian structures.
 --- Sums
record Sums {i j} (C : Cat i j) : Set (i ⊔ j) where
  constructor Sums:
  private instance the-cat = C
  -- TODO: don't use an infix operator for this here.
  infixr 2 _∨_
  field _∨_ : Op (Obj C)
  field in₁ : ∀{a b} -> a ≤ a ∨ b
  field in₂ : ∀{a b} -> b ≤ a ∨ b
  field [_,_] : ∀{a b c} -> a ≤ c -> b ≤ c -> a ∨ b ≤ c
  field init : Obj C
  field init≤ : ∀{a} -> init ≤ a

  idem∨ : ∀{a} -> a ∨ a ≤ a
  idem∨ = [ id , id ]

  map∨ : ∀{a b c d} -> a ≤ c -> b ≤ d -> a ∨ b ≤ c ∨ d
  map∨ f g = [ f • in₁ , g • in₂ ]

  functor∨ : Fun (cat× C C) C
  functor∨ = fun λ { (f , g) -> map∨ f g }

  juggle∨ : ∀{a b c d} -> (a ∨ b) ∨ (c ∨ d) ≤ (a ∨ c) ∨ (b ∨ d)
  juggle∨ = [ map∨ in₁ in₁ , map∨ in₂ in₂ ]

 --- Products
record Products {i j} (C : Cat i j) : Set (i ⊔ j) where
  constructor Products:
  private instance the-cat = C
  -- TODO: don't use an infix operator for this here
  infixr 2 _∧_
  field _∧_ : Op (Obj C)
  field π₁ : ∀{a b} -> (a ∧ b) ≤ a
  field π₂ : ∀{a b} -> (a ∧ b) ≤ b
  field ⟨_,_⟩ : ∀{a b Γ} -> Γ ≤ a -> Γ ≤ b -> Γ ≤ (a ∧ b)
  -- TODO: terminal object?

  map∧ : ∀{a b c d} -> a ≤ c -> b ≤ d -> a ∧ b ≤ c ∧ d
  map∧ f g = ⟨ π₁ • f , π₂ • g ⟩

  ∇ : ∀{a} -> a ≤ a ∧ a
  ∇ = ⟨ id , id ⟩

  swap : ∀{a b} -> a ∧ b ≤ b ∧ a
  swap = ⟨ π₂ , π₁ ⟩

  -- This *could* be useful if cat× were an instance, but it's not.
  -- instance
  functor∧ : Fun (cat× C C) C
  functor∧ = fun λ { (f , g) -> map∧ f g }

  juggle∧ : ∀{a b c d} -> (a ∧ b) ∧ (c ∧ d) ≤ (a ∧ c) ∧ (b ∧ d)
  juggle∧ = ⟨ map∧ π₁ π₁ , map∧ π₂ π₂ ⟩

module _ {i j} {{C : Cat i j}} where
  module _ {{S : Sums C}} where open Sums S public
  module _ {{P : Products C}} where open Products P public

 --- CC means "cartesian closed".
record CC {i j} (C : Cat i j) : Set (i ⊔ j) where
  constructor CC:
  private instance the-cat = C
  field overlap {{products}} : Products C
  -- TODO FIXME: shouldn't bind tighter than ∧.
  infixr 4 _⇨_
  field _⇨_ : Op (Obj C)
  field apply : ∀{a b} -> (a ⇨ b) ∧ a ≤ b
  field curry : ∀{a b c} -> a ∧ b ≤ c -> a ≤ b ⇨ c

  call : ∀{a b c} -> a ≤ (b ⇨ c) -> a ≤ b -> a ≤ c
  call f a = ⟨ f , a ⟩ • apply
  swapply : ∀{a b} -> a ∧ (a ⇨ b) ≤ b
  swapply = swap • apply

  uncurry : ∀{a b c} -> a ≤ b ⇨ c -> a ∧ b ≤ c
  uncurry f = map∧ f id • apply

  flip : ∀{a b c} -> a ≤ b ⇨ c -> b ≤ a ⇨ c
  flip f = curry (swap • uncurry f)

  precompose : ∀{a b c} -> a ≤ b -> b ⇨ c ≤ a ⇨ c
  precompose f = curry (map∧ id f • apply)

  module _ {{S : Sums C}} where
    distrib-∧/∨ : ∀{a b c} -> (a ∨ b) ∧ c ≤ (a ∧ c) ∨ (b ∧ c)
    distrib-∧/∨ = map∧ [ curry in₁ , curry in₂ ] id • apply

module _ {i j} {{C : Cat i j}} {{Ccc : CC C}} where open CC Ccc public hiding (products)

 --- Possibly-infinitary products
record SetΠ k {i j} (C : Cat i j) : Set (i ⊔ j ⊔ suc k) where
  constructor SetΠ:
  private instance the-cat = C
  field Π : (A : Set k) (P : A -> Obj C) -> Obj C
  -- Do I need projection and an introduction form?
  field Πi : ∀{A P Γ} (Γ→P : (a : A) -> Γ ≤ P a) -> Γ ≤ Π A P
  field Πe : ∀{A P} (a : A) -> Π A P ≤ P a

  mapΠ : ∀{A B P Q} (F : B -> A) (G : ∀ b -> P (F b) ≤ Q b) -> Π A P ≤ Π B Q
  mapΠ F G = Πi λ b → Πe (F b) • G b

  prefixΠ : ∀{A B P} (f : B -> A) -> Π A P ≤ Π B (P ∘ f)
  prefixΠ f = Πi (Πe ∘ f) -- mapΠ f (λ _ → id)

  suffixΠ : ∀{A} {B B' : A -> Obj C} (f : ∀ a -> B a ≤ B' a) -> Π A B ≤ Π A B'
  suffixΠ f = mapΠ (λ x → x) f

  module _ {{Prod : Products C}} where
    Π/∧ : ∀{A P Q} -> Π A (λ a → P a ∧ Q a) ≤ Π A P ∧ Π A Q
    Π/∧ = ⟨ suffixΠ (λ _ → π₁) , suffixΠ (λ _ → π₂) ⟩

    -- Currently unused:
    -- ∧/Π : ∀{A P Q} -> Π A P ∧ Π A Q ≤ Π A (λ a -> P a ∧ Q a)
    -- ∧/Π = Πi λ a → map∧ (Πe a) (Πe a)

    -- fwiddle : ∀{A B P Q} -> Π A P ∧ Π B Q ≤ Π (A ⊎ B) Data.Sum.[ P , Q ]
    -- fwiddle = Πi Data.Sum.[ (λ x → π₁ • Πe x) , (λ x → π₂ • Πe x) ]

module _ {i j k} {{C : Cat i j}} {{Pi : SetΠ k C}} where open SetΠ Pi public

 -- Some useful categories & their structures.
⊤-cat ⊥-cat : ∀{i j} -> Cat i j
⊥-cat = Cat: (Lift ⊥) (λ { (lift ()) }) (λ { {lift ()} }) (λ { {lift ()} })
⊤-cat = Cat: (Lift ⊤) (λ _ _ -> Lift ⊤) (lift tt) (λ _ _ → lift tt)

instance
  sets : ∀{i} -> Cat (suc i) i
  Obj (sets {i}) = Set i
  Hom sets a b = a -> b
  ident sets x = x
  compo sets f g x = g (f x)

  set-products : ∀{i} -> Products (sets {i})
  set-products = Products: _×_ proj₁ proj₂ <_,_>
    where open import Data.Product

  set-sums : ∀{i} -> Sums (sets {i})
  set-sums = Sums: _⊎_ inj₁ inj₂ Data.Sum.[_,_] (Lift ⊥) (λ { (lift ()) })

  set-cc : ∀{i} -> CC (sets {i})
  set-cc = CC: Function (λ { (f , a) -> f a }) (λ f x y -> f (x , y))

  set-Π : ∀{i} -> SetΠ i (sets {i})
  set-Π = SetΠ: (λ A P → (x : A) -> P x) (λ Γ→P γ a → Γ→P a γ) (λ a ∀P → ∀P a)

  cats : ∀{i j} -> Cat (suc (i ⊔ j)) (i ⊔ j)
  Obj (cats {i}{j}) = Cat i j
  Hom cats = Fun
  ident cats = fun id
  compo cats (fun f) (fun g) = fun (f • g)

  cat-products : ∀{i j} -> Products (cats {i}{j})
  cat-products {i}{j} = Products: cat× (fun π₁) (fun π₂)
                        λ where (fun f) (fun g) → fun ⟨ f , g ⟩

  cat-sums : ∀{i j} -> Sums (cats {i}{j})
  cat-sums {i}{j} = Sums: cat+ (fun rel₁) (fun rel₂) disj ⊥-cat (Fun: init≤ λ { {lift ()} })
    where disj : ∀ {a b c : Cat i j} -> a ≤ c -> b ≤ c -> cat+ a b ≤ c
          disj F G = Fun: [ ap F , ap G ] (λ { (rel₁ x) → map F x ; (rel₂ x) → map G x })

  cat-Π : ∀{i j k} -> SetΠ k (cats {i ⊔ k} {j ⊔ k})
  cat-Π = SetΠ: catΠ (λ Γ→P → fun (λ γ a → Γ→P a .map γ)) (λ a → fun (λ ∀P≤ → ∀P≤ a))

 -- Preserving cartesian structure over operations on categories.
module _ {i j k l C D} (P : Sums {i}{j} C) (Q : Sums {k}{l} D) where
  private instance cc = C; cs = P; dd = D; ds = Q
  cat×-sums : Sums (cat× C D)
  _∨_ {{cat×-sums}} (a , x) (b , y) = (a ∨ b) , (x ∨ y)
  in₁ {{cat×-sums}} = in₁ , in₁
  in₂ {{cat×-sums}} = in₂ , in₂
  [_,_] {{cat×-sums}} (f₁ , f₂) (g₁ , g₂) = [ f₁ , g₁ ] , [ f₂ , g₂ ]
  init {{cat×-sums}} = init , init
  init≤ {{cat×-sums}} = init≤ , init≤

-- -- This is correct, but not yet useful.
-- module _ {i j k} (A : Set i) {B} (P : ∀ a -> Sums {j}{k} (B a)) where
--   catΠ-sums : Sums (catΠ A B)
--   Sums._∨_ catΠ-sums f g x = P x .Sums._∨_ (f x) (g x)
--   Sums.in₁ catΠ-sums x = P x .Sums.in₁
--   Sums.in₂ catΠ-sums x = P x .Sums.in₂
--   Sums.[_,_] catΠ-sums f g x = P x .Sums.[_,_] (f x) (g x)
--   Sums.init catΠ-sums x = P x .Sums.init
--   Sums.init≤ catΠ-sums x = P x .Sums.init≤
