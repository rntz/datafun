open import Prelude

module Cat.Base where

record Cat i j : Set (suc (i ⊔ j)) where
  -- PROS of eta-equality: no more annoying eta-expansion or coercion because
  -- some equalities no longer hold definitionally.
  --
  -- MOREOVER, with eta-equality on, we can omit a lot of instance definitions
  -- (eg. monad→comonad conversion) because they're true definitionally. The
  -- flip side is that we _must_ omit them, because they cause instance search
  -- to infinite loop.
  --
  -- PROS of no-eta-equality: inferred types of holes are actually readable
  -- instead of seeing eta-expanded categories all over the place. This is a
  -- HUGE annoyance.
  no-eta-equality
  constructor Cat:
  infix  1 Hom
  infixr 9 compo
  field Obj : Set i
  field Hom : Rel Obj j
  field ident : ∀{a} -> Hom a a
  field compo : ∀{a b c} (f : Hom a b) (g : Hom b c) -> Hom a c

open Cat public
open Cat {{...}} public using () renaming (Hom to _≤_; ident to id; compo to _∙_)

-- Functors
record Fun {i j k l} (C : Cat i j) (D : Cat k l) : Set (i ⊔ j ⊔ k ⊔ l) where
  constructor Fun:
  field ap  : Obj C -> Obj D
  field map : Hom C =[ ap ]⇒ Hom D

open Fun public
pattern fun {F} f = Fun: F f

-- TODO: remove if unused.
-- -- Composition of functors across different levels.
-- _⊚_ : ∀{i j k l m n A B C} → Fun {k}{l}{m}{n} B C → Fun {i}{j} A B → Fun A C
-- ap (F ⊚ G) = ap F ∘ ap G
-- map (F ⊚ G) = map F ∘ map G


-- Conveniences.
pattern TT = lift tt

sets : ∀ i -> Cat (suc i) i
sets i .Obj = Set i
sets i .Hom a b = a -> b
sets i .ident x = x
sets i .compo f g x = g (f x)

instance auto:sets = λ{i} → sets i

cats : ∀ i j -> Cat (suc (i ⊔ j)) (i ⊔ j)
cats i j = Cat: (Cat i j) Fun (fun id) λ { (fun f) (fun g) → fun (f ∙ g) }

instance auto:cats = λ{i}{j} → cats i j

⊤-cat ⊥-cat : ∀{i j} -> Cat i j
⊥-cat = Cat: (Lift ∅) (λ{()}) (λ { {()} }) λ { {()} }
⊤-cat = Cat: (Lift Unit) (λ _ _ -> Lift Unit) TT const

Proset : Set1
Proset = Cat zero zero

prosets : Cat _ _
prosets = cats zero zero

infix 1 _⇒_
_⇒_ : Rel Proset _
_⇒_ = Fun

constant : ∀{i j k l C D} -> Obj D -> Fun {i}{j}{k}{l} C D
constant {D = D} x = Fun: (const x) (λ _ → ident D)

-- This isn't really an isomorphism, it's just a pair of arrows in both
-- directions. But since we're lawless, we can't tell the difference.
infix 1 _≈_
_≈_ : ∀{i j} {{C : Cat i j}} (a b : Obj C) -> Set j
_≈_ {{C}} a b = Hom C a b × Hom C b a


-- Constructions on relations & categories
rel× : ∀{a b c d r s} {A : Set a} {B : Set b} {C : Set c} {D : Set d}
     -> (R : A -> C -> Set r) (S : B -> D -> Set s)
     -> (A × B) -> (C × D) -> Set _
rel× R S (a , x) (b , y) = R a b × S x y

data rel+ {i j k l A B} (R : Rel {i} A j) (S : Rel {k} B l) : Rel (A ⊎ B) (j ⊔ l) where
  rel₁ : ∀{a b} -> R a b -> rel+ R S (inj₁ a) (inj₁ b)
  rel₂ : ∀{a b} -> S a b -> rel+ R S (inj₂ a) (inj₂ b)

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

-- Functor category, sans the naturality condition.
cat→ : ∀{i j k l} (A : Cat i j) (B : Cat k l) -> Cat (i ⊔ j ⊔ k ⊔ l) _
cat→ A B .Obj = Fun A B
cat→ A B .Hom F G = ∀{x} -> Hom B (ap F x) (ap G x)
cat→ A B .ident = ident B
cat→ A B .compo F≤G G≤H = compo B F≤G G≤H

-- Indexed product of categories.
catΠ : ∀{i j k} (A : Set i) (B : A -> Cat j k) -> Cat (j ⊔ i) (k ⊔ i)
catΠ A B .Obj     = ∀ x -> B x .Obj
catΠ A B .Hom f g = ∀ x -> B x .Hom (f x) (g x)
catΠ A B .ident x     = B x .ident
catΠ A B .compo f g x = B x .compo (f x) (g x)

-- Weak connectedness.
module _  {i j} (C : Cat i j) where
  data Connected : (a b : Obj C) -> Set (i ⊔ j) where
    path-by : ∀{a b} -> Hom C a b -> Connected a b
    path⁻¹ : ∀{a b} -> Connected a b -> Connected b a
    path∙ : ∀{a b c} -> Connected a b -> Connected b c -> Connected a c

module _ {i j k} {C : Cat i j}
         (F : (a b : Obj C) -> Set k)
         (hom→F : ∀{a b} -> Hom C a b -> F a b)
         (F-symm : Symmetric F)
         (F-trans : Transitive F) where
  path-fold : ∀{a b} -> Connected C a b -> F a b
  path-fold (path-by x) = hom→F x
  path-fold (path⁻¹ p) = F-symm (path-fold p)
  path-fold (path∙ p q) = F-trans (path-fold p) (path-fold q)

-- Discrete category on a given set.
discrete : ∀{i} → Set i → Cat _ _
discrete A .Obj = A
discrete A .Hom = _≡_
discrete A .ident = refl
discrete A .compo refl refl = refl

Discrete : ∀{i} → Fun (sets i) (cats i i)
Discrete = Fun: discrete λ f → Fun: f λ { refl → refl }
