{-# OPTIONS --postfix-projections #-}
module Cat where

open import Prelude
import Data.Sum

record Cat i j : Set (suc (i ⊔ j)) where
  -- no-eta-equality cons: requires annoying eta-expansion or coercion because
  -- some equalities no longer hold definitionally.
  --
  -- no-eta-equality pros: makes inferred types of holes not total rubbish.
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

instance
  sets : ∀{i} -> Cat (suc i) i
  Obj (sets {i}) = Set i
  Hom sets a b = a -> b
  ident sets x = x
  compo sets f g x = g (f x)

  cats : ∀{i j} -> Cat (suc (i ⊔ j)) (i ⊔ j)
  cats {i}{j} = Cat: (Cat i j) Fun (fun id) λ { (fun f) (fun g) → fun (f ∙ g) }

Proset : Set1
Proset = Cat zero zero

prosets : Cat _ _
prosets = cats {zero} {zero}

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

 ---------- Tones ----------
-- ARGH! Without eta-equality on categories, (Tone.at tone-id C) isn't
-- definitionally equal to C!
--
-- This could be fixed by making (at : Cat i j → Cat i j) a field rather than a
-- defined function, and adding a field requiring that the at field agrees with
-- its definition. However, this still won't get (op (op C)) to be
-- definitionally equal to C!
record Tone i j : Set (suc (i ⊔ j)) where
  constructor Tone:

  -- A tone is...
  -- (1) A parametric transformation on orderings of a set...
  field rel : (A : Cat i j) → Rel (Obj A) j
  field rel-id : ∀{{A : Cat i j}} {a} → rel A a a
  field rel∙ : ∀{{A : Cat i j}} {a b c} → rel A a b → rel A b c → rel A a c

  -- (2) ... which is functorial, without changing function behavior.
  field covary : ∀{A B} (f : Fun A B) -> rel A =[ ap f ]⇒ rel B

  at : Cat i j -> Cat i j
  at A .Obj = Obj A
  at A .Hom = rel A
  at A .ident = rel-id
  at A .compo = rel∙

  functor : cats ≤ cats
  ap functor = at
  map functor f = fun (covary f)


-- Four tones.
tone-id tone-op tone-iso : ∀{i j} → Tone i j
tone-id = Tone: Hom id _∙_ map

Tone.rel tone-op A x y = Hom A y x
Tone.rel-id tone-op = id
Tone.rel∙ tone-op f g = g ∙ f
Tone.covary tone-op f = map f

-- The "equivalence quotient" of a proset. Not actually a category of
-- isomorphisms, since we don't require that the arrows be inverses. But *if* we
-- were gonna put equations on arrows, that's what we'd require.
Tone.rel tone-iso A x y = Hom A x y × Hom A y x -- Same as _≈_.
Tone.rel-id tone-iso = id , id
Tone.rel∙ tone-iso (f₁ , f₂) (g₁ , g₂) = f₁ ∙ g₁ , g₂ ∙ f₂
Tone.covary tone-iso f (i≤j , j≤i) = map f i≤j , map f j≤i

tone-path : ∀{i} → Tone i i
Tone.rel tone-path = Connected
Tone.rel-id tone-path = path-by id
Tone.rel∙ tone-path = path∙
Tone.covary tone-path f = path-fold _ (path-by ∘ map f) path⁻¹ path∙

-- Tone functors.
iso op : ∀{i j} → Cat i j → Cat i j
iso = Tone.at tone-iso; op = Tone.at tone-op

Iso Op : ∀{i j} → cats {i}{j} ≤ cats
Iso = Tone.functor tone-iso; Op = Tone.functor tone-op

instance -- The category of tones.
  tones : ∀{i j} → Cat (suc (i ⊔ j)) (suc (i ⊔ j))
  Obj (tones {i}{j}) = Tone i j
  Hom tones T U = ∀{A} → Tone.at T A ≤ Tone.at U A
  ident tones = id
  compo tones T≤U U≤V = T≤U ∙ U≤V

 ---------- Cartesian structures ----------
-- Products!
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

open Products public using (top; glb)
open Sums public using (bottom; lub)

-- TODO: auto-conversion from products to sums in opposite category? or vice-versa?

module _ {i j} {{C : Cat i j}} where
  module _ {{P : Products C}} where open Products P public
  module _ {{S : Sums C}} where open Sums S public

 --- CC means "cartesian closed".
record CC {i j} (C : Cat i j) : Set (i ⊔ j) where
  constructor CC:
  private instance the-cat = C
  -- I used to have an "overlap" modifier on `products`. I removed it and
  -- everything _seems_ ok. TODO: Is "overlap" necessary here?
  field {{products}} : Products C
  -- TODO FIXME: shouldn't bind tighter than ∧.
  infixr 4 hom
  field hom : BinOp (Obj C)
  field apply : ∀{a b} -> hom a b ∧ a ≤ b
  field curry : ∀{Γ a b} -> Γ ∧ a ≤ b -> Γ ≤ hom a b

  call : ∀{Γ a b} -> Γ ≤ hom a b -> Γ ≤ a -> Γ ≤ b
  call f a = ⟨ f , a ⟩ ∙ apply

  swapply : ∀{a b : Obj C} -> a ∧ hom a b ≤ b
  swapply = swap ∙ apply

  uncurry : ∀{a b c : Obj C} -> a ≤ hom b c -> a ∧ b ≤ c
  uncurry f = map∧ f id ∙ apply

  flip : ∀{a b c : Obj C} -> a ≤ hom b c -> b ≤ hom a c
  flip f = curry (swap ∙ uncurry f)

  precompose : ∀{a b c : Obj C} -> a ≤ b -> hom b c ≤ hom a c
  precompose f = curry (map∧ id f ∙ apply)

  module _ {{S : Sums C}} where
    distrib-∧/∨ : ∀{a b c : Obj C} -> (a ∨ b) ∧ c ≤ (a ∧ c) ∨ (b ∧ c)
    distrib-∧/∨ = map∧ [ curry in₁ , curry in₂ ] id ∙ apply

open CC public using (hom)
module _ {i j} {{C : Cat i j}} {{cc : CC C}} where
  open CC cc public renaming (hom to _⇨_) hiding (products)

 --- Set-indexed products.
record SetΠ k {i j} (C : Cat i j) : Set (i ⊔ j ⊔ suc k) where
  constructor SetΠ:
  private instance the-cat = C
  field Π : (A : Set k) (P : A -> Obj C) -> Obj C
  field Πi : ∀{A P Γ} (Γ→P : (a : A) -> Γ ≤ P a) -> Γ ≤ Π A P
  field Πe : ∀{A P} (a : A) -> Π A P ≤ P a

  mapΠ : ∀{A B P Q} (F : B -> A) (G : ∀ b -> P (F b) ≤ Q b) -> Π A P ≤ Π B Q
  mapΠ F G = Πi λ b → Πe (F b) ∙ G b

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
    -- fwiddle = Πi Data.Sum.[ (λ x → π₁ ∙ Πe x) , (λ x → π₂ ∙ Πe x) ]

module _ {i j k} {{C : Cat i j}} {{Pi : SetΠ k C}} where open SetΠ Pi public

 -- Structure of basic categories.
instance
  set-products : ∀{i} -> Products (sets {i})
  top set-products = Lift Unit , _
  glb set-products a b = a × b / proj₁ / proj₂ / Data.Product.<_,_>
    where import Data.Product

  set-sums : ∀{i} -> Sums (sets {i})
  bottom set-sums = Lift ∅ , λ{()}
  lub set-sums a b = a ⊎ b / inj₁ / inj₂ / Data.Sum.[_,_]

  set-cc : ∀{i} -> CC (sets {i})
  set-cc = CC: Function (λ { (f , a) -> f a }) (λ f x y -> f (x , y))

  set-Π : ∀{i} -> SetΠ i (sets {i})
  set-Π = SetΠ: (λ A P → (x : A) -> P x) (λ Γ→P γ a → Γ→P a γ) (λ a ∀P → ∀P a)

⊤-cat ⊥-cat : ∀{i j} -> Cat i j
⊥-cat = Cat: (Lift ∅) (λ{()}) (λ { {()} }) λ { {()} }
⊤-cat = Cat: (Lift Unit) (λ _ _ -> Lift Unit) TT const

instance
  cat-products : ∀{i j} -> Products (cats {i}{j})
  top cat-products = ⊤-cat , fun ≤⊤
  glb cat-products a b = cat× a b / fun π₁ / fun π₂ / λ { (fun f) (fun g) → fun ⟨ f , g ⟩ }

  cat-sums : ∀{i j} -> Sums (cats {i}{j})
  bottom cat-sums = ⊥-cat , Fun: ⊥≤ λ{ {()} }
  lub cat-sums a b = cat+ a b / fun rel₁ / fun rel₂ / disj
    where disj : ∀{a b c} -> a ≤ c -> b ≤ c -> cat+ a b ≤ c
          disj F G = Fun: [ ap F , ap G ] λ { (rel₁ x) → map F x ; (rel₂ x) → map G x }

  cat-cc : ∀{i} -> CC (cats {i}{i})
  CC.products cat-cc = cat-products
  _⇨_   {{cat-cc}} = cat→
  apply {{cat-cc}} .ap (F , a) = ap F a
  apply {{cat-cc}} {A}{B} .map {F , _} {G , _} (F≤G , a≤b) = compo B F≤G (map G a≤b)
  curry {{cat-cc}} F .ap a .ap b = ap F (a , b)
  curry {{cat-cc}} {A}{B} F .ap a .map b≤b' = map F (ident A , b≤b')
  curry {{cat-cc}} {A}{B} F .map a≤a' = map F (a≤a' , ident B)

  cat-Π : ∀{i j k} -> SetΠ k (cats {i ⊔ k} {j ⊔ k})
  cat-Π = SetΠ: catΠ (λ Γ→P → fun (λ γ a → Γ→P a .map γ)) (λ a → fun (λ ∀P≤ → ∀P≤ a))

 -- Preserving cartesian structure over operations on categories.
module _ {i j k l C D} (P : Sums {i}{j} C) (Q : Sums {k}{l} D) where
  private instance cc = C; cs = P; dd = D; ds = Q
  -- used in {Proset,Change}Sem/Types*.agda
  cat×-sums : Sums (cat× C D)
  bottom cat×-sums = (⊥ , ⊥) , ⊥≤ , ⊥≤
  lub cat×-sums (a , x) (b , y)
    = (a ∨ b) , (x ∨ y) / in₁ , in₁ / in₂ , in₂
    / λ { (f₁ , f₂) (g₁ , g₂) → [ f₁ , g₁ ] , [ f₂ , g₂ ] }

-- If B has sums, then (A ⇒ B) has sums too. Used in ProsetSem.Types.
module _ {i j k l} {A : Cat i j} {B} (bs : Sums {k}{l} B) where
  private instance b' = B; bs' = bs
  instance
    cat→sums : Sums (cat→ A B)
    bottom cat→sums = constant ⊥ , ⊥≤
    -- bottom cat→sums = constant ⊥ , λ _ → ⊥≤
    lub cat→sums F G .a∧b .ap x = ap F x ∨ ap G x
    lub cat→sums F G .a∧b .map x≤y = map∨ (map F x≤y) (map G x≤y)
    lub cat→sums F G .∧E₁ = in₁
    lub cat→sums F G .∧E₂ = in₂
    lub cat→sums F G .∧I F≤H G≤H = [ F≤H , G≤H ]


-- Discrete category on a given set.
discrete : ∀{i} → Set i → Cat _ _
discrete A .Obj = A
discrete A .Hom = _≡_
discrete A .ident = refl
discrete A .compo refl refl = refl

Discrete : ∀{i} → Fun (sets {i}) cats
Discrete = Fun: discrete λ f → Fun: f λ { refl → refl }
