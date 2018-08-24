{-# OPTIONS --postfix-projections #-}
module CatOmega2 where

-- TO TALK TO: ANDY PITTS or Marcello Fiore
--
-- see also: Eugenia Cheng, "Definitions of Weak omega categories" (?)
-- http://cheng.staff.shef.ac.uk/guidebook/index.html ?
-- https://arxiv.org/abs/1212.5853 ?

open import Prelude

open import Data.Product hiding (map)
open import Relation.Binary hiding (_⇒_)


-- Bottom and top, at any level.
data ⊥ {i} : Set i where
record ⊤ {i} : Set i where constructor tt

⊥-elim : ∀{i j}{A : Set j} -> ⊥ {i} -> A
⊥-elim ()


-- "Wok" stands for "weak ω-category"
mutual
  record Wok {i} (Obj : Set i) : Set (suc i) where
    coinductive
    constructor Wok:
    infix  1 Hom
    infixr 9 compo
    field Arr : (a b : Obj) -> Set i
    field Hom : (a b : Obj) -> Wok (Arr a b)

    -- aren't these supposed to be functors?
    -- I guess we'll try to prove that they always are later.
    field ident : ∀{a} -> Arr a a
    field compo : ∀{a b c} (f : Arr a b) (g : Arr b c) -> Arr a c

    field idl : ∀{a b} f -> Iso (Hom a b) f (compo ident f)
    field idr : ∀{a b} f -> Iso (Hom a b) f (compo f ident)
    -- according to https://en.wikipedia.org/wiki/Bicategory, this isomorphism
    -- ought to be "natural". I'm not sure what that means in this setting.
    field assoc : ∀{a b c d} (f : Arr a b) (g : Arr b c) (h : Arr c d) ->
                  Iso (Hom a d) (compo f (compo g h)) (compo (compo f g) h)

  record Iso {i Obj} (C : Wok {i} Obj) (a b : Obj) : Set i where
    coinductive
    field a→b : Wok.Arr C a b
    field b→a : Wok.Arr C b a
    field ida : Iso (Wok.Hom C a a) (Wok.ident C) (Wok.compo C a→b b→a)
    field idb : Iso (Wok.Hom C b b) (Wok.ident C) (Wok.compo C b→a a→b)

open Wok public
open Wok {{...}} public using ()
  renaming (Hom to _⇒_; Arr to _≤_; ident to id; compo to _∙_)
open Iso public

-- infix 4 _≈_
-- _≈_ : ∀{i A} {{C : Wok {i} A}} {a b : A} (f g : a ≤ b) -> Set i
-- _≈_ {{C}} {a} {b} f g = Iso (a ⇒ b) f g


-- A wok is boring if all objects are isomorphic.
IsBoring : ∀{i A} -> Wok {i} A -> Set i
IsBoring W = ∀{a b} -> Iso W a b

boring : ∀{i A W} {{B : IsBoring {i}{A} W}} -> IsBoring W
boring = it


-- Trivial wok.
instance ⊤-wok : ∀{i} -> Wok (⊤ {i})
instance ⊤-iso : ∀{i} -> IsBoring (⊤-wok {i})

⊤-wok .Arr tt tt = ⊤
⊤-wok .Hom tt tt = ⊤-wok
⊤-wok .ident = tt
⊤-wok .compo tt tt = tt
⊤-wok .idl tt = ⊤-iso
⊤-wok .idr tt = ⊤-iso
⊤-wok .assoc tt tt tt = ⊤-iso

⊤-iso .a→b = tt
⊤-iso .b→a = tt
⊤-iso .ida = ⊤-iso
⊤-iso .idb = ⊤-iso


-- The empty wok
instance ⊥-wok : ∀{i} -> Wok (⊥ {i})
⊥-wok .Arr ()
⊥-wok .Hom ()
⊥-wok .ident {()}
⊥-wok .compo {()}
⊥-wok .idl {()}
⊥-wok .idr {()}
⊥-wok .assoc {()}


-- The indiscrete Wok, where every object is connected to every other by a
-- unique morphism.
Indiscrete : ∀{i A} -> Wok {i} A
Indiscrete .Arr a b = ⊤
Indiscrete .Hom a b = ⊤-wok
Indiscrete .ident = tt
Indiscrete .compo tt tt = tt
Indiscrete .idl tt = boring
Indiscrete .idr tt = boring
Indiscrete .assoc tt tt tt = boring

instance boringIndiscrete : ∀{i A} -> IsBoring (Indiscrete {i}{A})
boringIndiscrete .a→b = tt
boringIndiscrete .b→a = tt
boringIndiscrete .ida = boring
boringIndiscrete .idb = boring


-- Lifting a wok
LiftWok : ∀{i A} -> Wok {i} A -> ∀{j} -> Wok (Lift {ℓ = j} A)
LiftIso : ∀{i A} {C : Wok {i} A} {a b} (iso : Iso C a b) {j}
         -> Iso (LiftWok C {j}) (lift a) (lift b)

LiftWok {i} C {j} .Arr (lift a) (lift b) = Lift {ℓ = j} (Arr C a b)
LiftWok C .Hom (lift a) (lift b) = LiftWok (Hom C a b)
LiftWok C .ident = lift (ident C)
LiftWok C .compo (lift f) (lift g) = lift (compo C f g)
LiftWok C .idl (lift f) = LiftIso (idl C f)
LiftWok C .idr (lift g) = LiftIso (idr C g)
LiftWok C .assoc (lift f) (lift g) (lift h) = LiftIso (assoc C f g h)

LiftIso iso .a→b = lift (a→b iso)
LiftIso iso .b→a = lift (b→a iso)
LiftIso iso .ida = LiftIso (ida iso)
LiftIso iso .idb = LiftIso (idb iso)


-- The wok {0,1} with 0 < 1.
open import Data.Bool

data bool≤ : (a b : Bool) -> Set where
  f≤* : ∀{a} -> bool≤ false a
  t≤t : bool≤ true  true

bool-wok : Wok Bool
bool-wok .Arr = bool≤
bool-wok .Hom _ _ = Indiscrete
bool-wok .ident {false} = f≤*
bool-wok .ident {true} = t≤t
bool-wok .compo f≤* _   = f≤*
bool-wok .compo t≤t t≤t = t≤t
bool-wok .idl _ = boring
bool-wok .idr _ = boring
bool-wok .assoc _ _ _ = boring


-- Given a setoid, we can make a wok.
-- Wait, is this right? It's throwing away a lot of structure.
setoid→wok : ∀{i} (S : Setoid i i) -> Wok (Setoid.Carrier S)
setoid→wok S .Arr = Setoid._≈_ S
setoid→wok S .Hom a b = Indiscrete
setoid→wok S .ident = Setoid.refl S
setoid→wok S .compo = Setoid.trans S
setoid→wok S .idl _ = boring
setoid→wok S .idr _ = boring
setoid→wok S .assoc _ _ _ = boring


-- Product of woks.
{-# TERMINATING #-}
wok× : ∀{i j A B} (V : Wok {i} A) (W : Wok {j} B) -> Wok (A × B)
iso× : ∀{i j A B V W} {a₁ a₂ b₁ b₂} (F : Iso {i}{A} V a₁ b₁) (G : Iso {j}{B} W a₂ b₂)
     -> Iso (wok× V W) (a₁ , a₂) (b₁ , b₂)

wok× V W .Arr (a₁ , a₂) (b₁ , b₂) = Arr V a₁ b₁ × Arr W a₂ b₂
wok× V W .Hom (a₁ , a₂) (b₁ , b₂) = wok× (Hom V a₁ b₁) (Hom W a₂ b₂)
wok× V W .ident = ident V , ident W
wok× V W .compo (f₁ , f₂) (g₁ , g₂) = compo V f₁ g₁ , compo W f₂ g₂
wok× V W .idl (f₁ , f₂) = iso× (idl V f₁) (idl W f₂)
wok× V W .idr (f₁ , f₂) = iso× (idr V f₁) (idr W f₂)
wok× V W .assoc (f₁ , f₂) (g₁ , g₂) (h₁ , h₂) = iso× (assoc V f₁ g₁ h₁) (assoc W f₂ g₂ h₂)

iso× F G .a→b = a→b F , a→b G
iso× F G .b→a = b→a F , b→a G
iso× F G .ida = iso× (ida F) (ida G)
iso× F G .idb = iso× (idb F) (idb G)


-- blah
module _ {i : Level} where
  mutual
    Tower : (n : ℕ) -> Set (suc i)
    Tower 0 = Σ (Set i) Wok
    Tower (ℕ.suc n) = ∃ λ X → ∃ λ Y → Map n X Y

    record Map n (X Y : Tower n) : Set (suc i) where

  mutual
    -- the ℕ index is, strictly speaking, unnecessary
    data Sig : ℕ -> Set (suc i) where
      ⋆ : Sig 0
      cell : ∀{n} (s : Sig n) -> Elem s -> Elem s -> Sig (ℕ.suc n)

    Elem : ∀{n} -> Sig n -> Set (suc i)
    Elem ⋆ = Σ (Set i) Wok
    Elem (cell s A B) = Cell s A B

    record Cell {n} (S : Sig n) (X Y : Elem S) : Set (suc i) where
      coinductive
      -- for every (n-1)-cell

      -- for n = 0:
      --   S = ⋆
      --   X , Y : Elem S = Σ (Set i) Wok
      --   ap : proj₁ X -> proj₂ Y
      --
      -- for n = 1:
      --   S = cell ⋆ (A , U) (B , V)
      --   X , Y : Elem S = Cell ⋆ (A , U) (B , V)
      --   ap : ∀{a b : A} -> ???
      --   ap : ∀{a b : A} -> Hom U a b -> Hom V (ap X a) (ap Y b)?
      --   ap : (F : Σ[ ab : A × A ] (Hom U)) -> Hom V (ap XY (proj₁ F))
      field ap : ∀ n -> {!!} 


-- ω-functors
mutual
  record Fun {i j A B} (C : Wok {i} A) (D : Wok {j} B) : Set (suc (i ⊔ j)) where
    coinductive
    private instance cc = C; dd = D
    field ap : A -> B
    field up : ∀{a b} -> Fun (Hom C a b) (Hom D (ap a) (ap b))

    -- oh shit, we need to preserve id and ∙!
    field on-id : ∀{a : A} -> Iso (Hom D _ _) (ident D) (Ap up (ident C {a}))
    -- TODO: preserving ∙.

    map : ∀{a b} -> Arr C a b -> Arr D (ap a) (ap b)
    map = Ap up

  private Ap : ∀{i j A B C D} (F : Fun {i}{j}{A}{B} C D) -> A -> B
  Ap = Fun.ap

open Fun public

-- according to shachaf, a natural transformation e : F -> G : C -> D
-- is a map e : 2*C -> D such that e(0,-) = F and e(1,-) = G.
-- see also https://ncatlab.org/nlab/show/transfor
-- and https://ncatlab.org/nlab/show/pseudofunctor
--
-- maybe I should try the other style of doing category theory, where arrows
-- exist independently and we have dom and cod maps; or see
-- https://ncatlab.org/nlab/show/single-sorted+definition+of+a+category

record Nat {i j A B C D} (F G : Fun {i}{j}{A}{B} C D) : Set (suc (i ⊔ j)) where
  field foo : ∀{a} -> Arr D (ap F a) (ap G a)
  field nat : {!!}


-- -- Showing that id is functorial.
-- Id : ∀ {i A} (W : Wok {i} A) -> Fun W W
-- Id W .ap A = A
-- Id W .up = Id _

-- functorId : ∀{i A} (W : Wok {i} A) {a} -> Fun (⊤-wok {i}) (Hom W a a)
-- functorId W .ap tt = ident W
-- functorId W {a} .up {tt}{tt} = functorId (Hom W a a) {ident W}

-- -- TODO: show that composition is functorial.
-- -- First need to show that the wok of woks is cartesian.

-- 
-- -- Functors form a wok.
-- funs : ∀{i j A B} (C : Wok {i} A) (D : Wok {j} B) -> Wok (Fun C D)
-- -- wait, shit. I need commuting diagrams here! don't I?
-- -- something is wrong here.
-- -- what is a natural transformation, anyway?
-- --
-- -- according to shachaf, a natural transformation e : F -> G : C -> D
-- -- is a map e : 2*C -> D such that e(0,-) = F and e(1,-) = G.
-- -- see also https://ncatlab.org/nlab/show/transfor
-- funs C D .Arr F G = {!!}
-- funs C D .Hom F G = {!!}
-- funs C D .ident = {!!}
-- funs C D .compo = {!!}
-- funs C D .idl = {!!}
-- funs C D .idr = {!!}
-- funs C D .assoc = {!!}

-- -- Woks form a wok.
-- woks : ∀ i -> Wok (Σ[ A ∈ Set i ] Wok A)
-- woks i .Arr (A , V) (B , W) = Fun V W
-- woks i .Hom _ _ = funs _ _
-- woks i .ident = Id _
-- woks i .compo F G .ap x = ap G (ap F x)
-- woks i .compo F G .up = woks i .compo (up F) (up G)
-- woks i .idl F = {!!}
-- woks i .idr = {!!}
-- woks i .assoc = {!!}

-- 
-- -- thungs
-- open import Data.Nat using (ℕ)
-- Boom : ∀ i -> ℕ -> Set (suc i)
-- -- a 0-boom is a Wok.
-- -- a 1-boom is a pair of Woks.
-- -- a 2-boom is a pair of pairs of Woks.
-- -- Hm...
-- Boom i 0 = Σ[ A ∈ Set i ] Wok A
-- Boom i (ℕ.suc n) = Boom i n × Boom i n

-- 
