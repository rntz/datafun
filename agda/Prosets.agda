module Prosets where

open import Prelude
open import Cat
open import Decidability
open import Monads

Proset : Set1
Proset = Cat zero zero

prosets : Cat _ _
prosets = cats {zero} {zero}

-- A type for monotone maps.
infix 1 _⇒_
_⇒_ : Rel Proset _
_⇒_ = Fun


-- The proset of monotone maps between two prosets. Like the category of
-- functors and natural transformations, but without the naturality condition.
proset→ : (A B : Proset) -> Proset
proset→ A B .Obj = Fun A B
-- We use this definition rather than the more usual pointwise definition
-- because it makes more sense when generalized to categories.
proset→ A B .Hom F G = ∀ {x y} -> Hom A x y -> Hom B (ap F x) (ap G y)
proset→ A B .ident {F} = map F
proset→ A B .compo {F}{G}{H} F≤G G≤H {x}{y} x≤y = compo B (F≤G x≤y) (G≤H (ident A))

-- Now we can show that prosets is cartesian closed.
instance
  proset-cc : CC prosets
  CC.products proset-cc = cat-products
  _⇨_   {{proset-cc}} = proset→
  -- apply or eval
  apply {{proset-cc}} .ap (F , a) = ap F a
  apply {{proset-cc}} .map (F≤G , a≤a') = F≤G a≤a'
  -- curry or λ
  curry {{proset-cc}} {A}{B}{C} F .ap a .ap b    = ap F (a , b)
  curry {{proset-cc}} {A}{B}{C} F .ap a .map b   = map F (ident A , b)
  curry {{proset-cc}} {A}{B}{C} F .map a≤a' b≤b' = map F (a≤a' , b≤b')

-- If B has sums, then (A ⇒ B) has sums too.
module _ {A B : Proset} (bs : Sums B) where
  private instance b' = B; bs' = bs
  proset→-sums : Sums (proset→ A B)
  _∨_ {{proset→-sums}} f g .ap x = ap f x ∨ ap g x
  _∨_ {{proset→-sums}} f g .map x≤y = ∨-map (map f x≤y) (map g x≤y)
  in₁ {{proset→-sums}} {f}{g} x≤y = map f x≤y • in₁
  in₂ {{proset→-sums}} {f}{g} x≤y = map g x≤y • in₂
  [_,_] {{proset→-sums}} {f}{g}{h} f≤h g≤h x≤y = [ f≤h x≤y , g≤h x≤y ]
  init {{proset→-sums}} = constant init
  init≤ {{proset→-sums}} _ = init≤


-- The "equivalence quotient" of a proset. Not actually a category of
-- isomorphisms, since we don't require that the arrows be inverses. But if we
-- were gonna put equations on arrows, that's what we'd require.
Iso : (C : Proset) (a b : Obj C) -> Set
Iso C a b = Hom C a b × Hom C b a

infix 1 _≈_
_≈_ : {{C : Proset}} (a b : Obj C) -> Set
_≈_ {{C}} = Iso C

isos : Proset -> Proset
isos C .Obj = Obj C
isos C .Hom x y = Iso C x y
isos C .ident = ident C , ident C
isos C .compo (f₁ , f₂) (g₁ , g₂) = compo C f₁ g₁ , compo C g₂ f₂

isos≤? : ∀ A -> Decidable≤ A -> Decidable≤ (isos A)
isos≤? _ test x y = dec× (test x y) (test y x)

-- If (f : a -> b) is monotone, then (f : isos a -> isos b) is also monotone.
Isos : prosets ≤ prosets
ap Isos = isos
map Isos f = fun (λ { (x , y) -> map f x , map f y })

instance
  -- This comonad factors into an adjunction to groupoids, I believe.
  Isos-comonad : Comonad Isos
  Comonad.dup Isos-comonad = fun ⟨ id , swap ⟩
  Comonad.extract Isos-comonad = fun proj₁


-- The booleans, ordered false < true.
data bool≤ : Rel Bool zero where
  bool-refl : Reflexive bool≤
  false<true : bool≤ false true

false≤ : ∀{a} -> bool≤ false a
false≤ {false} = bool-refl
false≤ {true}  = false<true

instance
  bools : Cat _ _
  Obj bools = Bool
  Hom bools = bool≤
  ident bools = bool-refl
  compo bools bool-refl x = x
  compo bools false<true bool-refl = false<true

  -- I never thought I'd commit a proof by exhaustive case analysis,
  -- but I was wrong.
  bool-sums : Sums bools
  _∨_ {{bool-sums}} true  _ = true
  _∨_ {{bool-sums}} _  true = true
  _∨_ {{bool-sums}} _ _ = false
  in₁ {{bool-sums}} {false} = false≤
  in₁ {{bool-sums}} {true}  = bool-refl
  in₂ {{bool-sums}} {_}    {false} = false≤
  in₂ {{bool-sums}} {false} {true} = bool-refl
  in₂ {{bool-sums}} {true}  {true} = bool-refl
  [_,_] {{bool-sums}} {false} {false} x y = false≤
  [_,_] {{bool-sums}} {_}     {true}  {false} x ()
  [_,_] {{bool-sums}} {true}  {false} {false} () y
  [_,_] {{bool-sums}} {false} {true}  {true}  x y = bool-refl
  [_,_] {{bool-sums}} {true}  {false} {true}  x y = bool-refl
  [_,_] {{bool-sums}} {true}  {true}  {true}  x y = bool-refl
  init {{bool-sums}} = false
  init≤ {{bool-sums}} = false≤

  bool≤? : Decidable bool≤
  bool≤? false true = yes false<true
  bool≤? true  false = no λ {()}
  bool≤? false false = yes bool-refl
  bool≤? true  true = yes bool-refl

antisym:bool≤ : Antisymmetric _≡_ bool≤
antisym:bool≤ bool-refl _ = Eq.refl
antisym:bool≤ false<true ()


-- Natural numbers
open import Data.Nat as Nat using (ℕ; z≤n; s≤s) renaming (_≤_ to _≤'_; _⊔_ to _⊔'_)
open import Relation.Binary using (module DecTotalOrder)

instance
  ℕ≤ : Proset
  Obj ℕ≤ = ℕ
  Hom ℕ≤ = Nat._≤_
  ident ℕ≤ = DecTotalOrder.refl Nat.decTotalOrder
  compo ℕ≤ = DecTotalOrder.trans Nat.decTotalOrder

  -- ℕ forms a semilattice with 0 and ⊔ (max).
  ℕ-sums : Sums ℕ≤
  Sums._∨_ ℕ-sums = Nat._⊔_
  Sums.in₁ ℕ-sums {ℕ.zero}  {_}       = z≤n
  Sums.in₁ ℕ-sums {ℕ.suc a} {ℕ.zero}  = id
  Sums.in₁ ℕ-sums {ℕ.suc a} {ℕ.suc b} = s≤s in₁
  Sums.in₂ ℕ-sums {a}       {ℕ.zero}  = z≤n
  Sums.in₂ ℕ-sums {ℕ.zero}  {ℕ.suc b} = id
  Sums.in₂ ℕ-sums {ℕ.suc a} {ℕ.suc b} = s≤s (in₂ {a = a})
  [_,_] {{ℕ-sums}} z≤n x = x
  [_,_] {{ℕ-sums}} (s≤s f) z≤n = s≤s f
  [_,_] {{ℕ-sums}} (s≤s f) (s≤s g) = s≤s [ f , g ]
  Sums.init ℕ-sums  = 0
  Sums.init≤ ℕ-sums = z≤n
