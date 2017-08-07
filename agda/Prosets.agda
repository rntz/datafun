module Prosets where

open import Prelude
open import Cat

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
  init {{proset→-sums}} = const-fun init
  init≤ {{proset→-sums}} _ = init≤


-- The "equivalence quotient" of a proset. Not actually a category of
-- isomorphisms, since we don't require that the arrows be inverses.
isos : Proset -> Proset
isos C .Obj = Obj C
isos C .Hom x y = Hom C x y × Hom C y x
isos C .ident = ident C , ident C
isos C .compo (f₁ , f₂) (g₁ , g₂) = compo C f₁ g₁ , compo C g₂ f₂


-- The trivial proset.
⊤-proset : Proset
⊤-proset = record { Obj = ⊤ ; Hom = λ { tt tt → ⊤ } ; ident = tt ; compo = λ { tt tt → tt } }

-- The booleans, ordered false < true.
data bool≤ : Rel Bool zero where
  bool-refl : Reflexive bool≤
  false<true : bool≤ false true

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
  _∨_ {{bool-sums}} false y = y
  _∨_ {{bool-sums}} true _ = true
  in₁ {{bool-sums}} {false} {true} = false<true
  in₁ {{bool-sums}} {false} {false} = bool-refl
  in₁ {{bool-sums}} {true} = bool-refl
  in₂ {{bool-sums}} {false} {false} = bool-refl
  in₂ {{bool-sums}} {false} {true} = bool-refl
  in₂ {{bool-sums}} {true} {false} = false<true
  in₂ {{bool-sums}} {true} {true} = bool-refl
  [_,_] {{bool-sums}} {false} {false} {false} x y = bool-refl
  [_,_] {{bool-sums}} {false} {false} {true} x y = false<true
  [_,_] {{bool-sums}} {false} {true} {false} x ()
  [_,_] {{bool-sums}} {false} {true} {true} x y = bool-refl
  [_,_] {{bool-sums}} {true} {false} {false} () y
  [_,_] {{bool-sums}} {true} {false} {true} x y = bool-refl
  [_,_] {{bool-sums}} {true} {true} {false} () y
  [_,_] {{bool-sums}} {true} {true} {true} x y = bool-refl
  init {{bool-sums}} = false
  init≤ {{bool-sums}} {false} = bool-refl
  init≤ {{bool-sums}} {true} = false<true

antisym:bool≤ : Antisymmetric _≡_ bool≤
antisym:bool≤ bool-refl bool-refl = Eq.refl
antisym:bool≤ false<true ()
