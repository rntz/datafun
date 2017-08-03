module Prosets where

open import Prelude

Proset : Set1
Proset = Cat Level.zero Level.zero

prosets : Cat _ _
prosets = cats {Level.zero} {Level.zero}

-- For readability's sake, we define _⇒_ to mean monotone maps (i.e. functors).
infix 3 _⇒_
_⇒_ : Rel Proset _
_⇒_ = Fun

-- The proset of monotone maps between two prosets. Like the category of
-- functors and natural transformations, but without the naturality condition.
proset⇒ : (A B : Proset) -> Proset
proset⇒ A B .Obj = Fun A B
-- We use this definition rather than the more usual pointwise definition
-- because it makes more sense when generalized to categories.
proset⇒ A B .Hom F G = ∀ {x y} -> Hom A x y -> Hom B (ap F x) (ap G y)
proset⇒ A B .ident {F} = cov F
proset⇒ A B .compo {F}{G}{H} F≤G G≤H {x}{y} x≤y = compo B (F≤G x≤y) (G≤H (ident A))

-- Now we can show that prosets is cartesian closed.
instance
  proset-cc : CCC _ _
  CCC.products proset-cc = cat-products
  _⇨_   {{proset-cc}} = proset⇒
  -- apply or eval
  apply {{proset-cc}} .ap (F , a) = ap F a
  apply {{proset-cc}} .cov (F≤G , a≤a') = F≤G a≤a'
  -- curry or λ
  curry {{proset-cc}} {A}{B}{C} F .ap a .ap b    = ap F (a , b)
  curry {{proset-cc}} {A}{B}{C} F .ap a .cov b   = cov F (ident A , b)
  curry {{proset-cc}} {A}{B}{C} F .cov a≤a' b≤b' = cov F (a≤a' , b≤b')


-- The "equivalence quotient" of a proset. Not actually a category of
-- isomorphisms, since we don't require that the arrows be inverses.
isos : ∀{i j} -> Cat i j -> Cat i j
isos C .Obj = Obj C
isos C .Hom x y = Hom C x y × Hom C y x
isos C .ident = ident C , ident C
isos C .compo (f₁ , f₂) (g₁ , g₂) = compo C f₁ g₁ , compo C g₂ f₂


-- The booleans, ordered false < true.
data bool≤ : Rel Bool Level.zero where
  bool-refl : Reflexive bool≤
  false<true : bool≤ false true

instance
  bools : Cat _ _
  Obj bools = Bool
  Hom bools = bool≤
  ident bools = bool-refl
  compo bools bool-refl x = x
  compo bools false<true bool-refl = false<true
