module Preorders-new where

open import Prelude
open import Cartesian-new

open import Relation.Binary using (Rel; Reflexive) public

-- A proset is just a name for a category regarded a certain way: we only care
-- about whether (a ⇨ b) is inhabited, not about its structure. In particular,
-- maps between prosets don't need to preserve id and •. (Although probably most
-- of those we define do, if you use the right equivalence relation.)
Proset : Set1
Proset = Cat Level.zero Level.zero

cat:proset = cat:cat {Level.zero} {Level.zero}

-- For readability's sake, we define _⇒_ to mean monotone maps (i.e. functors).
infix 3 _⇒_
_⇒_ : (a b : Proset) -> Set; _⇒_ = Homo


-- TODO: Ordering by projection, using Function._on_

-- -- this looks like a contravariant mapping function. Hm...
-- proset:on : ∀{A B R} (f : B -> A) -> Proset A R -> Proset B (R on f)
-- proset:on _ (IsCat: r t) = IsCat: r t


-- Pointwise and product relations over functions
-- rel-pointwise : ∀{i j k} {A : Set i} {B} -> Rel {j} B k -> (a b : A -> B) -> Set _
-- rel-pointwise R f g = ∀ x -> R (f x) (g x)

-- rel-Π : ∀{i j k} (A : Set i) (B : A -> Set j)
--       -> (∀ x -> Rel (B x) k) -> Rel (∀ x -> B x) _
-- rel-Π _ _ R f g = ∀ x → R x (f x) (g x)

-- pointwise : Set -> Proset -> Proset
-- Obj (pointwise A B) = A -> Obj B
-- Arr (pointwise A B) f g = rel-pointwise (Arr B) f g
-- ident (pointwise A B) _ = ident B
-- compo (pointwise A B) f g x = compo B (f x) (g x)

catΠ : ∀{i j k} (A : Set i) (B : A -> Cat j k) -> Cat _ _
catΠ A B .Obj         = ∀ x → B x .Obj
catΠ A B .Arr f g     = ∀ x → B x .Arr (f x) (g x)
catΠ A B .ident x     = B x .ident
catΠ A B .compo f g x = B x .compo (f x) (g x)

-- The proset of monotone maps between two prosets. Like the category of
-- functors and natural transformations, but without the naturality condition.
proset⇒ : (A B : Proset) -> Proset
proset⇒ A B .Obj = Homo A B
-- We use this definition rather than the more usual pointwise definition
-- because it makes more sense when generalized to categories.
proset⇒ A B .Arr F G = ∀ {x y} -> Arr A x y -> Arr B (ap F x) (ap G y)
proset⇒ A B .ident {F} = cov F
proset⇒ A B .compo {F}{G}{H} F≤G G≤H {x}{y} x≤y = compo B (F≤G x≤y) (G≤H (ident A))

-- -- Now we can show that cat:proset has exponentials.
-- instance
--   closed:proset : Closed cat:proset cat× proset⇒
--   -- _⇨_   {{closed:proset}} = proset⇒
--   -- apply or eval
--   apply {{closed:proset}} .ap (F , a) = ap F a
--   apply {{closed:proset}} .cov (F≤G , a≤a') = F≤G a≤a'
--   -- curry or λ
--   curry {{closed:proset}} {A}{B}{C} F .ap a .ap b    = ap F (a , b)
--   curry {{closed:proset}} {A}{B}{C} F .ap a .cov b   = cov F (ident A , b)
--   curry {{closed:proset}} {A}{B}{C} F .cov a≤a' b≤b' = cov F (a≤a' , b≤b')

-- Now we can show that cat:proset has exponentials.
instance
  closed:proset : Exponentials cat:proset products:cat proset⇒
  -- _⇨_   {{closed:proset}} = proset⇒
  -- apply or eval
  apply {{closed:proset}} .ap (F , a) = ap F a
  apply {{closed:proset}} .cov (F≤G , a≤a') = F≤G a≤a'
  -- curry or λ
  curry {{closed:proset}} {A}{B}{C} F .ap a .ap b    = ap F (a , b)
  curry {{closed:proset}} {A}{B}{C} F .ap a .cov b   = cov F (ident A , b)
  curry {{closed:proset}} {A}{B}{C} F .cov a≤a' b≤b' = cov F (a≤a' , b≤b')


-- The "equivalence quotient" of a preorder.
relEquiv : ∀{i j A} -> Rel {i} A j -> Rel A j
relEquiv R x y = R x y × R y x

-- Not actually a category of isomorphisms, since we don't require that the
-- arrows be inverses. But they usually will be.
catEquiv : ∀{i j} -> Cat i j -> Cat i j
Obj (catEquiv C) = Obj C
Arr (catEquiv C) = relEquiv (Arr C)
ident (catEquiv C) = ident C , ident C
compo (catEquiv C) (f₁ , f₂) (g₁ , g₂) = compo C f₁ g₁ , compo C g₂ f₂


-- The booleans, ordered false < true.
data bool≤ : Rel Bool Level.zero where
  bool-refl : Reflexive bool≤
  false<true : bool≤ false true

instance
  compose:bool≤ : Compose Bool bool≤
  ident compose:bool≤ = bool-refl
  compo compose:bool≤ bool-refl y = y
  compo compose:bool≤ false<true bool-refl = false<true

  catBool : Proset
  catBool = cat compose:bool≤


-- -- Reflexive transitive closure of a relation
-- data Path {A} (R : Rel A) : Rel A where
--   path-edge : ∀{a b} -> R a b -> Path R a b
--   path-refl : Reflexive (Path R)
--   path-trans : Transitive (Path R)

-- preorder:Path : ∀{A R} -> Preorder A (Path R)
-- preorder:Path = IsCat: path-refl path-trans
