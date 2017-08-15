module ChangeSem where

open import Prelude
open import Cat
open import Prosets

-- Prosets equipped with change structures
record Change : Set1 where
  field {{objects}} : Proset
  field deltas : Proset
  object = Obj objects
  change = Obj deltas

  -- FIXME: this needs to respect equivalence! (doesn't it?)
  field valid : object -> change -> Set
  Δ : object -> Set
  Δ a = Σ[ da ∈ change ] valid a da

  -- update is ⊕. choose is ⊖ (and zero). choose-update says they interact
  -- properly. does update need to respect the order on da? I think it does!
  field update : ∀ a (da : Δ a) -> object
  field choose : ∀{a b} -> a ≤ b -> Δ a
  -- a ⊕ (b ⊖ a) = a
  field choose-update : ∀{a b} (p : a ≤ b) -> b ≈ update a (choose p)

  -- do we need some lemma about how deltas are ordered and how that interacts
  -- with update?

  nil : ∀{a} -> Δ a
  nil = choose id

open Change public
open Change {{...}} public using () renaming (update to _⊕_)

 -- Morphisms between change structures.
record ChangeFun (A B : Change) : Set where
  private instance aa = objects A; bb = objects B; instance aaa = A; instance bbb = B
  field func  : objects A ⇒ objects B
  field deriv : isos (objects A) ∧ deltas A ⇒ deltas B
  field legit : ∀{a da} -> valid A a da -> valid B (ap func a) (ap deriv (a , da))

  derivΔ : ∀ a -> Δ A a -> Δ B (ap func a)
  derivΔ a da = ap deriv (a , proj₁ da) , legit (proj₂ da)

  -- how does this property fall out of functoriality?
  -- can this be phrased as preserving an Iso?
  field is-deriv : ∀ a da -> ap func (a ⊕ da) ≈ ap func a ⊕ derivΔ a da

  func&deriv : isos (objects A) ∧ deltas A ⇒ isos (objects B) ∧ deltas B
  func&deriv = ⟨ π₁ • map Isos func , deriv ⟩

open ChangeFun public

infixr 9 _!_
_!_ : ∀{A B} -> ChangeFun A B -> Obj (objects A) -> Obj (objects B)
f ! x = func f .ap x

 -- Category of change structures
changes : Cat _ _
Obj changes = Change
Hom changes = ChangeFun
ident changes .func = id
ident changes .deriv = π₂
ident changes .legit = id
ident changes {a} .is-deriv _ _ = ident (isos (objects a))
compo changes f g .func = func f • func g
compo changes f g .deriv = func&deriv f • deriv g
compo changes f g .legit = f .legit • g .legit
compo changes {A}{B}{C} f g .is-deriv a da =
  map Isos (func g) .map (is-deriv f a da) • is-deriv g (f ! a) (derivΔ f a da)
  where instance ciso = isos (objects C)

-- WTS:
-- (g ! (f ! (a ⊕ da)))
-- ≈
-- (g ! ((f ! a) ⊕ (derivΔ f a da)))

-- WTS:
-- g ! (f ! (a ⊕ da))
-- ≈
-- (g ! (f ! a)
--  ⊕
--  (g ! (func&deriv f .ap (a , proj₁ da)) ,
--   g .legit (f .legit (proj₂ da)))))
