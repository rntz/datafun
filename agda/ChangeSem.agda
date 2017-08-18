{-# OPTIONS --postfix-projections #-}
module ChangeSem where

open import Prelude
open import Cat
open import Prosets
open import Cast

-- We will need this a few times.
juggle : ∀{i j k l} {A B C D}
       -> Σ {i}{j} A C × Σ {k}{l} B D
       -> Σ (A × B) λ { (a , b) -> C a × D b }
juggle ((a , c) , (b , d)) = (a , b) , (c , d)


-- Prosets equipped with change structures
record Change : Set1 where
  field {{𝑶}} : Proset          -- O for objects
  field 𝑫 : Proset              -- D for deltas
  object = Obj 𝑶
  delta  = Obj 𝑫

  -- this needs to respect equivalence of objects & deltas, doesn't it? I think
  -- for all the ones we actually construct this will be the case; I'm not sure
  -- if we need it for any of the proofs we're doing.
  field isΔ : object -> delta -> Set

  Δ : object -> Set
  Δ a = ∃ λ da → isΔ a da

  -- ΣΔ ζ : Set
  -- ΣΔ = object × delta
  -- ζ = Σ[ a ∈ object ] Δ a

  -- update is ⊕. find is ⊖ (and zero).

  -- does update need to respect the order on da? I think it does!
  -- also, why doesn't update go to (Σ[ b ∈ object ] a ≤ b)?
  -- TODO: need that a ≤ a ⊕ da!
  --
  -- TODO: per discussion with Neel, update should be defined for all deltas,
  -- not just valid deltas. In theory this restricts the space of possible
  -- implementations/models; in practice I think it won't, and it will work for
  -- Datafun, at least.
  field update : ∀ a (da : Δ a) -> object
  field update-inc : ∀ {a} da -> a ≤ update a da

  -- (b ≈ update a da) means a ⊕ (b ⊖ a) = a.
  -- should `find` be monotone in b?
  -- or just respect equivalence in both arguments?
  -- what does it mean to respect equivalence in both arguments,
  -- when a ≤ b is a different type for different (even equivalent) a, b?
  field find : ∀{a b} -> a ≤ b -> Δ a
  field find-update : ∀{a b} (a≤b : a ≤ b) -> b ≈ update a (find a≤b)

  nil : ∀{a} -> Δ a
  nil = find id

  is-nil : ∀{a} -> a ≈ update a nil
  is-nil = find-update id

open Change public hiding (nil; is-nil)
open Change {{...}} public using (nil; is-nil)
  renaming (update to _⊕_; isΔ to _Δ?_)

 -- Pairs of elements and updates, ordered by their target, form a proset.
Δ* : Change -> Proset
Δ* A .Obj = Σ[ a ∈ object A ] Δ A a
Δ* A .Hom (a , da) (b , db) = a ⊕ da ≤ b ⊕ db
  where private instance aa = A
Δ* A .ident = id
Δ* A .compo = _•_

 -- Constructions on change structures
module _ (A : Change) where
  private instance aa = A; isoa = isos (𝑶 A)
  change□ : Change
  𝑶 change□ = isos (𝑶 A)
  𝑫 change□ = isos (𝑫 A)
  -- a valid □ change is a zero change
  change□ .isΔ a da = Σ[ va ∈ a Δ? da ] (a ≈ a ⊕ (da , va))
  change□ .update a (da , (is-ok , is-zero)) = a ⊕ (da , is-ok)
  change□ .update-inc (da , (is-ok , is-zero)) = is-zero
  -- There has to be a way to simplify this.
  change□ .find a≈b@(a≤b , b≤a) =
    find A a≤b .proj₁ , find A a≤b .proj₂ , a≈b • find-update A a≤b
  change□ .find-update (a≤b , b≤a) =
    find-update A a≤b , swap {{sets}} (find-update A a≤b)

module _ (A B : Change) where
  private instance aa = A; bb = B

  change× : Change
  𝑶 change× = 𝑶 A ∧ 𝑶 B
  𝑫 change× = 𝑫 A ∧ 𝑫 B
  change× .isΔ (a , b) (da , db) = a Δ? da × b Δ? db
  -- SO MUCH JUGGLING.
  change× .update (a , b) ((da , db) , (va , vb)) = a ⊕ (da , va) , b ⊕ (db , vb)
  change× .update-inc ((da , db) , (va , vb)) =
    update-inc A (da , va) , update-inc B (db , vb)
  change× .find (p , q) = juggle (find A p , find B q)
  change× .find-update (a , b) = juggle (find-update A a , find-update B b)

  -- Legit f df := "df is a legitimate change to f"
  -- In seminaive.tex, this is df ∈ Δ_{A -> B}(f).
  record Legit (f : 𝑶 A ⇒ 𝑶 B) (df : isos (𝑶 A) ∧ 𝑫 A ⇒ 𝑫 B) : Set where
    -- 1. valid input change --> valid output change
    field stays-valid : ∀{a da} -> a Δ? da -> ap f a Δ? ap df (a , da)

    derivΔ : ∀ {a} -> Δ A a -> Δ B (ap f a)
    derivΔ = λ { (da , va) → ap df (_ , da) , stays-valid va }

    w/δ : Δ* A .Obj → Δ* B .Obj
    w/δ = λ { (a , da) → ap f a , derivΔ da }

    -- 2. it's monotone in the order implied by (a,da) ↦ (a ⊕ da)
    field keeps-order : Hom (Δ* A) =[ w/δ ]⇒ Hom (Δ* B)

  open Legit public

  change→ : Change
  𝑶 change→ = 𝑶 A ⇨ 𝑶 B
  𝑫 change→ = (isos (𝑶 A) ∧ 𝑫 A) ⇨ 𝑫 B
  change→ .isΔ = Legit
  -- ap f x ⊕ derivΔ df-ok x nil
  change→ .update f (df , df-ok) .ap x = ap f x ⊕ derivΔ df-ok nil
  change→ .update f (df , df-ok) .map x≤y =
    df-ok .keeps-order (proj₂ is-nil • x≤y • proj₁ is-nil)
  change→ .update-inc {f} (df , df-ok) x≤y =
    map f x≤y • update-inc B (derivΔ df-ok nil)
  -- TODO: this could be simplified. I'm pulling an existential back over an arrow.
  -- (a -> ∃b (P b)) ==> (∃(f : a -> b) -> ∀ a -> P (f a)
  --
  -- FIXME: this is wrong!
  -- find (f≤g) = (x, dx) ↦ g (x + dx) - f x
  -- wait, FUCK, we don't know that dx is legit! FUCK!
  change→ .find f≤g .proj₁ .ap (x , dx) = find B (f≤g (update-inc A {!x , dx!})) .proj₁
  change→ .find f≤g .proj₁ .map {x , dx} {y , dy} (x≈y , dx≤dy) =
  -- find B (f≤g (id x)) .proj₁ ≤ find B (f≤g (id y)) .proj₁
  -- NB. this is an inequality on (𝑫 B) - on raw deltas!
    {!find B (f≤g {x} id)  !}
  change→ .find f≤g .proj₂ = {!!}
  change→ .find-update = {!!}

 -- Morphisms between change structures.
record ChangeFun (A B : Change) : Set where
  private instance aa = A; instance bb = B
  field func  : 𝑶 A ⇒ 𝑶 B
  field deriv : isos (𝑶 A) ∧ 𝑫 A ⇒ 𝑫 B
  field legit : Legit A B func deriv

  func&deriv : isos (𝑶 A) ∧ 𝑫 A ⇒ isos (𝑶 B) ∧ 𝑫 B
  func&deriv = ⟨ π₁ • map Isos func , deriv ⟩

  field is-zero : ∀ a da -> ap func (a ⊕ da) ≈ ap func a ⊕ derivΔ legit da

open ChangeFun public

infixr 9 _!_
_!_ : ∀{A B} -> ChangeFun A B -> 𝑶 A .Obj -> 𝑶 B .Obj
f ! x = func f .ap x

 -- Category of changes
instance
  changes : Cat _ _
  Obj changes = Change
  Hom changes = ChangeFun
  ident changes .func = id
  ident changes .deriv = π₂
  ident changes .legit .stays-valid x = x
  ident changes .legit .keeps-order = {!!}
  ident changes {A} .is-zero _ _ = isos (𝑶 A) .ident
  compo changes f g .func = func f • func g
  compo changes f g .deriv = func&deriv f • deriv g
  -- compo changes f g .legit = f .legit • g .legit
  compo changes f g .legit = {!!}
  compo changes {A}{B}{C} f g .is-zero a da = {!!}
    -- map Isos (func g) .map (is-zero f a da) • is-zero g (f ! a) (derivΔ f a da)
    -- where instance ciso = isos (𝑶 C)

-- -- It's cartesian!
-- instance
--   change-products : Products changes
--   _∧_ {{change-products}} = change×
--   π₁ {{change-products}} .func = π₁
--   π₁ {{change-products}} .deriv = π₂ • π₁
--   π₁ {{change-products}} .legit = π₁
--   -- π₁ {{change-products}} .is-zero _ _ = id , id
--   π₂ {{change-products}} .func = π₂
--   π₂ {{change-products}} .deriv = π₂ • π₂
--   π₂ {{change-products}} .legit = π₂
--   -- π₂ {{change-products}} .is-zero _ _ = id , id
--   ⟨_,_⟩ {{change-products}} f g .func = ⟨ func f , func g ⟩
--   ⟨_,_⟩ {{change-products}} f g .deriv = ⟨ deriv f , deriv g ⟩
--   ⟨_,_⟩ {{change-products}} f g .legit = ⟨ legit f , legit g ⟩
--   -- ⟨_,_⟩ {{change-products}} f g .is-zero x dx = juggle (f .is-zero x dx , g .is-zero x dx)

-- Is it cartesian closed?
-- Func : ∀{A B} -> 𝑶 (change→ A B) ⇒ (∣ A ∣ ⇨ ∣ B ∣)
-- Func .ap F = func F
-- Func .map F≤G = F≤G

-- instance
--   change-cc : CC changes
--   CC.products change-cc = change-products
--   _⇨_ {{change-cc}} = change→
--   apply {{change-cc}} .func = ∧-map Func id • apply
--   apply {{change-cc}} .deriv = {!!}
--   apply {{change-cc}} .legit = {!!}
--   -- apply {{change-cc}} .is-zero = {!!}
--   curry {{change-cc}} = {!!}
