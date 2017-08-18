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

  -- update is ⊕. ≤→Δ is ⊖ (and zero). do we need some lemma about how deltas
  -- are ordered and how that interacts with update?

  -- does update need to respect the order on da? I think it does!
  -- also, why doesn't update go to (Σ[ b ∈ object ] a ≤ b)?
  field update : ∀ a (da : Δ a) -> object

  -- (b ≈ update a da) means a ⊕ (b ⊖ a) = a.
  field ≤→Δ : ∀{a b} -> a ≤ b -> Δ a
  field ≤→Δ-update : ∀{a b} (a≤b : a ≤ b) -> b ≈ update a (≤→Δ a≤b)

  nil : ∀{a} -> Δ a
  nil = ≤→Δ id

open Change public hiding (nil)
open Change {{...}} public using (nil)
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
  private instance aa = A
  change□ : Change
  𝑶 change□ = isos (𝑶 A)
  𝑫 change□ = isos (𝑫 A)
  -- a valid □ change is a zero change
  change□ .isΔ a da = Σ[ va ∈ a Δ? da ] (a ≈ a ⊕ (da , va))
  change□ .update a (da , (is-ok , is-zero)) = a ⊕ (da , is-ok)
  change□ .≤→Δ (a≤b , b≤a) = {!!}
  change□ .≤→Δ-update = {!!}

module _ (A B : Change) where
  private instance aa = A; bb = B

  change× : Change
  𝑶 change× = 𝑶 A ∧ 𝑶 B
  𝑫 change× = 𝑫 A ∧ 𝑫 B
  change× .isΔ (a , b) (da , db) = a Δ? da × b Δ? db
  change× .update (a , b) ((da , db) , (va , vb)) = a ⊕ (da , va) , b ⊕ (db , vb)
  change× .≤→Δ (p , q) = juggle (≤→Δ A p , ≤→Δ B q)
  change× .≤→Δ-update (a , b) = juggle (≤→Δ-update A a , ≤→Δ-update B b)
  -- change× .≤→Δ (p , q) with ≤→Δ A p | ≤→Δ B q
  -- change× .≤→Δ (p , q) | (a , c) , e , g | (b , d) , f , h =
  --   ((a , b) , (c , d)) , (e , f) , (g , h)

  -- Legit f df := "df is a legitimate change to f"
  -- In seminaive.tex, this is df ∈ Δ_{A -> B}(f).
  record Legit (f : 𝑶 A ⇒ 𝑶 B) (df : isos (𝑶 A) ∧ 𝑫 A ⇒ 𝑫 B) : Set where
    -- 1. valid input change --> valid output change
    field stays-valid : ∀{a da} -> a Δ? da -> ap f a Δ? ap df (a , da)
    -- 2. it's monotone in the order implied by (a,da) ↦ (a ⊕ da)
    -- Hom (Δ* A) =[ (λ { (x , dx) → {!!} }) ]⇒ Hom (Δ* B)
    field keeps-order : {!!}    -- TODO

    -- TODO: rename
    derivΔ : ∀ a -> Δ A a -> Δ B (ap f a)
    derivΔ a (da , va) = ap df (a , da) , stays-valid va

  open Legit public

  change→ : Change
  𝑶 change→ = 𝑶 A ⇨ 𝑶 B
  𝑫 change→ = (isos (𝑶 A) ∧ 𝑫 A) ⇨ 𝑫 B
  change→ .isΔ = Legit
  change→ .update f (df , df-ok) .ap x = ap f x ⊕ derivΔ df-ok x nil
  change→ .update f df .map = {!!}
  change→ .≤→Δ = {!!}
  change→ .≤→Δ-update = {!!}

 -- Morphisms between change structures.
record ChangeFun (A B : Change) : Set where
  private instance aa = A; instance bb = B
  field func  : 𝑶 A ⇒ 𝑶 B
  field deriv : isos (𝑶 A) ∧ 𝑫 A ⇒ 𝑫 B

  func&deriv : isos (𝑶 A) ∧ 𝑫 A ⇒ isos (𝑶 B) ∧ 𝑫 B
  func&deriv = ⟨ π₁ • map Isos func , deriv ⟩

  field legit : Legit A B func deriv

  -- field legit : ∀{a da} -> a Δ? da -> ap func a Δ? ap deriv (a , da)

  -- derivΔ : ∀ a -> Δ A a -> Δ B (ap func a)
  -- derivΔ a (da , va) = ap deriv (a , da) , stays-valid legit va

  -- -- FIXME: wait a minute, I think this needs to be a field!
  -- -- yes, it does! or something guaranteeing it!
  -- -- (would is-zero guarantee this?)
  -- foo : Δ* A ⇒ Δ* B
  -- ap  foo (a , da) = ap func a , derivΔ legit a da
  -- map foo {a , da} {b , db} a+da≤b+db = {!map func a+da≤b+db!}

  -- TODO: re-add this!
  field is-zero : ∀ a da -> ap func (a ⊕ da) ≈ ap func a ⊕ derivΔ legit a da

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
  ident changes .legit = {!!}
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
