{-# OPTIONS --postfix-projections #-}
module ChangeSem where

open import Prelude
open import Cat
open import Prosets
open import Cast
open import Monads

-- We will need this a lot.
juggle : ∀{i j k l} {A B C D}
       -> Σ {i}{j} A C × Σ {k}{l} B D
       -> Σ (A × B) λ { (a , b) -> C a × D b }
juggle ((a , c) , (b , d)) = (a , b) , (c , d)

-- For example:
isos∧ : ∀{A B} -> isos A ∧ isos B ⇒ isos (A ∧ B); isos∧ = fun juggle
∧isos : ∀{A B} -> isos (A ∧ B) ⇒ isos A ∧ isos B; ∧isos = fun juggle


-- Prosets equipped with change structures
record Change : Set1 where
  field {{𝑶}} : Proset          -- O for objects
  field 𝑫 : Proset              -- D for deltas
  object = Obj 𝑶
  delta  = Obj 𝑫

  -- this needs to respect equivalence of objects & deltas, doesn't it? I think
  -- for all the ones we actually construct this will be the case; I'm not sure
  -- if we need it for any of the proofs we're doing.
  field Path : (da : delta) (a b : object) -> Set

  field add : isos 𝑶 ∧ 𝑫 ⇒ 𝑶
  field sub : 𝑶 ∧ isos 𝑶 ⇒ 𝑫

  field is-add : ∀{a b da} (da:a→b : Path da a b) -> ap add (a , da) ≈ b
  field is-sub : ∀{a b} (a≤b : a ≤ b) -> Path (ap sub (b , a)) a b

  field path→≤ : ∀{a b da} (da:a→b : Path da a b) -> a ≤ b

  -- In "Theory of Changes" notation, add is ⊕ and sub is ⊖.
  --
  -- In our work, unlike in the Theory of Changes, add/⊕ is defined for all
  -- deltas, not just valid deltas. In theory this restricts the space of
  -- possible implementations/models; in practice I think it won't, and it will
  -- work for Datafun, at least.

  nil : object -> delta
  nil a = ap sub (a , a)

  is-nil : ∀{a} -> ap add (a , nil a) ≈ a
  is-nil {a} = is-add (is-sub id)

open Change public hiding (nil; is-nil)
open Change {{...}} public using (nil; is-nil) renaming (sub to _⊖_)
module _ {{A : Change}} where
  _⊕_ : object A → delta A → object A
  a ⊕ da = add A .ap (a , da)

 -- Pairs of elements and updates, ordered by their target, form a proset.
-- Δ* : Change -> Proset
-- Δ* A .Obj = Σ[ a ∈ object A ] Δ A a
-- Δ* A .Hom (a , da) (b , db) = a ⊕ da ≤ b ⊕ db
--   where private instance aa = A
-- Δ* A .ident = id
-- Δ* A .compo = _•_

 -- Constructions on change structures
change□ : Change -> Change
change□ A .𝑶 = isos (𝑶 A)
change□ A .𝑫 = isos (𝑫 A)
-- a valid □ change is a zero change
change□ A .Path da a b = Path A da a b ∧ (a ≈ b)
change□ A .add = isos∧ • map Isos (add A)
change□ A .sub = isos∧ • map Isos (sub A)
change□ A .is-add (da:a→b , a≈b) = a+da=b , swap {{sets}} a+da=b
  where a+da=b = is-add A da:a→b
change□ A .is-sub a≈b@(a≤b , _) = is-sub A a≤b , a≈b
change□ A .path→≤ = proj₂

module _ (A B : Change) where
  private instance aa = A; bb = B

  change× : Change
  change× .𝑶 = 𝑶 A ∧ 𝑶 B
  change× .𝑫 = 𝑫 A ∧ 𝑫 B
  change× .Path (da , db) = rel× (Path A da) (Path B db)
  -- TODO: figure out what "fun juggle" is doing here.
  change× .add = ∧-map ∧isos id • fun juggle • ∧-map (add A) (add B)
  change× .sub = ∧-map id ∧isos • fun juggle • ∧-map (sub A) (sub B)
  change× .is-add = ∧-map (is-add A) (is-add B) • juggle
  change× .is-sub = ∧-map (is-sub A) (is-sub B)
  change× .path→≤ = ∧-map (path→≤ A) (path→≤ B)

  -- Legit df f g := "df legitimately changes f to g"
  module _ (df : isos (𝑶 A) ∧ 𝑫 A ⇒ 𝑫 B) (f g : 𝑶 A ⇒ 𝑶 B) where
    Legit : Set
    Legit = ∀{da a b}
            -> Path A da a b
            -> Path B (ap df (a , da)) (ap f a) (ap g b)

    private
      -- TODO: This oughtta be defined somewhere else.
      f+df : isos (𝑶 A) ∧ 𝑫 A ⇒ 𝑶 B
      f+df = ⟨ π₁ • map Isos f , df ⟩ • add B

      keeps-order : ∀{da a b da' a' b'}
          -> Legit -> Path A da a b -> Path A da' a' b'
          -> b ≤ b' -> ap f+df (a , da) ≤ ap f+df (a' , da')
      keeps-order legit da:a→b da:a→b' b≤b' =
          is-add B (legit da:a→b) .proj₁
        • map g b≤b'
        • is-add B (legit da:a→b') .proj₂

    -- derivΔ : ∀ {a} -> Δ A a -> Δ B (ap f a)
    -- derivΔ = λ { (da , va) → ap df (_ , da) , stays-valid va }

    -- w/δ : Δ* A .Obj → Δ* B .Obj
    -- w/δ = λ { (a , da) → ap f a , derivΔ da }

    -- -- 2. it's monotone in the order implied by (a,da) ↦ (a ⊕ da)
    -- field keeps-order : Hom (Δ* A) =[ w/δ ]⇒ Hom (Δ* B)

  change→ : Change
  change→ .𝑶 = 𝑶 A ⇨ 𝑶 B
  change→ .𝑫 = (isos (𝑶 A) ∧ 𝑫 A) ⇨ 𝑫 B
  change→ .Path = Legit
  -- change→ .≤→path {f}{g} f≤g .proj₁ .ap (a , da) = ≤→path B asdf .proj₁
  --   where asdf : ap f a ≤ ap g (a ⊕ da)
  --         -- we're stuck because we need a ≤ a ⊕ da
  --         -- AND WE CAN'T GET THAT BECAUSE IT'S NOT ALWAYS TRUE FOR INVALID da
  --         -- (e.g. at □ type, there are invalid (non-zero) changes
  --         --  for which a ≉ a ⊕ da)
  --         asdf = {!!}
  -- change→ .≤→path f≤g .proj₁ .map = {!!}
  -- change→ .≤→path f≤g .proj₂ = {!!}

  -- FUUUUCK THIS isn't going to work
  -- because add : isos (𝑶 A) ∧ 𝑫 A → 𝑶 A
  -- is discrete in (𝑶 A)
  -- but we need to produce a function which is monotone in 𝑶 A
  -- but that requires legitimacy!

  -- THE BIG PICTURE PROBLEM:
  -- 1. legitimacy feeds back into monotonicity!
  --    need legitimacy of changes at function type to ensure monotonicity of result.
  --    (TODO: Show where.)
  -- 2. Ok, so why can't we just do without monotonicity for add, sub?
  -- 3. because *sub* at *function types* needs to guarantee *monotonicity of its output*!
  --    and to do that, we need monotonicity of sub in general.
  --    (TODO: Show where.)
  --
  -- Conclusion: WE HAVE TO GO FULL DEPENDENT TYPES.
  -- (Put this point into ze paper!)

  -- add : isos (𝑶 A ⇨ 𝑶 B) ∧ ((isos (𝑶 A) ∧ 𝑫 A) ⇨ 𝑫 B) ⇒ (𝑶 A ⇨ 𝑶 B)
  -- (f ⊕ df) x = f x ⊕ df x (0 x)
  -- (isos (𝑶 A ⇨ 𝑶 B) ∧ ((isos (𝑶 A) ∧ 𝑫 A) ⇨ 𝑫 B)) ∧ 𝑶 A ⇒ 𝑶 B
  --  f                   df                             x
  change→ .add = curry (⟨ ⟨ π₁ • π₁ • {!!} , π₂ ⟩ • apply , {!!} ⟩ • add B)

  -- (g ⊖ f) x dx = g (x + dx) ⊖ f x
  -- (𝑶 A ⇨ 𝑶 B) ∧ isos (𝑶 A ⇨ 𝑶 B) ⇒ (isos (𝑶 A) ∧ 𝑫 A) ⇨ 𝑫 B
  -- There has to be a better way to prove this.
  change→ .sub = curry (⟨ gx+dx , fx ⟩ • sub B)
    -- context: ((𝑶 A ⇨ 𝑶 B) ∧ isos (𝑶 A ⇨ 𝑶 B)) ∧ (isos (𝑶 A) ∧ 𝑫 A)
    --           g              f                    x             dx
    where fx = ⟨ π₁ • π₂ , π₂ • π₁ ⟩ • isos∧ • map Isos apply
          gx+dx = ⟨ π₁ • π₁ , π₂ • add A ⟩ • apply

  change→ .is-add = {!!}
  change→ .is-sub = {!!}
  change→ .path→≤ = {!!}

--   change→ : Change
--   𝑶 change→ = 𝑶 A ⇨ 𝑶 B
--   𝑫 change→ = (isos (𝑶 A) ∧ 𝑫 A) ⇨ 𝑫 B
--   change→ .isΔ = Legit
--   -- ap f x ⊕ derivΔ df-ok x nil
--   change→ .update f (df , df-ok) .ap x = ap f x ⊕ derivΔ df-ok nil
--   change→ .update f (df , df-ok) .map x≤y =
--     df-ok .keeps-order (proj₂ is-nil • x≤y • proj₁ is-nil)
--   change→ .update-inc {f} (df , df-ok) x≤y =
--     map f x≤y • update-inc B (derivΔ df-ok nil)
--   -- TODO: this could be simplified. I'm pulling an existential back over an arrow.
--   -- (a -> ∃b (P b)) ==> (∃(f : a -> b) -> ∀ a -> P (f a)
--   --
--   -- FIXME: this is wrong!
--   -- find (f≤g) = (x, dx) ↦ g (x + dx) - f x
--   -- wait, FUCK, we don't know that dx is legit! FUCK!
--   change→ .find f≤g .proj₁ .ap (x , dx) = find B (f≤g (update-inc A {!x , dx!})) .proj₁
--   change→ .find f≤g .proj₁ .map {x , dx} {y , dy} (x≈y , dx≤dy) =
--   -- find B (f≤g (id x)) .proj₁ ≤ find B (f≤g (id y)) .proj₁
--   -- NB. this is an inequality on (𝑫 B) - on raw deltas!
--     {!find B (f≤g {x} id)  !}
--   change→ .find f≤g .proj₂ = {!!}
--   change→ .find-update = {!!}

--  -- Morphisms between change structures.
-- record ChangeFun (A B : Change) : Set where
--   private instance aa = A; instance bb = B
--   field func  : 𝑶 A ⇒ 𝑶 B
--   field deriv : isos (𝑶 A) ∧ 𝑫 A ⇒ 𝑫 B
--   field legit : Legit A B func deriv

--   func&deriv : isos (𝑶 A) ∧ 𝑫 A ⇒ isos (𝑶 B) ∧ 𝑫 B
--   func&deriv = ⟨ π₁ • map Isos func , deriv ⟩

--   field is-zero : ∀ a da -> ap func (a ⊕ da) ≈ ap func a ⊕ derivΔ legit da

-- open ChangeFun public

-- infixr 9 _!_
-- _!_ : ∀{A B} -> ChangeFun A B -> 𝑶 A .Obj -> 𝑶 B .Obj
-- f ! x = func f .ap x

--  -- Category of changes
-- instance
--   changes : Cat _ _
--   Obj changes = Change
--   Hom changes = ChangeFun
--   ident changes .func = id
--   ident changes .deriv = π₂
--   ident changes .legit .stays-valid x = x
--   ident changes .legit .keeps-order = {!!}
--   ident changes {A} .is-zero _ _ = isos (𝑶 A) .ident
--   compo changes f g .func = func f • func g
--   compo changes f g .deriv = func&deriv f • deriv g
--   -- compo changes f g .legit = f .legit • g .legit
--   compo changes f g .legit = {!!}
--   compo changes {A}{B}{C} f g .is-zero a da = {!!}
--     -- map Isos (func g) .map (is-zero f a da) • is-zero g (f ! a) (derivΔ f a da)
--     -- where instance ciso = isos (𝑶 C)

-- -- -- It's cartesian!
-- -- instance
-- --   change-products : Products changes
-- --   _∧_ {{change-products}} = change×
-- --   π₁ {{change-products}} .func = π₁
-- --   π₁ {{change-products}} .deriv = π₂ • π₁
-- --   π₁ {{change-products}} .legit = π₁
-- --   -- π₁ {{change-products}} .is-zero _ _ = id , id
-- --   π₂ {{change-products}} .func = π₂
-- --   π₂ {{change-products}} .deriv = π₂ • π₂
-- --   π₂ {{change-products}} .legit = π₂
-- --   -- π₂ {{change-products}} .is-zero _ _ = id , id
-- --   ⟨_,_⟩ {{change-products}} f g .func = ⟨ func f , func g ⟩
-- --   ⟨_,_⟩ {{change-products}} f g .deriv = ⟨ deriv f , deriv g ⟩
-- --   ⟨_,_⟩ {{change-products}} f g .legit = ⟨ legit f , legit g ⟩
-- --   -- ⟨_,_⟩ {{change-products}} f g .is-zero x dx = juggle (f .is-zero x dx , g .is-zero x dx)

-- -- Is it cartesian closed?
-- -- Func : ∀{A B} -> 𝑶 (change→ A B) ⇒ (∣ A ∣ ⇨ ∣ B ∣)
-- -- Func .ap F = func F
-- -- Func .map F≤G = F≤G

-- -- instance
-- --   change-cc : CC changes
-- --   CC.products change-cc = change-products
-- --   _⇨_ {{change-cc}} = change→
-- --   apply {{change-cc}} .func = ∧-map Func id • apply
-- --   apply {{change-cc}} .deriv = {!!}
-- --   apply {{change-cc}} .legit = {!!}
-- --   -- apply {{change-cc}} .is-zero = {!!}
-- --   curry {{change-cc}} = {!!}
