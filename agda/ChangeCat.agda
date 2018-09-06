{-# OPTIONS --postfix-projections #-}
module ChangeCat where

open import Cat
open import Prelude
open import TreeSet
open import Changes
open import Monads
open import Tones

-- There is a very simple pattern that comes up in many change functions, where
-- the derivative is "boring" - it's the same as the function itself, but
-- operating on the deltas. (The proof that it is a correct derivative is
-- usually simple as well, but I haven't found a strict pattern that it obeys.)
-- See the definition of boring-cfun, below.
--
-- We can in principle capture the type of this pattern, but the result is
-- ludicrously complicated:

-- boring-cfun : ∀ {j}{I : Set j} {F G : I -> Proset}
--             -> (f : ∀{i : I} -> F i ⇒ G i)
--             -> ∀ {A ΔA B ΔB : I} {PA PB}
--             -> (∀{da a b} -> PA da a b -> PB (ap f da) (ap f a) (ap f b))
--             -> ∀{d1 d2}
--             -> ChangeFun (Change: {{F A}} (F ΔA) PA d1)
--                          (Change: {{G A}} (G ΔA) PB d2)
-- boring-cfun f x = cfun f (π₂ • f) x -- ========== <-- the pattern ==========

-- Moreover, it's impossible to *use* boring-cfun without explicitly providing
-- some of its many implicit arguments, which destroys any concision one might
-- hope to gain. I note this here because it's a clear instance of types, even
-- dependent types, not being powerful enough to allow even a very obvious
-- refactoring without more pain than it's worth.

 -- Category of changes
instance
  changes : Cat _ _
  Obj changes = Change
  Hom changes = ChangeFun
  ident changes = cfun id π₂ id
  compo changes F@(cfun f df fok) (cfun g dg gok) =
    cfun (f • g) (func&deriv F • dg) (fok • gok)

  change-products : Products changes
  change-products .top = ⊤-change , cfun ≤⊤ ≤⊤ (λ _ → TT)
  change-products .glb a b .a∧b = change× a b
  change-products .glb a b .∧E₁ = cfun π₁ (π₂ • π₁) π₁
  change-products .glb a b .∧E₂ = cfun π₂ (π₂ • π₂) π₂
  change-products .glb a b .∧I (cfun f df fok) (cfun g dg gok) =
    cfun ⟨ f , g ⟩ ⟨ df , dg ⟩ ⟨ fok , gok ⟩

  change-sums : Sums changes
  bottom change-sums = ⊥-change , cfun ⊥≤ (π₁ • Fun: ⊥≤ λ { {()} }) λ { {_} {()} }
  lub change-sums a b .a∨b = change+ a b
  lub change-sums a b .∨I₁ = cfun in₁ (π₂ • in₁) rel₁
  lub change-sums a b .∨I₂ = cfun in₂ (π₂ • in₂) rel₂
  lub change-sums a b .∨E f g .funct = [ funct f , funct g ]
  lub change-sums a b .∨E {C} f g .deriv
    = uncurry (iso/∨ • [ flip [ use f , fail ] , flip [ fail , use g ] ])
    where use : ∀{A} -> A ≤ C -> 𝑫 A ⇒ iso (𝑶 A) ⇨ 𝑫 C
          use f = curry (swap • deriv f)
          fail : ∀{A B} -> A ≤ B ⇨ (𝑫 C)
          fail = curry (constant (dummy C))
  lub change-sums a b .∨E f g .is-id (rel₁ da) = is-id f da
  lub change-sums a b .∨E f g .is-id (rel₂ db) = is-id g db

  change-cc : CC changes
  CC.products change-cc = change-products
  _⇨_ {{change-cc}} = change→
  -- apply {{change-cc}} .funct = apply
  -- apply {{change-cc}} .deriv .ap ((f , a) , df , da) = ap df (a , da)
  -- apply {{change-cc}} .is-id (df:f→g , dx:x→y) = df:f→g dx:x→y
  -- curry {{change-cc}} (cfun f df ok) =
  --   cfun (curry f) (curry (isojuggle • df)) (λ da db → ok (da , db))
  apply {{change-cc}} .funct = apply
  apply {{change-cc}} .deriv .ap ((f , a) , df , da) = ap df (a , da)
  -- apply {{change-cc}} .deriv .map (fa≈gb , df≤ , da≤) = df≤ (juggle fa≈gb .proj₂ , da≤)
  apply {{change-cc}} .deriv .map {_} {(g , b) , (dg , db)} (fa≈gb , df≤dg , da≤db) = df≤dg • map dg (juggle fa≈gb .proj₂ , da≤db)
  apply {{change-cc}} .is-id (df:f→g , dx:x→y) = df:f→g dx:x→y
  curry {{change-cc}} (cfun f df ok) =
    cfun (curry f) (curry (isojuggle • df)) (λ da db → ok (da , db))

  change-Π : SetΠ zero changes
  SetΠ.Π change-Π = changeΠ
  SetΠ.Πi change-Π Γ→P .funct = Πi λ a → Γ→P a .funct
  SetΠ.Πi change-Π Γ→P .deriv = Πi λ a → Γ→P a .deriv
  SetΠ.Πi change-Π Γ→P .is-id df:f→g a = Γ→P a .is-id df:f→g
  SetΠ.Πe change-Π a = cfun (Πe a) (π₂ • Πe a) (λ df-ok → df-ok a)

 -- Showing that □ is a comonad on the category of changes.
Change□ : changes ≤ changes
ap  Change□ = change□
map Change□ (cfun f df ok) =
  cfun (map Iso f) (∧/iso • map Iso df) (map∧ ok (map Iso f .map))

instance
  Change□-comonad : Comonad Change□
  Comonad.dup Change□-comonad .funct = dup Iso
  Comonad.dup Change□-comonad .deriv = π₂ • dup Iso
  -- agh.
  Comonad.dup Change□-comonad .is-id p@(da:a→b , a≈b) = p , a≈b , swap {{sets}} a≈b
  Comonad.extract Change□-comonad = cfun (extract Iso) (π₂ • extract Iso) proj₁


-- Antisymmetry
antisym□≤ : ∀{A B C : Change} -> Antisymmetric _≡_ (𝑶 A .Hom)
          -> (𝑶 A .Obj -> B ≤ C) -> change□ A ≤ B ⇨ C
antisym□≤ antisym f .funct = antisym⇒ antisym (λ a → f a .funct)
antisym□≤ antisym f .deriv = π₁ • antisym⇒ (λ x≈y y≈x → uncurry antisym x≈y) (λ a → f a .deriv)
antisym□≤ antisym f .is-id (da , a≈a') with uncurry antisym a≈a'
... | refl = f _ .is-id
