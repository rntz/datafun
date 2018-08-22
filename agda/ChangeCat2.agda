{-# OPTIONS --postfix-projections #-}
module ChangeCat2 where

open import Cat
open import Prelude
open import Prosets
open import TreeSet
open import Changes2
open import Monads

 -- Category of changes
instance
  changes : Cat _ _
  Obj changes = Change
  Hom changes = ChangeFun
  ident changes = cfun id π₂ id
  compo changes F@(cfun f df fok) (cfun g dg gok) =
    cfun (f • g) (func&deriv F • dg) (fok • gok)

  change-products : Products changes
  _∧_ {{change-products}} = change×
  π₁ {{change-products}} = cfun π₁ (π₂ • π₁) π₁
  π₂ {{change-products}} = cfun π₂ (π₂ • π₂) π₂
  ⟨_,_⟩ {{change-products}} (cfun f df fok) (cfun g dg gok) =
    cfun ⟨ f , g ⟩ ⟨ df , dg ⟩ ⟨ fok , gok ⟩
  ⊤ {{change-products}} = ⊤-change
  ≤⊤ {{change-products}} = cfun ≤⊤ ≤⊤ (λ _ → tt)

  change-sums : Sums changes
  lub change-sums a b .a∨b = change+ a b
  lub change-sums a b .∨I₁ = cfun in₁ (π₂ • in₁) rel₁
  lub change-sums a b .∨I₂ = cfun in₂ (π₂ • in₂) rel₂
  lub change-sums a b .∨E f g .funct = [ funct f , funct g ]
  lub change-sums a b .∨E {C} f g .deriv
    = uncurry (isos/∨ • [ flip [ use f , fail ] , flip [ fail , use g ] ])
    where use : ∀{A} -> A ≤ C -> 𝑫 A ⇒ isos (𝑶 A) ⇨ 𝑫 C
          use f = curry (swap • deriv f)
          fail : ∀{A B} -> A ≤ B ⇨ (𝑫 C)
          fail = curry (constant (dummy C))
  lub change-sums a b .∨E f g .is-id (rel₁ da) = is-id f da
  lub change-sums a b .∨E f g .is-id (rel₂ db) = is-id g db
  bottom change-sums = ⊥-change , cfun ⊥≤ (π₁ • Fun: ⊥≤ λ { {()} }) λ { {_} {()} }

  change-cc : CC changes
  CC.products change-cc = change-products
  _⇨_ {{change-cc}} = change→
  apply {{change-cc}} .funct = apply
  apply {{change-cc}} .deriv .ap ((f , a) , df , da) = ap df (a , da)
  apply {{change-cc}} .deriv .map (fa≈gb , df≤ , da≤) = df≤ (juggle fa≈gb .proj₂ , da≤)
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
map Change□ {A}{B} (cfun f df ok) = cfun (map Isos f) (∧/isos • map Isos df) ok

instance
  Change□-comonad : Comonad Change□
  Comonad.dup Change□-comonad = cfun (dup Isos) (π₂ • dup Isos) id
  Comonad.extract Change□-comonad = cfun (extract Isos) (π₂ • extract Isos) id
