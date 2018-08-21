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
  top {{change-products}} = ⊤-change
  ≤top {{change-products}} = cfun ≤top ≤top (λ _ → tt)

  -- change-sums : Sums changes
  -- _∨_ {{change-sums}} = change+
  -- in₁ {{change-sums}} = cfun in₁ (π₂ • in₁) rel₁
  -- in₂ {{change-sums}} = cfun in₂ (π₂ • in₂) rel₂
  -- [_,_] {{change-sums}} f g .funct = [ funct f , funct g ]
  -- -- isos (𝑶 a ∨ 𝑶 b) ∧ (𝑫 a ∨ 𝑫 b) ⇒ 𝑫 c
  -- -- this is the bit where I have to invent values.
  -- [_,_] {{change-sums}} {A}{B}{C} f g .deriv = uncurry (isos/∨ • [ flip [ use f , fail ]
  --                                                                , flip [ fail , use g ] ])
  --   where use : ∀{A} -> A ≤ C -> 𝑫 A ⇒ isos (𝑶 A) ⇨ 𝑫 C
  --         fail : ∀{A B} -> A ⇒ B ⇨ 𝑫 C
  --         use f = curry (swap • deriv f)
  --         fail = curry (constant (dummy C))
  -- [_,_] {{change-sums}} f g .is-id (rel₁ da) = is-id f da
  -- [_,_] {{change-sums}} f g .is-id (rel₂ db) = is-id g db
  -- bot {{change-sums}} = ⊥-change
  -- bot≤ {{change-sums}} = cfun bot≤ (π₁ • Fun: bot≤ λ { {lift ()} }) (λ { {_} {lift ()} })

  change-joins : Joins changes
  Joins.join change-joins a b .a∨b = change+ a b
  Joins.join change-joins a b .∨I₁ = cfun in₁ (π₂ • in₁) rel₁
  Joins.join change-joins a b .∨I₂ = cfun in₂ (π₂ • in₂) rel₂
  Joins.join change-joins a b .∨E f g .funct = [ funct f , funct g ]
  Joins.join change-joins a b .∨E {C} f g .deriv
    = uncurry (isos/∨ • [ flip [ use f , fail ] , flip [ fail , use g ] ])
    where use : ∀{A} -> A ≤ C -> 𝑫 A ⇒ isos (𝑶 A) ⇨ 𝑫 C
          use f = curry (swap • deriv f)
          fail : ∀{A B} -> A ≤ B ⇨ (𝑫 C)
          fail = curry (constant (dummy C))
  Joins.join change-joins a b .∨E f g .is-id (rel₁ da) = is-id f da
  Joins.join change-joins a b .∨E f g .is-id (rel₂ db) = is-id g db
  Joins.bottom change-joins = ⊥-change , cfun bot≤ (π₁ • Fun: bot≤ λ { {lift ()} }) λ { {_} {lift ()} }

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
