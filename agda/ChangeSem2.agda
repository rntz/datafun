{-# OPTIONS --postfix-projections #-}
module ChangeSem2 where

-- IDEA:
--
-- Actually, all we need is a logical relation that says:
--
-- ⟦δe⟧_A implements ⟦e ≤ e⟧_A.
--
-- that is, we interpret ≤ constructively at each type A, and define a logical
-- relation for "implementing (x ≤ y : A)". and I guess we should exhibit an ⊕
-- function?
--
-- meaning : (a : A) (da : ΔA) -> Maybe (Σ(b : A) a ≤ b)

-- maybe instead of Change-Posets, what we really have is *two different*
-- semantics in Poset, and a proof that they're equivalent: the usual one, and a
-- delta one, where (a ≤ b) is the type of deltas from a to b. and then some
-- argument about how ⟦δe⟧ relates to this.

-- I should try working this out on paper, as well as Agda.

open import Prelude
open import Cat
open import Prosets
open import Cast
open import Monads
open import TreeSet

juggle : ∀{i j k l} {A B C D}
       -> Σ {i}{j} A C × Σ {k}{l} B D
       -> Σ (A × B) λ { (a , b) -> C a × D b }
juggle ((a , c) , (b , d)) = (a , b) , (c , d)

assocᵣ : ∀{i j k A B} {C : Set k} -> Σ {i}{j} A B × C → Σ A (λ a → B a × C)
assocᵣ ((a , b) , c) = a , (b , c)

isos∧ : ∀{A B} -> isos A ∧ isos B ⇒ isos (A ∧ B); isos∧ = fun juggle
∧isos : ∀{A B} -> isos (A ∧ B) ⇒ isos A ∧ isos B; ∧isos = fun juggle


-- Prosets equipped with change structures
record Change : Set1 where
  field {{𝑶}} : Proset          -- O for objects
  object = Obj 𝑶

  -- How is this different from Hom/≤?
  -- It looks like it *isn't*!
  field Δ : (a b : object) -> Set
  -- Can we use *irrelevance* to capture the nature of deltas?
  -- field Δi : ∀{a b} .(a≤b : a ≤ b) → Δ a b
  field Δi : ∀{a b} (a≤b : a ≤ b) → Δ a b
  field Δe : ∀{a b} (aΔb : Δ a b) -> a ≤ b

open Change public

 -- Constructions on change structures
change□ : Change -> Change
change□ A .𝑶 = isos (𝑶 A)
change□ A .Δ a b = (a ≈ b) × Δ A a b
change□ A .Δi a≈b@(a≤b , _) = a≈b , Δi A a≤b
change□ A .Δe = proj₁

module _ (A B : Change) where
  private instance aa = A; bb = B
  change× : Change
  change× .𝑶 = 𝑶 A ∧ 𝑶 B
  change× .Δ = rel× (Δ A) (Δ B)
  change× .Δi (p , q) = Δi A p , Δi B q
  change× .Δe (p , q) = Δe A p , Δe B q

  change→ : Change
  change→ .𝑶 = 𝑶 A ⇨ 𝑶 B
  change→ .Δ f g = ∀{a b} -> Δ A a b -> Δ B (ap f a) (ap g b)
  change→ .Δi f≤g = Δe A • f≤g • Δi B
  change→ .Δe fΔg = Δi A • fΔg • Δe B

module _ (A : Change) where
  private instance aa = A; tree-cat = trees (isos (𝑶 A)); treesets = tree-sums (isos (𝑶 A))
  change-trees : Change
  change-trees .𝑶 = trees (isos (𝑶 A))
  -- here, the aΔb would be relevant, but the (a ∨ aΔb ≈ b) irrelevant.
  change-trees .Δ a b = Σ[ aΔb ∈ Obj (trees (isos (𝑶 A))) ] (a ∨ aΔb ≈ b)
  change-trees .Δi {a}{b} a≤b = b , [ a≤b , id ] , in₂
  change-trees .Δe (c , a∨c=b) = in₁ • proj₁ a∨c=b
