module Cat2 where

open import Prelude
open import Cat

-- Possibly I should see also:
-- https://en.wikipedia.org/wiki/Internal_category

-- Really, we should take any monoidal structure on C.
record VCat {j k} (C : Cat j k) {{Prod : Products C}} i : Set (suc i ⊔ j ⊔ k) where
  private instance cc = C
  field OBJ : Set i
  field HOM : (a b : OBJ) -> Obj C
  -- need terminal object of C. Products doesn't currently give this.
  field Ident : ∀{a} -> {!!} ≤ HOM a a
  field Compo : ∀{a b c} -> HOM a b ∧ HOM b c ≤ HOM a c
  -- and we're going to ignore the coherence conditions / commuting diagrams.

open VCat public

Cat2 : ∀ i j k -> Set (suc (i ⊔ j ⊔ k))
Cat2 i j k = VCat (cats {j}{k}) i

-- open Cat2 {{...}} public using () renaming (Ident to Id; Compo to _●_)

-- Is this right? Ugh, I should read a category theory book...
record Products2 {i j k} (C : Cat2 i j k) : Set (i ⊔ j ⊔ k) where
  infixr 2 _∧_
  field _∧_ : Op (OBJ C)
  field π₁ : ∀{a b} -> ⊤-cat ≤ HOM C (a ∧ b) a
  field π₂ : ∀{a b} -> ⊤-cat ≤ HOM C (a ∧ b) b
  field pair : ∀{a b x} -> cat× (HOM C x a) (HOM C x b) ≤ HOM C x (a ∧ b)

module _ {i j k} (cat : Cat2 i j k) where
  record SumsIn (C : OBJ cat) : Set where
    infixr 2 _∨_
    field _∨_ : {!Hom (C ∧ C) C!}
