module Changes2 where

open import Booleans
open import Cat
open import Prelude
open import Tones
open import TreeSet


-- Prosets equipped with change structures
record Change : Set1 where
  constructor Change:
  field {{𝑶}} : Proset          -- O for objects
  field 𝑫 : Proset              -- D for deltas

  -- this needs to respect equivalence of objects & deltas, doesn't it? I think
  -- for all the ones we actually construct this will be the case; I'm not sure
  -- if we need it for any of the proofs we're doing.
  field Path : ∀{a b} (a≤b : 𝑶 .Hom a b) (da : Obj 𝑫) -> Set
  IdPath : (a : Obj 𝑶) (da : Obj 𝑫) -> Set
  IdPath a da = Path {a} id da

  -- This hack is needed to prove Change has coproducts. We need it for the
  -- derivative of case-analysis, [_,_], to invent values to use in the
  -- impossible case branches.
  --
  -- Another strategy would be to require (dummy : 𝑶 ⇒ 𝑫). This complicates the
  -- code, but doesn't require that 𝑫 be inhabited for uninhabited 𝑶.
  field dummy : Obj 𝑫

open Change public

 -- Constructions on change structures
⊤-change ⊥-change : Change
⊤-change = Change: {{⊤}} ⊤ (λ _ _ → ⊤) TT
⊥-change = Change: {{⊥}} ⊤ (λ { {()} }) TT

change-SL : (P : Proset) (S : Sums P) -> Change
-- Hm, is this right? We don't use a≤b!
change-SL P S = Change: {{P}} P (λ {a} {b} a≤b da → a ∨ da ≈ b) ⊥
  where instance p = P; s = S

change-bool : Change
change-bool = change-SL bools bool-sums

change-tree : Change -> Change
change-tree A = change-SL (trees (𝑶 A)) (tree-sums (𝑶 A))

module _ (A : Change) where
  change□ : Change
  𝑶 change□ = iso (𝑶 A)
  𝑫 change□ = iso (𝑫 A)
  -- should this be (Path A a≤b da ∧ Path A b≤a da)?
  Path change□ a≈b@(a≤b , b≤a) da = Path A a≤b da
  dummy change□ = dummy A

module _ (A B : Change) where
  change× change+ change→ : Change
  change× = Change: {{𝑶 A ∧ 𝑶 B}} (𝑫 A ∧ 𝑫 B) (rel× (Path A) (Path B)) (dummy A , dummy B)

  data Path+ : {a b : 𝑶 A .Obj ⊎ 𝑶 B .Obj}
             -> (p : (rel+ (𝑶 A .Hom) (𝑶 B .Hom) a b)) (q : 𝑫 A .Obj ⊎ 𝑫 B .Obj)
             -> Set where
    rel₁ : ∀{a b a≤b p} -> Path A {a}{b} a≤b p -> Path+ (rel₁ a≤b) (inj₁ p)
    rel₂ : ∀{a b a≤b p} -> Path B {a}{b} a≤b p -> Path+ (rel₂ a≤b) (inj₂ p)

  change+ = Change: {{𝑶 A ∨ 𝑶 B}} (𝑫 A ∨ 𝑫 B) Path+ (inj₁ (dummy A))

  𝑶 change→ = 𝑶 A ⇨ 𝑶 B
  𝑫 change→ = (iso (𝑶 A) ∧ 𝑫 A) ⇨ 𝑫 B
  Path change→ f≤g df = ∀{a b a≤b da} (da-ok : Path A {a}{b} a≤b da)
                      -> Path B (f≤g a≤b) (ap df (a , da))
  dummy change→ = constant (dummy B)

changeΠ : (A : Set) (B : A -> Change) -> Change
changeΠ A B .𝑶 = catΠ A (λ a -> B a .𝑶)
changeΠ A B .𝑫 = catΠ A (λ a -> B a .𝑫)
changeΠ A B .Path F≤G dF = ∀ a -> Path (B a) (F≤G a) (dF a)
changeΠ A B .dummy a = dummy (B a)

 -- Morphisms between change structures.
Zero : (A : Change) (a : Obj (𝑶 A)) -> Set
Zero A a = Σ[ δ ∈ Obj (𝑫 A) ] IdPath A a δ

Deriv : ∀ A B (f : _) -> Set
Deriv A B f = Zero (change→ A B) f

record ChangeFun (A B : Change) : Set where
  constructor cfun
  field funct  : 𝑶 A ⇒ 𝑶 B
  field deriv : iso (𝑶 A) ∧ 𝑫 A ⇒ 𝑫 B
  field is-id : IdPath (change→ A B) funct deriv

  func&deriv : iso (𝑶 A) ∧ 𝑫 A ⇒ iso (𝑶 B) ∧ 𝑫 B
  func&deriv = ⟨ π₁ • map Iso funct , deriv ⟩

  cfun→zero : Deriv A B funct
  cfun→zero = deriv , is-id

open ChangeFun public

-- Is there a category of ChangeFuns? Is it useful? Am I really doing 2-category
-- theory?

zero→cfun : ∀{A B} f -> Deriv A B f -> ChangeFun A B
zero→cfun f (d , isd) = cfun f d isd

const-cfun : ∀{A B} (x : Obj (𝑶 B)) (dx : Obj (𝑫 B)) -> IdPath B x dx -> ChangeFun A B
const-cfun x dx dx:x→x = cfun (constant x) (constant dx) (λ _ → dx:x→x)

-- Is this useful? WHY? WHEN?
record Hom! (A : Change) (a b : 𝑶 A .Obj) : Set where
  field a≤b : 𝑶 A .Hom a b
  field path : 𝑫 A .Obj
  field path-ok : Path A a≤b path
