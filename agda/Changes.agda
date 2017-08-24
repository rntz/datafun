module Changes where

open import Cast
open import Cat
open import Prelude
open import Prosets
open import TreeSet


-- Prosets equipped with change structures
record Change : Set1 where
  constructor Change:
  field {{𝑶}} : Proset          -- O for objects
  field 𝑫 : Proset              -- D for deltas

  -- this needs to respect equivalence of objects & deltas, doesn't it? I think
  -- for all the ones we actually construct this will be the case; I'm not sure
  -- if we need it for any of the proofs we're doing.
  field Path : (da : Obj 𝑫) (a b : Obj 𝑶) -> Set

  -- This hack is needed to prove Change has coproducts. We need it for the
  -- derivative of case-analysis, [_,_], to invent values to use in the
  -- impossible case branches.
  --
  -- Another strategy would be to require (dummy : 𝑶 ⇒ 𝑫). This complicates the
  -- code, but doesn't require that 𝑫 be inhabited for uninhabited 𝑶.
  field dummy : Obj 𝑫

  IdPath : (da : Obj 𝑫) (a : Obj 𝑶) -> Set
  IdPath da a = Path da a a

open Change public

 -- Constructions on change structures
data rel3+ {A A' B B' C C' : Set} (R : A -> B -> C -> Set) (S : A' -> B' -> C' -> Set)
           : A ⊎ A' -> B ⊎ B' -> C ⊎ C' -> Set where
  rel₁ : ∀{a b c} -> R a b c -> rel3+ R S (inj₁ a) (inj₁ b) (inj₁ c)
  rel₂ : ∀{a b c} -> S a b c -> rel3+ R S (inj₂ a) (inj₂ b) (inj₂ c)

⊤-change ⊥-change : Change
⊤-change = Change: {{⊤-cat}} ⊤-cat (λ da a b → ⊤) (lift tt)
⊥-change = Change: {{⊥-cat}} ⊤-cat (λ { _ (lift ()) }) (lift tt)

change-SL : (P : Proset) (S : Sums P) -> Change
change-SL P S = Change: {{P}} P (λ da a b → a ∨ da ≈ b) init
  where instance p = P; s = S

change-bool : Change
change-bool = change-SL bools bool-sums

change-tree : Change -> Change
change-tree A = change-SL (trees (𝑶 A)) (tree-sums (𝑶 A))

changeΠ : (A : Set) (B : A -> Change) -> Change
changeΠ A B .𝑶 = catΠ A (λ a -> B a .𝑶)
changeΠ A B .𝑫 = catΠ A (λ a -> B a .𝑫)
changeΠ A B .Path df f g = ∀ a -> Path (B a) (df a) (f a) (g a)
changeΠ A B .dummy a = dummy (B a)

module _ (A : Change) where
  change□ : Change
  𝑶 change□ = isos (𝑶 A)
  𝑫 change□ = isos (𝑫 A)
  Path change□ da a b = Path A da a b ∧ (a ≈ b)
  dummy change□ = dummy A

module _ (A B : Change) where
  change× change+ change→ : Change
  change× = Change: {{𝑶 A ∧ 𝑶 B}} (𝑫 A ∧ 𝑫 B) paths (dummy A , dummy B)
    where paths = λ { (da , db) → rel× (Path A da) (Path B db) }

  change+ = Change: {{𝑶 A ∨ 𝑶 B}} (𝑫 A ∨ 𝑫 B) (rel3+ (Path A) (Path B)) (inj₁ (dummy A))

  𝑶 change→ = 𝑶 A ⇨ 𝑶 B
  𝑫 change→ = (isos (𝑶 A) ∧ 𝑫 A) ⇨ 𝑫 B
  Path change→ df f g = ∀{da a b} (da:a→b : Path A da a b)
                      -> Path B (ap df (a , da)) (ap f a) (ap g b)
  dummy change→ = constant (dummy B)

 -- Morphisms between change structures.
Zero : (A : Change) (a : Obj (𝑶 A)) -> Set
Zero A a = Σ[ δ ∈ Obj (𝑫 A) ] IdPath A δ a

Deriv : ∀ A B (f : _) -> Set
Deriv A B f = Zero (change→ A B) f

record ChangeFun (A B : Change) : Set where
  constructor cfun
  field funct  : 𝑶 A ⇒ 𝑶 B
  field deriv : isos (𝑶 A) ∧ 𝑫 A ⇒ 𝑫 B
  field is-id : IdPath (change→ A B) deriv funct

  func&deriv : isos (𝑶 A) ∧ 𝑫 A ⇒ isos (𝑶 B) ∧ 𝑫 B
  func&deriv = ⟨ π₁ • map Isos funct , deriv ⟩

  cfun→zero : Deriv A B funct
  cfun→zero = deriv , is-id

open ChangeFun public

zero→cfun : ∀{A B} f -> Deriv A B f -> ChangeFun A B
zero→cfun f (d , isd) = cfun f d isd

const-cfun : ∀{A B} (x : Obj (𝑶 B)) (dx : Obj (𝑫 B)) -> Path B dx x x -> ChangeFun A B
const-cfun x dx dx:x→x = cfun (constant x) (constant dx) (λ _ → dx:x→x)
