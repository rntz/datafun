module Changes where

open import Cat
open import Prelude
open import Prosets
open import TreeSet

juggle : ∀{i j k l} {A B C D}
       -> Σ {i}{j} A C × Σ {k}{l} B D
       -> Σ (A × B) λ { (a , b) -> C a × D b }
juggle ((a , c) , (b , d)) = (a , b) , (c , d)

constant : ∀{A B} -> Obj B -> A ⇒ B
constant {A}{B} x = Fun: (λ _ → x) (λ _ → ident B)

isos∧ : ∀{A B} -> isos A ∧ isos B ⇒ isos (A ∧ B)
isos∧ = fun juggle

isos∨ : ∀{A B} -> isos (A ∨ B) ⇒ isos A ∨ isos B
isos∨ .ap = id
isos∨ .map (rel₁ p , rel₁ q) = rel₁ (p , q)
isos∨ .map (rel₂ p , rel₂ q) = rel₂ (p , q)

isojuggle : ∀{A B C D} -> (isos A ∧ B) ∧ (isos C ∧ D) ⇒ isos (A ∧ C) ∧ (B ∧ D)
isojuggle = fun juggle • ∧-map isos∧ id

module _ {{A : Proset}} {{Sum : Sums A}} where
  juggle∨ : ∀{a b c d : Obj A} -> (a ∨ b) ∨ (c ∨ d) ≤ (a ∨ c) ∨ (b ∨ d)
  juggle∨ = [ ∨-map in₁ in₁ , ∨-map in₂ in₂ ]

  juggle∨≈ : ∀{a b c d : Obj A} -> (a ∨ b) ∨ (c ∨ d) ≈ (a ∨ c) ∨ (b ∨ d)
  juggle∨≈ = juggle∨ , juggle∨

  ∨≈ : ∀{a b a' b' : Obj A} -> a ≈ a' -> b ≈ b' -> (a ∨ b) ≈ (a' ∨ b')
  ∨≈ a≈a' b≈b' = ∨-map (proj₁ a≈a') (proj₁ b≈b') , ∨-map (proj₂ a≈a') (proj₂ b≈b')


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

open Change public

 -- Constructions on change structures
data rel3+ {A A' B B' C C' : Set} (R : A -> B -> C -> Set) (S : A' -> B' -> C' -> Set)
           : A ⊎ A' -> B ⊎ B' -> C ⊎ C' -> Set where
  rel₁ : ∀{a b c} -> R a b c -> rel3+ R S (inj₁ a) (inj₁ b) (inj₁ c)
  rel₂ : ∀{a b c} -> S a b c -> rel3+ R S (inj₂ a) (inj₂ b) (inj₂ c)

⊤-change ⊥-change : Change
⊤-change = Change: {{⊤-cat}} ⊤-cat (λ da a b → ⊤) (lift tt)
⊥-change = Change: {{⊥-cat}} ⊤-cat (λ { _ (lift ()) }) (lift tt)

change-bool : Change
change-bool = Change: {{bools}} bools (λ da a b → (a ∨ da) ≈ b) false

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

  change-tree : Change
  𝑶 change-tree = trees (𝑶 A)
  𝑫 change-tree = trees (𝑶 A)
  Path change-tree da a b = Hom (isos (trees (𝑶 A))) (node a da) b
  dummy change-tree = empty

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
record ChangeFun (A B : Change) : Set where
  constructor cfun
  field func  : 𝑶 A ⇒ 𝑶 B
  field deriv : isos (𝑶 A) ∧ 𝑫 A ⇒ 𝑫 B
  field is-id : Path (change→ A B) deriv func func

  func&deriv : isos (𝑶 A) ∧ 𝑫 A ⇒ isos (𝑶 B) ∧ 𝑫 B
  func&deriv = ⟨ π₁ • map Isos func , deriv ⟩

open ChangeFun public
