{-# OPTIONS --postfix-projections #-}
open import Prelude
open import Cat
open import Prosets
import Data.Sum

module MonoContext (types : Proset) where

private Type = Obj types
private instance -types = types

-- Contexts are monotone maps taking a type to the sets of variables of that
-- type. Monotonicity here is with respect to subtyping: enlarge the type,
-- enlarge the set of variables.
instance
  cxs : Cat (suc zero) zero
  cxs = proset→ types sets

Cx : Set1
Cx = Obj cxs -- ie. Cx = Fun types sets

-- Union (or, categorical sum) of contexts.
instance
  cx-sums : Sums cxs
  bottom cx-sums = (fun {λ _ → ⊥} λ {x () }) , λ { a≤b () }
  lub cx-sums X Y .a∨b .ap a = ap X a ∨ ap Y a
  lub cx-sums X Y .a∨b .map b≤c = map∨ (map X b≤c) (map Y b≤c)
  lub cx-sums X Y .∨I₁ a≤b x = inj₁ (map X a≤b x)
  lub cx-sums X Y .∨I₂ a≤b y = inj₂ (map Y a≤b y)
  lub cx-sums X Y .∨E X≤Z Y≤Z a≤b = [ X≤Z a≤b , Y≤Z a≤b ]

-- A singleton context containing a variable of type `a` maps the type `b` to
-- the set of proofs that `a` is a subtype of `b`.
hyp : Type → Cx
hyp a .ap b = a ≤ b
hyp a .map b≤c a≤b = a≤b • b≤c

-- Consing onto contexts
infixr 4 _∷_
_∷_ : Type → Cx → Cx
a ∷ X = hyp a ∨ X

-- Context renamings
infix 1 _⊆_
_⊆_ : Cx → Cx → Set
_⊆_ = Hom cxs

-- Context renamings are natural transformations, i.e. given contexts X,Y and
-- types (a ≤ b), a renaming ρ : X ⊆ Y gives arrows such that this diagram
-- commutes:
--
--     Xa ----> Xb
--     |        |
--     ρa       ρb
--     ↓        ↓
--     Ya ----> Yb
--
-- As our categories are lawless, we don't actually enforce that this commutes.
-- It's convenient to instead have our natural transformations give back the
-- diagonal arrow Xa → Yb. If you look up the definition of the Hom for proset→,
-- you'll find that the above definition is equivalent to:
--
-- X ⊆ Y = {x y : Type} → Hom types x y → ap X x → ap Y y

∪/⊆ : ∀{X L R} → L ⊆ R → X ∨ L ⊆ X ∨ R
∪/⊆ {X} ρ a≤b = map∨ (map X a≤b) (ρ a≤b)
