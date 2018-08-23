{-# OPTIONS --postfix-projections #-}
open import Prelude
open import Cat
open import Prosets
import Data.Sum

module SetContext (types : Proset) where

private Type = Obj types
private instance -types = types

-- A set of variables with values ("types") in A.
record Cx : Set1 where
  constructor Cx:
  field Var : Set
  field typeof : Var -> Type

open Cx public

pattern here = inj₁ tt
pattern next x = inj₂ x

hyp : Type → Cx
hyp a = Cx: ⊤ λ { tt → a }


-- Context renamings.
infix 1 _⊆_
_⊆_ : Cx → Cx → Set

-- is this something I've already defined? or (an instance of) some standard
-- concept in category theory? Perhaps, (catΣ[ a ∈ opp sets ] catΠ a types)?
Cx: X f ⊆ Cx: Y g = Σ[ ρ ∈ (X → Y) ] (∀ x → f x ≤ g (ρ x) )

instance
  cxs : Cat _ _
  Obj cxs = Cx
  Hom cxs = _⊆_
  ident cxs = (id , λ _ → id)
  compo cxs (f , f′) (g , g′) = f • g , λ _ → f′ _ • g′ _

  -- Contexts have coproducts, namely unions.
  cx-sums : Sums cxs
  bottom cx-sums = Cx: ∅ (λ ()) , (λ ()) , λ ()
  lub cx-sums (Cx: X Xf) (Cx: Y Yf)
    = Cx: (X ⊎ Y) [ Xf , Yf ]
    / (inj₁ , λ _ → id) / (inj₂ , λ _ → id)
    / λ { (f , f') (g , g') → [ f , g ] , Data.Sum.[ f' , g' ] }

infixr 4 _∷_
_∷_ : Type → Cx → Cx
a ∷ X = hyp a ∨ X

∪/⊆ : ∀{X L R} → L ⊆ R → X ∨ L ⊆ X ∨ R
∪/⊆ = map∨ id
