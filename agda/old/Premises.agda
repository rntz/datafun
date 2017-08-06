module Premises where

open import Prelude


---------- Types and contexts ----------
infixr 6 _⊃_
data Type : Set where
  _⊃_ _*_ : (a b : Type) -> Type
  base : Type

open import Contexts (Type)


---------- "ABTs" ----------
infix 3 _⊩_ _⊢_ _!_
infixr 4 _∧_ _,_
infix  5 _▷_

-- TODO: find a better name.
data Premise : Set1 where
  nil : Premise
  _∧_ : (P Q : Premise) -> Premise
  -- maybe this could be: _▷_ : (P Q : Premise) -> Premise  ???
  _▷_ : (X : Cx) (P : Premise) -> Premise
  term : (a : Type) -> Premise

-- Rules of inference
data _⊩_ : Premise -> Premise -> Set1 where
  -- functions
  lam  : ∀{a b} -> hyp a ▷ term b ⊩ term (a ⊃ b)
  app  : ∀{a b} -> term (a ⊃ b) ∧ term a ⊩ term b
  -- products
  pair : ∀{a b} -> term a ∧ term b ⊩ term (a * b)
  unpair : ∀{a b} -> term (a * b) ⊩ term a ∧ term b
  -- wut
  proj : ∀{P Q} d -> P ∧ Q ⊩ (if d then P else Q)

-- Proofs
data _⊢_ (X : Cx) : Premise -> Set1 where
  tt   : X ⊢ nil
  _,_  : ∀{P Q} (M : X ⊢ P) (N : X ⊢ Q) -> X ⊢ P ∧ Q
  bind : ∀{P Y} (M : Y ∪ X ⊢ P) -> X ⊢ Y ▷ P
  -- is this excessively general?
  _!_ : ∀{P Q} (form : P ⊩ Q) (args : X ⊢ P) -> X ⊢ Q
  -- terms
  -- _!_ : ∀{P a} (form : P ⊩ term a) (args : X ⊢ P) -> X ⊢ term a
  var  : ∀{a} (p : X a) -> X ⊢ term a


-- Applying context renamings to proofs
rename : ∀{X Y P} -> X ⊆ Y -> X ⊢ P -> Y ⊢ P
rename f tt = tt
rename f (M , N) = rename f M , rename f N
rename f (bind M) = bind (rename (∪/⊆ f) M)
rename f (form ! M) = form ! rename f M
rename f (var p) = var (f _ p)
