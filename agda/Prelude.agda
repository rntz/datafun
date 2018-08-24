module Prelude where

-- STANDARD LIBRARY STUFF
open import Level public

open import Data.Bool public using (Bool; true; false; not; if_then_else_)
open import Data.Empty public using () renaming (⊥ to ∅; ⊥-elim to ∅-elim)
open import Data.Maybe public using (Maybe; just; nothing; maybe)
open import Data.Nat public using (ℕ)
open import Data.Product public using (Σ; proj₁; proj₂; Σ-syntax; ∃; ∄; _×_; _,_)
open import Data.Sum public using (_⊎_; inj₁; inj₂)
open import Data.Unit public using (tt) renaming (⊤ to Unit)
open import Function public using (_∘_; _on_; const)
open import Relation.Nullary public using (¬_; Dec; yes; no)
open import Relation.Binary public
  using (Rel; Reflexive; Transitive; Symmetric; Antisymmetric; Decidable; _=[_]⇒_)

module Eq where open import Relation.Binary.PropositionalEquality public
open Eq public using (_≡_; refl)


-- MY STUFF
BinOp : ∀{i} -> Set i -> Set i
BinOp A = A -> A -> A

Function : ∀{i j} -> Set i -> Set j -> Set _
Function A B = A -> B

coerce : ∀{i}{A B : Set i} -> A ≡ B -> A -> B
coerce = Eq.subst (λ x → x)

ignore : ∀{i j} {A : Set i} {B : Set j} → A → B → B
ignore = λ x y → y

-- A better version of Data.Product.,_
infixr 4 ,_
pattern ,_ x = _ , x

it : ∀{i}{A : Set i} {{x : A}} -> A
it {{x}} = x

∃-map : ∀{i j k A P Q} -> ((x : A) -> P x -> Q x) -> ∃ {i}{j} P -> ∃ {i}{k} Q
∃-map f (, p) = , f _ p

-- TODO: remove this once I think I've proved everything
postulate TODO : ∀{i}{A : Set i} -> A
