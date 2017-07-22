module Prelude where

-- STANDARD LIBRARY STUFF
module Level where open import Level public

open import Data.Bool using (Bool; true; false; not; if_then_else_) public
open import Data.Empty using (⊥; ⊥-elim) public
open import Data.Maybe using (Maybe; just; nothing; maybe) public
open import Data.Nat using (ℕ; zero; suc) public
open import Data.Product using (Σ; proj₁; proj₂; Σ-syntax; ∃; ∄; _×_; _,_; ,_) public
open import Data.Sum using (_⊎_; inj₁; inj₂) public
open import Data.Unit using (⊤; tt) public
open import Function using (_∘_; _on_) public
open import Relation.Nullary using (¬_; Dec; yes; no) public

module Eq where
  open import Relation.Binary.PropositionalEquality public

open Eq using (_≡_) public

-- MY STUFF
open import Cat public
open import Cartesian public

-- The agda tutorial calls this `it`.
auto : ∀{i}{A : Set i} {{x : A}} -> A
auto {{x}} = x
