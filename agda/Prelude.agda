module Prelude where

open import Level renaming (zero to lzero; suc to lsuc) public

import Relation.Binary.PropositionalEquality as Eq
open Eq public using (_≡_)

open import Data.Bool using (Bool; true; false; not; if_then_else_) public
open import Data.Empty using (⊥; ⊥-elim) public
open import Data.Product using (Σ; proj₁; proj₂; Σ-syntax; ∃; ∄; _×_; _,_; ,_) public
open import Data.Sum using (_⊎_; inj₁; inj₂) public
open import Data.Unit using (⊤; tt) public
open import Function using (id; _∘_) public

