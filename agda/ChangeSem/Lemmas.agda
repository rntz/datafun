-- Lemmas used by term denotations.
module ChangeSem.Lemmas where

open import Cat
open import ChangeCat
open import ChangeSem.Types
open import Changes
open import Datafun
open import Monads
open import Prelude
open import Iso
open import Booleans

 -- Lemmas for semantics of terms
-- ⟦_⟧ is a functor, Cx^op -> Change
comap⟦_⟧ : ∀{X Y} -> X ⊆ Y -> ⟦ Y ⟧ ≤ ⟦ X ⟧
comap⟦ f ⟧ = prefixΠ {P = ⟦_⟧v} (∃-map f)

-- Managing environments.
lookup : ∀{X x} -> X x -> ⟦ X ⟧ ≤ ⟦ x ⟧₁
lookup p = Πe (Var p)

cons : ∀{X Y} -> ⟦ X ⟧ ∧ ⟦ Y ⟧ ≤ ⟦ Y ∪ X ⟧
cons = Πi {P = ⟦_⟧v} λ { (, inj₁ x) → π₂ • lookup x ; (, inj₂ y) → π₁ • lookup y }

singleton : ∀{x} -> ⟦ x ⟧₁ ≤ ⟦ hyp x ⟧
singleton = Πi duh
 where duh : ∀{x} (v : Vars (hyp x)) -> ⟦ x ⟧₁ ≤ ⟦ v ⟧v
       duh (Var refl) = id

-- Lemmas for wipe≤□.
Π/□ : ∀{A} P -> Π A (λ a -> change□ (P a)) ≤ change□ (Π A P)
-- I find this slightly incomprehensible myself.
Π/□ _ = cfun (fun Π/∧) (π₂ • fun Π/∧) (Π/∧ • map∧ id Π/∧)

Π≤□ : ∀{A P} -> (∀ a -> P a ≤ change□ (P a)) -> Π A P ≤ change□ (Π A P)
Π≤□ {P = P} F = suffixΠ F • Π/□ P

wipevar : ∀{X} (v : Vars (wipe X)) -> ⟦ v ⟧v ≤ change□ ⟦ v ⟧v
wipevar (Var {mono} ())
wipevar (Var {disc} p) = dup Change□

wipe≤□ : ∀{X} -> ⟦ wipe X ⟧ ≤ change□ ⟦ wipe X ⟧
wipe≤□ = Π≤□ wipevar

lambda : ∀{x} c -> ⟦ hyp x ⟧ ⇨ type c ≤ ⟦ x ⟧₁ ⇨ type c
lambda c = precompose {c = type c} singleton


-- TODO: clean up / refactor / inline
boolπ : ∀{A} -> iso bools ⇒ ((A ∧ A) ⇨ A)
boolπ = antisym⇒ antisym:bool≤ (λ x → if x then π₁ else π₂)

if⇒ : ∀{Γ a} -> (N : Γ ≤ a ∧ a) -> iso bools ∧ Γ ⇒ a
if⇒ N = map∧ id N • uncurry boolπ

from-bool : ∀{{A}} {{S : Sums A}} -> bools ∧ A ⇒ A
from-bool .ap (c , x) = if c then x else ⊥
from-bool .map (f≤* , x≤y) = ⊥≤
from-bool .map (t≤t , x≤y) = x≤y

