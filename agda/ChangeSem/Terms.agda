{-# OPTIONS --postfix-projections #-}
module ChangeSem.Terms where

open import Cat
open import ChangeCat
open import ChangeSem.Types
open import Changes
open import Datafun
open import Monads
open import Prelude
open import Prosets
open import TreeSet

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

lambda : ∀{c x} -> ⟦ hyp x ⟧ ⇨ c ≤ ⟦ x ⟧₁ ⇨ c
lambda {c} = precompose {c = c} singleton

-- this is wrong and should be destroyed
module _ {A : Change} (f g : ⊤-change ≤ A) (d : Hom! (⊤-change ⇨ A) (funct f) (funct g)) where
  private instance aaa = A; daa = 𝑫 A
  from-bool : change-bool ≤ A
  from-bool .funct = bool⇒ (Hom!.a≤b d _)
  from-bool .deriv .ap (x , dx) =
    (if x then g .deriv
    else if dx then Hom!.path d
    else f .deriv) .ap _
  from-bool .deriv .map ((false<true , ()) , _)
  from-bool .deriv .map ((, refl) , refl) = id
  from-bool .deriv .map {true , _} ((, refl) , _) = id
  -- gah! I need to know that (δf tt ≤ d)!
  from-bool .deriv .map {false , _} ((refl , refl) , false<true) = {!!}
  from-bool .is-id da:a→b = {!!}

-- from-bool : ∀{A a b ida idb da} -> Hom (𝑶 A) a b
--           -> Path A ida a a -> Path A idb b b -> Path A da a b
--           -> change-bool ≤ A
-- from-bool a≤b _ _ _ .funct = bool⇒ a≤b
-- from-bool {ida = ida} {idb = idb} {da} _ _ _ _ .deriv .ap (x , dx) =
--   if x then idb else if dx then da else ida
-- from-bool _ _ _ _ .deriv .map = {!!}
-- from-bool _ _ _ _ .is-id = {!!}

-- -- Need it to be a decidable semilattice!
-- from-bool : ∀{a} (S : IsSL a) -> change-bool ≤ a ⇨ a
-- from-bool sl .funct .ap false = constant (Sums.init (𝑶-sums sl))
-- from-bool sl .funct .ap true = {!!}
-- from-bool sl .funct .map = {!!}
-- from-bool sl .deriv = {!!}
-- from-bool sl .is-id = {!!}

-- from-bool : ∀{a} (S : Sums a) -> change-bool ∧ a ≤ a
-- from-bool S .ap (c , x) = if c then x else Sums.init S
-- from-bool {a} S .map {false , x} (bool-refl , x≤y) = ident a
-- from-bool S .map {true  , x} (bool-refl , x≤y) = x≤y
-- from-bool S .map {false , x} (false<true , x≤y) = Sums.init≤ S
