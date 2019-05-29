{-# OPTIONS --postfix-projections #-}
module ChangeSem.Terms3 where

open import Cat
open import ChangeCat3
open import ChangeSem.Types3
open import Changes3
open import Datafun
open import Monads
open import Prelude
open import TreeSet

 -- Lemmas for semantics of terms
-- ⟦_⟧ is a functor, Cx^op -> Change
comap⟦_⟧ : ∀{X Y} -> X ⊆ Y -> ⟦ Y ⟧ ≤ ⟦ X ⟧
comap⟦ f ⟧ = prefixΠ {P = ⟦_⟧v} (∃-map f)

-- Managing environments.
lookup : ∀{X x} -> X x -> ⟦ X ⟧ ≤ ⟦ x ⟧₁
lookup p = Πe {P = ⟦_⟧v} (Var p)

cons : ∀{X Y} -> ⟦ X ⟧ ∧ ⟦ Y ⟧ ≤ ⟦ Y ∪ X ⟧
cons = Πi {P = ⟦_⟧v} λ { (, inj₁ x) → π₂ ∙ lookup x ; (, inj₂ y) → π₁ ∙ lookup y }

--singleton : ∀{o a} -> ⟦ o , a ⟧₁ ≤ ⟦ hyp (o , a) ⟧
singleton : ∀{x} -> ⟦ x ⟧₁ ≤ ⟦ hyp x ⟧
singleton = Πi duh
 where duh : ∀{x} (v : Vars (hyp x)) -> ⟦ x ⟧₁ ≤ ⟦ v ⟧v
       duh (Var refl) = id

-- god, what an ugly brute-force of a proof. TODO: revise.
wipe-sym : ∀{X} -> Symmetric (changeΠ (Vars (wipe X)) ⟦_⟧v .𝑶 .Hom)
wipe-sym f (Var {mono} ())
wipe-sym f (Var {disc} p) = swap {{sets}} (f (Var {disc} p))

wipe-dsym : ∀{X} -> Symmetric (Hom (𝑫 ⟦ wipe X ⟧))
wipe-dsym f (Var {mono} ())
wipe-dsym f (Var {disc} p) = swap {{sets}} (f (Var {disc} p))

wipe⇒□ : ∀{X} -> ⟦ wipe X ⟧ ≤ change□ ⟦ wipe X ⟧
wipe⇒□ .funct = fun ⟨ id , wipe-sym ⟩
wipe⇒□ .deriv = π₂ ∙ fun (⟨ id , wipe-dsym ⟩)
wipe⇒□ .is-id = id
-- end horrible proof

lambda : ∀{c x} -> ⟦ hyp x ⟧ ⇨ c ≤ ⟦ x ⟧₁ ⇨ c
lambda {c} = precompose {c = c} singleton

module _ {A : Change} (f g : ⊤ ≤ A) (d : Hom! (⊤ ⇨ A) (funct f) (funct g)) where
  private instance aaa = A; daa = 𝑫 A
  from-bool : change-bool ≤ A
  from-bool .funct = bool⇒ (Hom!.a≤b d _)
  from-bool .deriv .ap (x , dx) =
    (if x then g .deriv
    else if dx then Hom!.path d
    else f .deriv) .ap _
  from-bool .deriv .map (Var {f≤*} {f≤*} f≤*) = {!!}
  from-bool .deriv .map (Var {f≤*} {f≤*} t≤t) = id
  from-bool .deriv .map (Var {t≤t} {t≤t} _) = id
  -- from-bool .deriv .map ((false<true , ()) , _)
  -- from-bool .deriv .map ((, refl) , refl) = id
  -- from-bool .deriv .map {true , _} ((, refl) , _) = id
  -- -- gah! I need to know that (δf tt ≤ d)!
  -- from-bool .deriv .map {false , _} ((refl , refl) , false<true) = {!!}
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
