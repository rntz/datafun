{-# OPTIONS --postfix-projections #-}
module ChangeSem.Types where

open import Cat
open import ChangeCat
open import Changes
open import Datafun
open import Decidability
open import Monads
open import Prelude
open import Prosets
open import TreeSet

 ---------- Denotations of types & tones ----------
Vars : Cx -> Set
Vars X = ∃ (λ a -> X a)
pattern Var {o} {a} p = (o , a) , p

type : Type -> Change
type bool = change-bool
type (set a p) = change-tree (change□ (type a))
type (□ a) = change□ (type a)
type (a ⊃ b) = type a ⇨ type b
type (a * b) = type a ∧ type b
type (a + b) = type a ∨ type b

⟦_⟧₁ : Tone × Type -> Change
⟦ mono , a ⟧₁ = type a
⟦ disc , a ⟧₁ = change□ (type a)

⟦_⟧ : Cx -> Change
⟦_⟧+ : Premise -> Change
⟦ X ⟧ = changeΠ (Vars X) (λ v -> ⟦ proj₁ v ⟧₁)
⟦ nil ⟧+    = ⊤-change
⟦ P , Q ⟧+  = ⟦ P ⟧+ ∧ ⟦ Q ⟧+
⟦ □ P ⟧+    = change□ ⟦ P ⟧+
⟦ X ▷ P ⟧+  = ⟦ X ⟧ ⇨ ⟦ P ⟧+
⟦ term a ⟧+ = type a

 -- What does it mean for a type's denotation to be a semilattice?
-- 1. 𝑶 is a semilattice
-- 2. 𝑫 is a semilattice
-- 3. δ(⊥) = ⊥
-- 4. δ(a ∨ b) = δa ∨ δb
record IsSL (A : Change) : Set where
  constructor IsSL:
  field {{𝑶-sums}} : Sums (𝑶 A)
  field 𝑫-sums : Sums (𝑫 A)

  private
    -- δ(a ∨ b) = δa ∨ δb
    vee-deriv : ((A ∧ A) ⇨ A) .𝑫 .Obj
    vee-deriv = π₂ • Sums.∨-functor 𝑫-sums

    -- δ(⊥) = ⊥
    eps-func : ⊤-cat ⇒ 𝑶 A
    eps-func = constant init
    eps-deriv : isos ⊤-cat ∧ ⊤-cat ⇒ 𝑫 A
    eps-deriv = constant (Sums.init 𝑫-sums)

  field eps-ok : IdPath (change→ ⊤-change A) eps-deriv eps-func
  field vee-ok : IdPath (change→ (A ∧ A) A) vee-deriv ∨-functor

  eps : ⊤-change ≤ A
  eps = cfun eps-func eps-deriv eps-ok
  vee : A ∧ A ≤ A
  vee = cfun ∨-functor vee-deriv vee-ok

open IsSL public

slSL : ∀ A S -> IsSL (change-SL A S)
slSL A S = IsSL: S (λ _ → ∨-idem , in₁) (λ { (p , q) → juggle∨≈ • ∨≈ p q })
  where private instance aa = A; ss = S; isosaa = isos A

sl× : ∀ {A B} (P : IsSL A) (Q : IsSL B) -> IsSL (A ∧ B)
sl× P Q .𝑶-sums = cat×-sums (𝑶-sums P) (𝑶-sums Q)
sl× P Q .𝑫-sums = cat×-sums (𝑫-sums P) (𝑫-sums Q)
sl× P Q .eps-ok = is-id ⟨ eps P , eps Q ⟩
sl× P Q .vee-ok = is-id (juggle∧ • ∧-map (vee P) (vee Q))

-- TODO
sl→ : ∀ A {B} (P : IsSL B) -> IsSL (change→ A B)
sl→ A P .𝑶-sums = proset→-sums (𝑶-sums P)
sl→ A P .𝑫-sums = proset→-sums (𝑫-sums P)
sl→ A P .eps-ok tt _ = eps-ok P tt
sl→ A P .vee-ok (df:f→g , dh:h→k) da:a→b = {!!}

 ---------- Semantics of type-classes ----------
class : Class -> Change -> Set
class (c , d) A = class c A × class d A
-- If I were to add equality testing as an expression, I'd need that equality
-- has a derivative, which shouldn't be hard to prove.
--
-- TODO FIXME: decidability also requires that we can compute zero-changes
class DEC A  = Decidable (Hom (𝑶 A))
class SL  A  = IsSL A
class FIN A  = TODO
class ACC A  = TODO
class ACC≤ A = TODO

is! : ∀{C a} -> Is C a -> class C (type a)
is! {c , d} (x , y) = is! x , is! y

is! {DEC} bool = bool≤?
is! {DEC} (set a p) = tree≤? _ (isos≤? (type a .𝑶) (is! p))
is! {DEC} (□ a p) = isos≤? (type a .𝑶) (is! p)
is! {DEC} (a * b) = decidable× (is! a) (is! b)
is! {DEC} (a + b) = decidable+ (is! a) (is! b)

is! {SL} bool = slSL it it
is! {SL} (set a) = slSL (trees _) (tree-sums _)
is! {SL} (a * b) = sl× (is! a) (is! b)
is! {SL} (a ⊃ b) = sl→ (type a) (is! b)

is! {FIN} a = TODO
is! {ACC} a = TODO
is! {ACC≤} a = TODO
