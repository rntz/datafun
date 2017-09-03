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

lambda : ∀{x} c -> ⟦ hyp x ⟧ ⇨ type c ≤ ⟦ x ⟧₁ ⇨ type c
lambda c = precompose {c = type c} singleton


-- -- this is wrong and should be destroyed
-- module _ {A : Change} (f g : ⊤-change ≤ A) (d : Hom! (⊤-change ⇨ A) (funct f) (funct g)) where
--   private instance aaa = A; daa = 𝑫 A
--   from-bool : change-bool ≤ A
--   from-bool .funct = bool⇒ (Hom!.a≤b d _)
--   from-bool .deriv .ap (x , dx) =
--     (if x then g .deriv
--     else if dx then Hom!.path d
--     else f .deriv) .ap _
--   from-bool .deriv .map ((false<true , ()) , _)
--   from-bool .deriv .map ((, refl) , refl) = id
--   from-bool .deriv .map {true , _} ((, refl) , _) = id
--   -- gah! I need to know that (δf tt ≤ d)!
--   from-bool .deriv .map {false , _} ((refl , refl) , false<true) = {!!}
--   from-bool .is-id da:a→b = {!!}

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


-- what
boolπ : ∀{A} -> isos bools ⇒ ((A ∧ A) ⇨ A)
boolπ = antisym⇒ antisym:bool≤ (λ x → if x then π₁ else π₂)

from-bool : ∀{{A}} {{S : Sums A}} -> bools ∧ A ⇒ A
from-bool .ap (c , x) = if c then x else init
from-bool .map {false , _} (_ , _) = init≤
from-bool .map {true  , x} (refl , x≤y) = x≤y
-- from-bool .map {false , x} (refl , x≤y) = id
-- from-bool .map {false , x} (false<true , x≤y) = init≤

-- whenn = (x,y) ↦ when x then y
-- δ(when x then y) = if x then δy else when δx then (y ∨ δy)
whenn : ∀{A} -> class (DEC , SL) A -> (change-bool ∧ A) ≤ A
whenn (dec , sl) .funct = from-bool
whenn (dec , sl) .deriv = map∧ isos/∧ id • juggle∧ • uncurry {!plus dec!}

-- whenn {A} (dec , sl) .deriv .ap ((false , v) , false , dv) = 𝑫-sums sl .Sums.init
-- -- need A = ΔA. argh.
-- whenn (dec , sl) .deriv .ap ((false , v) , true , dv) = 𝑫-sums sl .Sums._∨_ {!v!} dv
-- whenn (dec , sl) .deriv .ap ((true , v) , _ , dv) = dv
-- -- probably need something to do with antisymmetry or here.
-- whenn (dec , sl) .deriv .map {(a , x) , (b , y)} {(a' , x') , b' , y'} (((a≤a' , x≤x') , a'≤a , x'≤x) , b≤b' , y≤y') = {!!}

whenn (dec , sl) .is-id = {!!}


-- Semantics of terms
eval  : ∀{X P} -> X ⊢ P -> ⟦ X ⟧ ≤ ⟦ P ⟧+
eval⊩ : ∀{P a} -> P ⊩ a -> ⟦ P ⟧+ ≤ type a

eval tt = const-cfun TT TT tt
eval (M , N) = ⟨ eval M , eval N ⟩
eval (bind M) = curry (cons • eval M)
-- what is the type of comap⟦ extract Wipe ⟧?
-- is this the only place I use comap⟦_⟧?
-- Can I specialize it for simpler code?
eval (box M) = comap⟦ extract Wipe ⟧ • wipe≤□ • map Change□ (eval M)
eval (form ! M) = eval M • eval⊩ form
eval (var mono p) = lookup p
eval (var disc p) = lookup p • extract Change□

eval⊩ (lam {a}{b}) = lambda b
eval⊩ app = apply
eval⊩ box = id
eval⊩ (letbox {a}{b}) = map∧ id (lambda b) • swapply
eval⊩ pair = id
eval⊩ (proj true) = π₁
eval⊩ (proj false) = π₂
eval⊩ (inj {a}{b} true) = in₁ {b = type b}
eval⊩ (inj false) = in₂
eval⊩ (case {a}{b}{c})
      = distrib-∧/∨ {a = type a} {b = type b}
           • [ map∧ singleton π₁ • swapply
             , map∧ singleton (π₂ {a = ⟦ _ ⟧ ⇨ type c}) • swapply ]
eval⊩ splitsum .funct = isos/∨
eval⊩ splitsum .deriv = π₂ • isos/∨
eval⊩ splitsum .is-id (rel₁ x , rel₁ y , rel₁ z) = rel₁ (x , y , z)
eval⊩ splitsum .is-id (rel₂ x , rel₂ y , rel₂ z) = rel₂ (x , y , z)
eval⊩ (bool x) = const-cfun x false a∨⊥≈a
eval⊩ if = uncurry (antisym□≤ antisym:bool≤ (λ x → if x then π₁ else π₂))
eval⊩ (when x) = whenn (is! x)
eval⊩ (single p) .funct = Fun: leaf leaf≤
eval⊩ (single p) .deriv = constant empty
-- this is the functoriality of (- ∨ ⊥)! I think.
-- this pattern comes up somewhere else, but I can't remember where...
-- TODO: simplify
eval⊩ (single {a} p) .is-id (da:a→b , a≈b) = [ leaf≤ a≈b , empty≤ ]
                                             , leaf≤ (swap {{sets}} a≈b) • in₁
  where instance x = trees (isos (type a .𝑶))
eval⊩ (for-in p q) = {!!}
eval⊩ (bottom sl) = eps (is! sl)
eval⊩ (join sl) = vee (is! sl)
eval⊩ (fix is-fix) = {!!}
eval⊩ (fix≤ is-fix≤) = {!!}
