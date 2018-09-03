{-# OPTIONS --postfix-projections #-}
module ChangeSem.Terms where

open import Cat
open import ChangeCat
open import ChangeSem.Types
open import ChangeSem.Lemmas
open import Changes
open import Datafun
open import Monads
open import Prelude
open import Prosets
open import TreeSet

-- whenn = (x,y) ↦ when x then y
-- δ(when x then y) = if x then δy else when δx then (y ∨ δy)
whenn : ∀{A} -> class (DEC , SL) A -> (change-bool ∧ A) ≤ A
whenn (dec , sl) .funct = from-bool
whenn {A} (dec , sl) .deriv =
  map∧ isos/∧ id • juggle∧ • assoc∧r
  • if⇒ ⟨ π₂ • π₂ , map∧ id (plus dec • from-zero dec sl)
                  • from-bool {{A = 𝑫 A}} {{S = 𝑫-sums sl}} ⟩ -- argh!
 -- Path A (ap (whenn (dec , sl) .deriv) (a , da))
 --        (ap (whenn (dec , sl) .funct) a)
 --        (ap (whenn (dec , sl) .funct) b)

whenn (dec , sl) .is-id {false , dx} {false , x} {false , y} ((f≤* , f≤*) , r) = eps-ok sl TT
-- WTF: Path A (change (⊥ , (x + dx))) ⊥ y
-- aha, we need to show y = x + dx.
-- ah crap, don't we need to compose paths?! no, we just need
-- if (Path da a b) and (b ≈ c) then (Path da a c).
whenn (dec , sl) .is-id = {!!}

-- whenn (dec , sl) .is-id {true , dx} {false , x} {true , y} ((t≤t , t≤t) , r) = {!!}
-- whenn (dec , sl) .is-id {_ , dx} {true , x} {.true , y} ((t≤t , t≤t) , r) = r
-- whenn (dec , sl) .is-id {true ,  dx} {false , x} {false , y} ((() , f≤*) , r)
-- whenn (dec , sl) .is-id {false , dx} {false , x} {true ,  y} ((f≤* , ()) , r)


-- Semantics of terms
eval  : ∀{X P} -> X ⊢ P -> ⟦ X ⟧ ≤ ⟦ P ⟧+
eval⊩ : ∀{P a} -> P ⊩ a -> ⟦ P ⟧+ ≤ type a

eval tt = const-cfun TT TT TT
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
eval⊩ (empty sl) = eps (is! sl)
eval⊩ (join sl) = vee (is! sl)
eval⊩ (fix is-fix) = {!!}
eval⊩ (fix≤ is-fix≤) = {!!}
