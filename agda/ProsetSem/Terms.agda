-- Denotational semantics for terms in core Datafun.
module ProsetSem.Terms where

open import Prelude
open import Cat
open import Prosets
open import Datafun
open import Monads
open import TreeSet
open import ProsetSem.Types


---------- Lemmas for denotational semantics of terms ----------
-- ⟦_⟧ is a functor, Cx^op -> Proset
comap⟦_⟧ : ∀{X Y} -> X ⊆ Y -> ⟦ Y ⟧ ⇒ ⟦ X ⟧
comap⟦ f ⟧ = comapΠ (∃-map f)

-- Managing environments.
lookup : ∀{X x} -> X x -> ⟦ X ⟧ ⇒ ⟦ x ⟧₁
lookup p = fun (λ f -> f (Var p))

-- isn't this just... pairing?
-- i.e. can't I express this without the semantic brackets?
cons : ∀{X Y} -> ⟦ X ⟧ ∧ ⟦ Y ⟧ ⇒ ⟦ Y ∪ X ⟧
ap cons (f , g) (, p) = [ g ∘ Var , f ∘ Var ] p
map cons (f , g) (, inj₁ p) = g (Var p)
map cons (f , g) (, inj₂ p) = f (Var p)

singleton : ∀{x} -> ⟦ x ⟧₁ ⇒ ⟦ hyp x ⟧
ap  singleton x   (Var Eq.refl) = x
map singleton x≤y (Var Eq.refl) = x≤y

wipe-sym : ∀{X x y} -> Hom ⟦ wipe X ⟧ x y -> Hom ⟦ wipe X ⟧ y x
wipe-sym f (Var {mono} ())
-- Argh!
wipe-sym f (Var {disc} p) = swap {{sets}} (f (Var {disc} p))

wipe⇒isos : ∀{X} -> ⟦ wipe X ⟧ ⇒ isos ⟦ wipe X ⟧
wipe⇒isos = fun ⟨ id , wipe-sym ⟩

lambda : ∀{x c} -> ⟦ hyp x ⟧ ⇨ c ⇒ ⟦ x ⟧₁ ⇨ c
lambda = precompose singleton

from-bool : ∀{a} (S : Sums a) -> bools ∧ a ⇒ a
from-bool S .ap (c , x) = if c then x else Sums.init S
from-bool {a} S .map {false , x} (bool-refl , x≤y) = ident a
from-bool S .map {true  , x} (bool-refl , x≤y) = x≤y
from-bool S .map {false , x} (false<true , x≤y) = Sums.init≤ S

 ---------- Denotations of terms, premises, and term formers ----------
eval  : ∀{X P} -> X ⊢ P -> ⟦ X ⟧ ⇒ ⟦ P ⟧+
eval⊩ : ∀{P a} -> P ⊩ a -> ⟦ P ⟧+ ⇒ type a

eval tt = fun (λ _ -> lift tt)
eval (M , N) = ⟨ eval M , eval N ⟩
eval (bind M) = curry (cons • eval M)
eval (box M) = comap⟦ extract Wipe ⟧ • wipe⇒isos • map Isos (eval M)
eval (var mono p) = lookup p
eval (var disc p) = lookup p • extract Isos
eval (form ! M) = eval M • eval⊩ form

eval⊩ lam = lambda
eval⊩ app = apply
eval⊩ box = id
eval⊩ letbox = map∧ id lambda • swap • apply
eval⊩ pair = id
eval⊩ (proj true)  = π₁
eval⊩ (proj false) = π₂
eval⊩ (bool b) = Fun: (λ _ -> b) (λ _ → bool-refl)
eval⊩ if = uncurry (antisym⇒ antisym:bool≤ (λ x -> if x then π₁ else π₂))
eval⊩ (inj true)  = in₁
eval⊩ (inj false) = in₂
eval⊩ case = distrib-∧/∨
           • [ map∧ singleton π₁ • swap • apply
             , map∧ singleton π₂ • swap • apply ]
eval⊩ splitsum .ap x = x
eval⊩ splitsum .map (rel₁ x , rel₁ y) = rel₁ (x , y)
eval⊩ splitsum .map (rel₂ x , rel₂ y) = rel₂ (x , y)
eval⊩ (when (_ , sl)) = from-bool (is! sl)
eval⊩ (single _) .ap = leaf
eval⊩ (single _) .map = leaf≤
eval⊩ (for-in _ (_ , b-sl)) =
  map∧ id (lambda • Tree-map)
  • swapply
  • tree-⋁ _ (is! b-sl)
eval⊩ (bottom sl) = constant (Sums.init (is! sl))
eval⊩ (join sl) = functor∨ {{S = is! sl}}
-- TODO
eval⊩ (fix is-fix) = {!!}
eval⊩ (fix≤ is-fix≤) = {!!}
