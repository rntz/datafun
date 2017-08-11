-- Denotational semantics for terms in core Datafun.
module TermSem where

open import Prelude
open import Cat
open import Prosets
open import Datafun
open import Monads
open import TreeSet
open import TypeSem


---------- Lemmas for denotational semantics of terms ----------
-- I've tried to put the most general lemmas at the beginning.
precompose : ∀{i j} {{C : Cat i j}} {{cc : CC C}} {a b c : Obj C}
           -> a ≤ b -> b ⇨ c ≤ a ⇨ c
precompose f = curry (∧-map id f • apply)

-- This actually holds in any bicartesian closed category, but we only need it for prosets.
distrib-∧/∨ : ∀{a b c} -> (a ∨ b) ∧ c ⇒ (a ∧ c) ∨ (b ∧ c)
-- distrib-∧/∨ : ∀{i j} {{C : Cat i j}} {{cc : CC C}} {{S : Sums C}}
--               {a b c : Obj C} -> (a ∨ b) ∧ c ≤ (a ∧ c) ∨ (b ∧ c)
distrib-∧/∨ = ∧-map [ curry in₁ , curry in₂ ] id • apply

-- Lifts an arbitrary function over an antisymmetric domain into a monotone map
-- over its discrete preorder.
antisym-lift : ∀{A B} -> Antisymmetric _≡_ (Hom A) -> (Obj A -> Obj B) -> isos A ⇒ B
antisym-lift {A}{B} antisym f = Fun: f helper
  where helper : ∀{x y} -> Hom (isos A) x y -> Hom B (f x) (f y)
        helper (x , y) with antisym x y
        ... | refl = ident B

instance
  -- If (f : a -> b) is monotone, then (f : isos a -> isos b) is also monotone.
  Isos : prosets ≤ prosets
  ap Isos = isos
  map Isos f = fun (λ { (x , y) -> map f x , map f y })

  -- This comonad factors into an adjunction to groupoids, I believe.
  Isos-comonad : Comonad Isos
  Comonad.dup Isos-comonad = fun ⟨ id , swap ⟩
  Comonad.extract Isos-comonad = fun proj₁

-- ⟦_⟧ is a functor, Cx^op -> Proset
-- TODO: better name
corename : ∀{X Y} -> X ⊆ Y -> ⟦ Y ⟧ ⇒ ⟦ X ⟧
corename f = fun (λ { γ≤σ (Var p) -> γ≤σ (Var (f _ p)) })

-- Managing environments.
lookup : ∀{X x} -> X x -> ⟦ X ⟧ ⇒ ⟦ x ⟧₁
lookup p = fun (λ f -> f (Var p))

cons : ∀{X Y} -> ⟦ X ⟧ ∧ ⟦ Y ⟧ ⇒ ⟦ Y ∪ X ⟧
ap cons (f , g) (Var p) = [ g ∘ Var , f ∘ Var ] p
map cons (f , g) (_ , inj₁ p) = g (Var p)
map cons (f , g) (_ , inj₂ p) = f (Var p)

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

eval tt = fun (λ _ -> tt)
eval (M , N) = ⟨ eval M , eval N ⟩
eval (bind M) = curry (cons • eval M)
eval (box M) = corename (extract Wipe) • wipe⇒isos • map Isos (eval M)
eval (var mono p) = lookup p
eval (var disc p) = lookup p • extract Isos
eval (form ! M) = eval M • eval⊩ form

eval⊩ lam = lambda
eval⊩ app = apply
eval⊩ box = id
eval⊩ letbox = ∧-map id lambda • swap • apply
eval⊩ pair = id
eval⊩ (proj true)  = π₁
eval⊩ (proj false) = π₂
eval⊩ (bool b) = Fun: (λ _ -> b) (λ _ → bool-refl)
eval⊩ if = uncurry (antisym-lift antisym:bool≤ (λ x -> if x then π₁ else π₂))
eval⊩ (inj true)  = in₁
eval⊩ (inj false) = in₂
eval⊩ case = distrib-∧/∨
           • [ ∧-map singleton π₁ • swap • apply
             , ∧-map singleton π₂ • swap • apply ]
eval⊩ splitsum .ap x = x
eval⊩ splitsum .map (rel₁ x , rel₁ y) = rel₁ (x , y)
eval⊩ splitsum .map (rel₂ x , rel₂ y) = rel₂ (x , y)
eval⊩ (when (dec , sl)) = from-bool (is! sl)
eval⊩ (single dec) .ap = leaf
eval⊩ (single {a} dec) .map = leaf≤
-- TODO
eval⊩ (for-in a-dec (b-dec , b-sl)) = {!!}
eval⊩ (bottom sl) = const-fun (Sums.init (is! sl))
eval⊩ (join sl) = Sums.∨-functor (is! sl)
-- TODO
eval⊩ (fix is-fix) = {!!}
eval⊩ (fix≤ is-fix≤) = {!!}
