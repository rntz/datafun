-- Denotational semantics for terms in core Datafun.
module ProsetSem.Terms-with-Trees where

open import Booleans
open import Cat
open import Datafun-with-Trees
open import Monads
open import Prelude
open import ProsetSem.Types-with-Trees
open import TreeSet


---------- Lemmas for denotational semantics of terms ----------
-- ⟦_⟧ is a functor, Cx^op -> Proset
comap⟦_⟧ : ∀{X Y} -> X ≤ Y -> ⟦ Y ⟧ ⇒ ⟦ X ⟧
comap⟦ empty≤ ⟧ = ≤⊤
-- uh-oh. I think I have failed to apply an "op" somewhere!
comap⟦ leaf≤ h ⟧ = {!!}
comap⟦ node≤ l r ⟧ = ⟨ comap⟦ l ⟧ , comap⟦ r ⟧ ⟩
comap⟦ split₁ x ⟧ = π₁ ∙ comap⟦ x ⟧
comap⟦ split₂ y ⟧ = π₂ ∙ comap⟦ y ⟧

-- Managing environments.
lookup : ∀{X x} -> x ∈ X -> ⟦ X ⟧ ⇒ ⟦ x ⟧₁
lookup = comap⟦_⟧

cons : ∀{X Y} -> ⟦ X ⟧ ∧ ⟦ Y ⟧ ⇒ ⟦ Y ∨ X ⟧
cons = swap

-- Singleton is just the identity function.

-- wipe-sym : ∀{X x y} -> Hom ⟦ wipe X ⟧ x y -> Hom ⟦ wipe X ⟧ y x
-- wipe-sym f (Var {mono} ())
-- -- Argh!
-- wipe-sym f (Var {disc} p) = swap {{sets}} (f (Var {disc} p))

-- wipe⇒iso : ∀{X} -> ⟦ wipe X ⟧ ⇒ iso ⟦ wipe X ⟧
-- wipe⇒iso = fun ⟨ id , wipe-sym ⟩

-- lambda : ∀{x c} -> ⟦ hyp x ⟧ ⇨ c ⇒ ⟦ x ⟧₁ ⇨ c
-- lambda = precompose singleton

-- from-bool : ∀{a} (S : Sums a) -> bools ∧ a ⇒ a
-- from-bool S .ap (c , x) = if c then x else Sums.⊥ S
-- from-bool S .map (f≤* , x≤y) = Sums.⊥≤ S
-- from-bool S .map (t≤t , x≤y) = x≤y

--  ---------- Denotations of terms, premises, and term formers ----------
-- eval  : ∀{X P} -> X ⊢ P -> ⟦ X ⟧ ⇒ ⟦ P ⟧+
-- eval⊩ : ∀{P a} -> P ⊩ a -> ⟦ P ⟧+ ⇒ type a

-- eval tt = constant TT
-- eval (M , N) = ⟨ eval M , eval N ⟩
-- eval (bind M) = curry (cons ∙ eval M)
-- eval (box M) = comap⟦ extract Wipe ⟧ ∙ wipe⇒iso ∙ map Iso (eval M)
-- eval (var mono p) = lookup p
-- eval (var disc p) = lookup p ∙ extract Iso
-- eval (form ! M) = eval M ∙ eval⊩ form

-- eval⊩ lam = lambda
-- eval⊩ app = apply
-- eval⊩ box = id
-- eval⊩ letbox = map∧ id lambda ∙ swapply
-- eval⊩ pair = id
-- eval⊩ (proj true)  = π₁
-- eval⊩ (proj false) = π₂
-- eval⊩ (bool b) = Fun: (λ _ -> b) (λ _ → id)
-- eval⊩ if = uncurry (antisym⇒ antisym:bool≤ (λ x → if x then π₁ else π₂))
-- eval⊩ (inj true)  = in₁
-- eval⊩ (inj false) = in₂
-- -- TODO: make more use of Lambdas.
-- eval⊩ case = cases π₁ (map∧ (π₂ ∙ π₁) singleton ∙ apply)
--                       (map∧ (π₂ ∙ π₂) singleton ∙ apply)
--   where open import Lambdas
-- -- eval⊩ case = distrib-∧/∨
-- --            ∙ [ map∧ singleton π₁ ∙ swapply
-- --              , map∧ singleton π₂ ∙ swapply ]
-- eval⊩ splitsum .ap x = x
-- eval⊩ splitsum .map (rel₁ x , rel₁ y) = rel₁ (x , y)
-- eval⊩ splitsum .map (rel₂ x , rel₂ y) = rel₂ (x , y)
-- eval⊩ (when (_ , sl)) = from-bool (is! sl)
-- eval⊩ (single _) .ap = leaf
-- eval⊩ (single _) .map = leaf≤
-- eval⊩ (for-in _ (_ , b-sl)) =
--   map∧ id (lambda ∙ Tree-map)
--   ∙ swapply
--   ∙ tree-⋁ _ (is! b-sl)
-- eval⊩ (empty sl) = constant (Sums.⊥ (is! sl))
-- eval⊩ (join sl) = functor∨ {{S = is! sl}}
-- -- TODO
-- eval⊩ (fix is-fix) = {!!}
-- eval⊩ (fix≤ is-fix≤) = {!!}