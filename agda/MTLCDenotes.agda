module MTLCDenotes where

open import Data.Sum using (inj₁; inj₂)

open import Prelude
open import MTLC
open import Monads
open import Preorders
open import ProsetCat


---------- Denotations of terms, premises, and term formers ----------
eval  : ∀{X P} -> X ⊢ P -> ⟦ X ⟧ ⇒ ⟦ P ⟧+
eval⊩ : ∀{P a} -> P ⊩ a -> ⟦ P ⟧+ ⇒ type a

eval tt = functor (λ _ -> tt)
eval (M , N) = ⟨ eval M , eval N ⟩
eval (bind M) = curry (cons • eval M)
eval (box M) = corename extract • wipe⇒■ • map (eval M)
eval (var mono p) = lookup p
eval (var disc p) = lookup p • extract
eval (form ! M) = eval M • eval⊩ form

eval⊩ lam = lambda
eval⊩ app = apply
eval⊩ box = id
eval⊩ letbox = ×-map id lambda • swap • apply
eval⊩ pair = id
eval⊩ (proj true)  = π₁
eval⊩ (proj false) = π₂
eval⊩ (bool b) = Functor: (λ _ -> b) (λ _ → bool-refl)
eval⊩ if = uncurry (antisym-lift antisym:bool≤ (λ x -> if x then π₁ else π₂))
eval⊩ (inj true)  = in₁
eval⊩ (inj false) = in₂
eval⊩ case = distrib-×/⊎
           • [ ×-map singleton π₁ • swap • apply
             , ×-map singleton π₂ • swap • apply ]
ap (eval⊩ splitsum) x = x
cov (eval⊩ splitsum) (rel₁ x , rel₁ y) = rel₁ (x , y)
cov (eval⊩ splitsum) (rel₂ x , rel₂ y) = rel₂ (x , y)
