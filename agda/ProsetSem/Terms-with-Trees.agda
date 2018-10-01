-- Denotational semantics for terms in core Datafun.
module ProsetSem.Terms-with-Trees where

open import Booleans
open import Cat
open import Datafun-with-Trees
open import Monads
open import Prelude
open import ProsetSem.Types-with-Trees
open import TreeSet
open import Iso


---------- Lemmas for denotational semantics of terms ----------
module _ {i j} (C : Cat i j) where
  -- Obj-id≡ : Obj (Tone.at tone-id C) ≡ Obj C; Obj-id≡ = refl
  -- rel-id≡ : Hom (Tone.at tone-id C) ≡ Hom C; rel-id≡ = refl
  -- ident-id≡ : (λ {a} → ident (Tone.at tone-id C) {a}) ≡ ident C; ident-id≡ = refl
  -- compo-id≡ : (λ {a}{b}{c} → compo (Tone.at tone-id C) {a}{b}{c}) ≡ compo C; compo-id≡ = refl

  -- How do I actually do this?
  at-id≡ : Tone.at {i}{j} tone-id C ≡ C
  at-id≡ = TODO
  -- at-id≡ with Tone.at tone-id C | Obj-id≡ | rel-id≡ | ident-id≡ | compo-id≡
  -- ... | D@(Cat: _ _ _ _) | refl | refl | refl | refl = ?

-- Can I prove this using ⟦_⟧ being mapreduce? map context?
-- no, this fundamentally relies on wipe distributing over ∧/⊤.
wipe⇒iso : ∀ X → ⟦ wipe X ⟧ ⇒ iso ⟦ X ⟧
wipe⇒iso empty = fun (λ _ → TT , TT)
-- The leaf case is □A ≤ □(TA). This follows from □ ≤ □T, but only given □(TA) =
-- (□T)A. It's easier to just prove it directly.
wipe⇒iso (leaf (mono , a)) = fun id
wipe⇒iso (leaf (disc , a)) = fun ⟨ id , swap ⟩
wipe⇒iso (node X Y) = map∧ (wipe⇒iso X) (wipe⇒iso Y) ∙ ∧/iso

 ---------- Denotations of terms, premises, and term formers ----------
eval  : ∀{X P} -> X ⊢ P -> ⟦ X ⟧ ⇒ ⟦ P ⟧+
eval⊩ : ∀{P a} -> P ⊩ a -> ⟦ P ⟧+ ⇒ type a

eval tt = constant TT
eval (M , N) = ⟨ eval M , eval N ⟩
eval (bind M) = curry (swap ∙ eval M)
eval (box {X} M) = wipe⇒iso X ∙ map Iso (eval M)
eval (var mono p) = map context p ∙ fun id
eval (var disc p) = map context p ∙ extract Iso
eval (form ! M) = eval M ∙ eval⊩ form

eval⊩ (lam {a}) rewrite at-id≡ (type a) = id
eval⊩ app = apply
eval⊩ box = id
eval⊩ letbox = swapply
eval⊩ pair = id
eval⊩ (proj true)  = π₁
eval⊩ (proj false) = π₂
eval⊩ (bool b) = Fun: (λ _ -> b) (λ _ → id)
eval⊩ if = uncurry (antisym⇒ antisym:bool≤ (λ x → if x then π₁ else π₂))
eval⊩ (inj true)  = in₁
eval⊩ (inj false) = in₂
-- TODO: make more use of Lambdas.
eval⊩ case = cases π₁ (map∧ (π₂ ∙ π₁) (fun id) ∙ apply)
                      (map∧ (π₂ ∙ π₂) (fun id) ∙ apply)
  where open import Lambdas
-- eval⊩ case = distrib-∧/∨
--            ∙ [ map∧ (fun id) π₁ ∙ swapply
--              , map∧ (fun id) π₂ ∙ swapply ]
eval⊩ splitsum .ap x = x
eval⊩ splitsum .map (rel₁ x , rel₁ y) = rel₁ (x , y)
eval⊩ splitsum .map (rel₂ x , rel₂ y) = rel₂ (x , y)
eval⊩ (when {a} (_ , sl)) = When {{A = type a}} {{S = is! sl}} π₁ π₂
eval⊩ (single _) .ap = leaf
eval⊩ (single _) .map = leaf≤
-- TODO: Can I use mapreduce here?
eval⊩ (for-in _ (_ , b-sl)) =
  map∧ id Tree-map ∙ swapply ∙ tree-⋁ _ (is! b-sl)
eval⊩ (empty sl) = constant (Sums.⊥ (is! sl))
eval⊩ (lub-of {a} sl) = functor∨ {{C = type a}} {{S = is! sl}}
-- TODO
eval⊩ (fix is-fix) = {!!}
eval⊩ (fix≤ is-fix≤) = {!!}
