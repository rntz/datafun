module Examples.MTLCSem where

open import Prelude
open import Cat
open import Examples.MTLC
open import Monads
open import Booleans
open import Iso


---------- Denotations of types & tones ----------
Vars : Cx -> Set
Vars X = ∃ (λ a -> X a)
pattern Var {o} {a} p = (o , a) , p

type : Type -> Proset
type (a ⊃ b) = type a ⇨ type b
type (a * b) = type a ∧ type b
type (a + b) = type a ∨ type b
type bool = bools
type (□ a) = iso (type a)

⟦_⟧₁ : Mode × Type -> Proset
⟦ mono , a ⟧₁ = type a
⟦ disc , a ⟧₁ = iso (type a)

⟦_⟧ : Cx -> Proset
⟦ X ⟧ = Π (Vars X) (λ v -> ⟦ proj₁ v ⟧₁)

⟦_⟧+ : Premise -> Proset
⟦ nil ⟧+    = ⊤-cat
⟦ P , Q ⟧+  = cat× ⟦ P ⟧+ ⟦ Q ⟧+
⟦ □ P ⟧+    = iso ⟦ P ⟧+
⟦ X ▷ P ⟧+  = ⟦ X ⟧ ⇨ ⟦ P ⟧+
⟦ term a ⟧+ = type a


---------- Lemmas for denotational semantics of terms ----------
-- ⟦_⟧ is a functor, Cx^op -> Proset
comap⟦_⟧ : ∀{X Y} -> X ⊆ Y -> ⟦ Y ⟧ ⇒ ⟦ X ⟧
comap⟦ f ⟧ = prefixΠ (∃-map f)

-- Managing environments.
lookup : ∀{X x} -> X x -> ⟦ X ⟧ ⇒ ⟦ x ⟧₁
lookup p = Πe (Var p)

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
wipe-sym f (Var {disc} p) = swap {{sets _}} (f (Var {disc} p))

wipe⇒iso : ∀{X} -> ⟦ wipe X ⟧ ⇒ iso ⟦ wipe X ⟧
wipe⇒iso = fun ⟨ id , wipe-sym ⟩

lambda : ∀{x c} -> ⟦ hyp x ⟧ ⇨ c ⇒ ⟦ x ⟧₁ ⇨ c
lambda = precompose singleton


---------- Denotations of terms, premises, and term formers ----------
eval  : ∀{X P} -> X ⊢ P -> ⟦ X ⟧ ⇒ ⟦ P ⟧+
eval⊩ : ∀{P a} -> P ⊩ a -> ⟦ P ⟧+ ⇒ type a

eval tt = constant TT
eval (M , N) = ⟨ eval M , eval N ⟩
eval (bind M) = curry (cons ∙ eval M)
eval (box M) = comap⟦ extract Wipe ⟧ ∙ wipe⇒iso ∙ map Iso (eval M)
eval (var mono p) = lookup p
eval (var disc p) = lookup p ∙ extract Iso
eval (form ! M) = eval M ∙ eval⊩ form

eval⊩ lam = lambda
eval⊩ app = apply
eval⊩ box = id
eval⊩ letbox = map∧ id lambda ∙ swap ∙ apply
eval⊩ pair = id
eval⊩ (proj true)  = π₁
eval⊩ (proj false) = π₂
eval⊩ (bool b) = Fun: (λ _ -> b) (λ _ → id)
eval⊩ if = uncurry (antisym⇒ antisym:bool≤ (λ x -> if x then π₁ else π₂))
eval⊩ (inj true)  = in₁
eval⊩ (inj false) = in₂
eval⊩ case = distrib-∧/∨
           ∙ [ map∧ singleton π₁ ∙ swap ∙ apply
             , map∧ singleton π₂ ∙ swap ∙ apply ]
eval⊩ split .ap x = x
eval⊩ split .map (inj₁ x , inj₁ y) = inj₁ (x , y)
eval⊩ split .map (inj₂ x , inj₂ y) = inj₂ (x , y)
