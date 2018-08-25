{-# OPTIONS --postfix-projections #-}
module Examples.MTLC-Tones where

open import Prelude
open import Cat
open import Prosets
open import Tones
open import Action

-- Types
infixr 6 _⊃_
data Type : Set where
  bool : Type
  _!_ : (T : Tone) (a : Type) → Type
  _⊃_ _*_ _+_ : (a b : Type) → Type

open import Contexts (Type)

data _⊣_ : (T U : Tone) → Set where
  instance id⊣id : ID ⊣ ID
  instance op⊣op : OP ⊣ OP
  instance ◇⊣□ : ◇ ⊣ □

mutual
  infix 1 _⊢_
  data _⊢_ (X : Cx) : Type → Set where
    var : ∀{a} → X a → X ⊢ a
    app : ∀{a b} (M : X ⊢ a ⊃ b) (N : X ⊢ a) → X ⊢ b
    lam : ∀{a b} (M : a ∷ X ⊢ b)
        → (p : ID ≤ usage [ const ID , const ◇ ] M)
        → X ⊢ a ⊃ b
    box : ∀{a} T (M : X ⊢ a) → X ⊢ T ! a
    unbox : ∀{a T} U {{p : U ⊣ T}} (M : X ⊢ T ! a) → X ⊢ a

  usage : ∀{X} (f : ∀{a} → X a → Tone) → ∀{a} → X ⊢ a → Tone
  usage f (var x) = f x
  usage f (app M N) = usage f M ∧ usage f N
  usage f (lam M p) = usage [ const ◇ , f ] M
  usage f (box T M) = T · usage f M
  -- Γ ⊢ T A
  -- -------
  -- U Γ ⊢ A
  usage f (unbox U M) = U · usage f M

rename : ∀{X Y} → X ≤ Y → ∀{a} → X ⊢ a → Y ⊢ a
rename ρ (var x) = var (ρ _ x)
rename ρ (app M N) = app (rename ρ M) (rename ρ N)
-- I need a lemma about the interaction of usage and rename!
rename ρ (lam M p) = lam (rename (λ a → map∨ id (ρ a)) M) (p • {!!})
rename ρ (box T M) = box T (rename ρ M)
rename ρ (unbox U M) = unbox U (rename ρ M)

-- foo : ∀{X Y : Cx} {a : Type} {f :  M ρ} → usage {X} f {a} M ≤ usage {Y} f (rename ρ M)
-- foo = {!!}

-- data _⊢_⊣_ (X : Cx) : (a : Type) (f : Usage X) → Set where
--   var : ∀{a f} {x : X a} (p : ID ≤ f (, x))
--       → X ⊢ a ⊣ f
--   app : ∀{a b f g} (M : X ⊢ a ⊃ b ⊣ f) (N : X ⊢ a ⊣ g)
--       → X ⊢ b ⊣ f ∧ g
--   lam : ∀{a b f} (p : ID ≤ f imm) (M : a ∷ X ⊢ b ⊣ f)
--       → X ⊢ a ⊃ b ⊣ drop f
--   lett : ∀{a b f g} (M : X ⊢ a ⊣ f) (N : a ∷ X ⊢ b ⊣ g)
--        → X ⊢ b ⊣ drop g ∧ g imm · f
--   bool : ∀{f} (b : Bool) → X ⊢ bool ⊣ f
--   if : ∀{a f g₁ g₂} (M : X ⊢ bool ⊣ f) (N₁ : X ⊢ a ⊣ g₁) (N₂ : X ⊢ a ⊣ g₂)
--      → X ⊢ a ⊣ f ∧ (λ x → □ · (g₁ x ∧ g₂ x))
--   box : ∀{a f} T (M : X ⊢ a ⊣ f) → X ⊢ T ! a ⊣ T · f
--   unbox : ∀{a f T U} (p : U ⊣ T) (M : X ⊢ T ! a ⊣ f)
--         → X ⊢ a ⊣ U · f
--   letbox : ∀{a b f g T} (p : T ≤ g imm) (M : X ⊢ T ! a ⊣ f) (N : a ∷ X ⊢ b ⊣ g)
--          → X ⊢ b ⊣ f ∧ drop g


-- -- Used in Examples.MTLC-Tones
-- catΠ-products : ∀{i j k A B} → (∀ x → Products (B x)) → Products (catΠ{i}{j}{k} A B)
-- catΠ-products P .top = proj₁ ∘ top ∘ P , λ x → P x .top .proj₂
-- catΠ-products P .glb a b = a∧b ∘ F / ∧E₁ ∘ F / ∧E₂ ∘ F / λ f g x → F x .∧I (f x) (g x)
--   where F : ∀ x → ProductOf _ (a x) (b x)
--         F x = P x .glb (a x) (b x)

-- -- Maps from variables to usage modes form a context-indexed family of
-- -- preorders.
-- module _ {X : Cx} where
--   instance
--     usages : Proset
--     Obj usages = ∀{a} → a ∈ X → Tone
--     Hom usages f g = ∀{a} x → f {a} x ≤ g x
--     ident usages _ = id
--     compo usages f≤g g≤h x = f≤g x • g≤h x

--     usage-products : Products usages
--     top usage-products = const ◇ , λ _ → ≺◇
--     glb usage-products a b = (λ x → a x ∧ b x)
--       / (λ x → π₁) / (λ x → π₂ {a = a x})
--       / λ f g x → ⟨ f x , g x ⟩

--   -- instance
--   --   usages : Proset
--   --   usages = catΠ (Var X) (const tones)

--   --   usage-products : Products usages
--   --   usage-products = catΠ-products (const tone-products)

-- Usage : Cx → Set
-- Usage X = usages {X} .Obj

-- Terms
-- pattern imm = (, here)
-- drop : ∀{X a} → Usage (a ∷ X) → Usage X
-- drop f = f ∘ ∃-map λ _ → next

-- TODO: subtyping?
-- TODO: is there a way to ABT-ify this by separating out premises & term formers?
-- seems difficult, because term formers can do complicated things with tones.

-- -- Other options:
-- -- - induction/recursion, with a function assigning each variable its usage
-- --   problem: can't test variables for equality!
-- --
-- -- - induction/recursion, with a function assigning a (variable,tone) pair to a
-- --   Set witnessing the variable is used {at,compatibly with} that tone.
-- infix 1 _⊢_⊣_
-- data _⊢_⊣_ (X : Cx) : (a : Type) (f : Usage X) → Set where
--   var : ∀{a f} {x : X a} (p : ID ≤ f (, x))
--       → X ⊢ a ⊣ f
--   app : ∀{a b f g} (M : X ⊢ a ⊃ b ⊣ f) (N : X ⊢ a ⊣ g)
--       → X ⊢ b ⊣ f ∧ g
--   lam : ∀{a b f} (p : ID ≤ f imm) (M : a ∷ X ⊢ b ⊣ f)
--       → X ⊢ a ⊃ b ⊣ drop f
--   lett : ∀{a b f g} (M : X ⊢ a ⊣ f) (N : a ∷ X ⊢ b ⊣ g)
--        → X ⊢ b ⊣ drop g ∧ g imm · f
--   bool : ∀{f} (b : Bool) → X ⊢ bool ⊣ f
--   if : ∀{a f g₁ g₂} (M : X ⊢ bool ⊣ f) (N₁ : X ⊢ a ⊣ g₁) (N₂ : X ⊢ a ⊣ g₂)
--      → X ⊢ a ⊣ f ∧ (λ x → □ · (g₁ x ∧ g₂ x))
--   box : ∀{a f} T (M : X ⊢ a ⊣ f) → X ⊢ T ! a ⊣ T · f
--   unbox : ∀{a f T U} (p : U ⊣ T) (M : X ⊢ T ! a ⊣ f)
--         → X ⊢ a ⊣ U · f
--   letbox : ∀{a b f g T} (p : T ≤ g imm) (M : X ⊢ T ! a ⊣ f) (N : a ∷ X ⊢ b ⊣ g)
--          → X ⊢ b ⊣ f ∧ drop g

-- -- TODO: renaming & substitution.
-- -- shit, I need _two_ renaming lemmas, probably? one for contexts, another for usages?
-- -- argh, and renaming a context needs to transport its usage, I think. ugh.

-- -- So, this works. But shouldn't there also be a map the other way? If X ≤ Y,
-- -- every variable in X can be mapped to one one Y. So if we know how variables
-- -- in X are used, we can derive how variables in Y will be used. Variables y ∈ Y
-- -- are used at the meet of the tones they're used at in X.
-- foo : ∀{X Y : Cx} → X ≤ Y → Usage Y → Usage X
-- foo ρ f (, x) = f (, ρ _ x)

-- bar : ∀{X Y : Cx} → X ≤ Y → Usage X → Usage Y
-- -- Problem: I need a ρ⁻¹! Do I? Yeah, probably, since I'm trying to come up with
-- -- a concrete tone, not just a Set. Uh-oh!
-- bar ρ R (a , y) = {!ρ a!}

-- -- Γ ⊑ Θ iff ∀x. Γ(x) ≤ Θ(x).
-- _⊑_ : Rel (Σ Cx Usage) zero
-- -- Is there a way to make this more concise? It's basically just (f ≤ g ∘ ρ)
-- -- but, bleh.
-- (X , f) ⊑ (Y , g) = Σ[ ρ ∈ X ≤ Y ] ∀ a (x : X a) → f (, x) ≤ g (, ρ a x)

-- -- -- This seems either impossible or ridiculously difficult.
-- -- rename : ∀{X Y f g} → (X , f) ⊑ (Y , g) → ∀{a} → X ⊢ a ⊣ f → Y ⊢ a ⊣ g
-- -- rename ρ (var p) = {!!}
-- -- rename (ρ , σ) (app M N) =
-- --   app (rename (ρ , λ a x → {!σ a x!}) M)
-- --       (rename {!!} N) -- app (rename ρ M) (rename ρ N)
-- -- rename ρ (lam p M) = {!!}
-- -- rename ρ (lett M N) = {!!}
-- -- rename ρ (bool b) = bool b
-- -- rename ρ (if M N₁ N₂) = {!!}
-- -- rename ρ (box T M) = {!!}
-- -- rename ρ (unbox p M) = {!!}
-- -- rename ρ (letbox p M N) = {!!}
