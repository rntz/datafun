-- Commonly used categorical structures (eg. products on sets) and instances for
-- them.
open import Prelude
import Data.Sum

open import Cat.Base
open import Cat.Tones
open import Cat.Cartesian
open import Cat.Closed
open import Cat.SetPi

module Cat.Instances where

-- Auto-conversion from Products in C to Sums in (op C). The other direction is
-- definitional.
instance -- ETA
  auto:products→sums : ∀{i j} {{C}} (P : Products {i}{j} C) → Sums (op C)
  auto:products→sums P .bottom = top P
  auto:products→sums P .lub a b = a ∧ b / π₁ / π₂ / ⟨_,_⟩
    where instance -auto = P


-- Structure of basic categories.
instance
  products:set : ∀{i} -> Products (sets {i})
  top products:set = Lift Unit , _
  glb products:set a b = a × b / proj₁ / proj₂ / Data.Product.<_,_>
    where import Data.Product

  sums:set : ∀{i} -> Sums (sets {i})
  bottom sums:set = Lift ∅ , λ{()}
  lub sums:set a b = a ⊎ b / inj₁ / inj₂ / Data.Sum.[_,_]

  cc:set : ∀{i} -> CC (sets {i})
  cc:set = CC: Function (λ { (f , a) -> f a }) (λ f x y -> f (x , y))

  setΠ:set : ∀{i} -> SetΠ i (sets {i})
  setΠ:set = SetΠ: (λ A P → (x : A) -> P x) (λ Γ→P γ a → Γ→P a γ) (λ a ∀P → ∀P a)

instance
  products:cat : ∀{i j} -> Products (cats {i} {j})
  top products:cat = ⊤-cat , fun ≤⊤
  glb products:cat a b = cat× a b / fun π₁ / fun π₂ / λ { (fun f) (fun g) → fun ⟨ f , g ⟩ }

  sums:cat : ∀{i j} -> Sums (cats {i} {j})
  bottom sums:cat = ⊥-cat , Fun: ⊥≤ λ{ {()} }
  lub sums:cat a b = cat+ a b / fun inj₁ / fun inj₂ / disj
    where disj : ∀{a b c} -> a ≤ c -> b ≤ c -> cat+ a b ≤ c
          disj F G = Fun: [ ap F , ap G ] λ { (inj₁ x) → map F x ; (inj₂ x) → map G x }

  cc:cat : ∀{i} -> CC (cats {i} {i})
  CC.products cc:cat = products:cat
  _⇨_   {{cc:cat}} = cat→
  apply {{cc:cat}} .ap (F , a) = ap F a
  apply {{cc:cat}} {A}{B} .map {F , _} {G , _} (F≤G , a≤b) = compo B F≤G (map G a≤b)
  curry {{cc:cat}} F .ap a .ap b = ap F (a , b)
  curry {{cc:cat}} {A}{B} F .ap a .map b≤b' = map F (ident A , b≤b')
  curry {{cc:cat}} {A}{B} F .map a≤a' = map F (a≤a' , ident B)

  setΠ:cat : ∀{i j k} -> SetΠ k (cats {i ⊔ k} {j ⊔ k})
  setΠ:cat = SetΠ: catΠ (λ Γ→P → fun (λ γ a → Γ→P a .map γ)) (λ a → fun (λ ∀P≤ → ∀P≤ a))


-- Preserving cartesian structure over operations on categories.
module _ {i j k l C D} (P : Sums {i}{j} C) (Q : Sums {k}{l} D) where
  private instance cc = C; cs = P; dd = D; ds = Q
  -- used in {Proset,Change}Sem/Types*.agda
  sums:cat× : Sums (cat× C D)
  bottom sums:cat× = (⊥ , ⊥) , ⊥≤ , ⊥≤
  lub sums:cat× (a , x) (b , y)
    = (a ∨ b) , (x ∨ y) / in₁ , in₁ / in₂ , in₂
    / λ { (f₁ , f₂) (g₁ , g₂) → [ f₁ , g₁ ] , [ f₂ , g₂ ] }

-- If B has sums, then (A ⇒ B) has sums too. Used in ProsetSem.Types.
module _ {i j k l} {A : Cat i j} {B} (bs : Sums {k}{l} B) where
  private instance b' = B; bs' = bs
  instance
    sums:cat→ : Sums (cat→ A B)
    bottom sums:cat→ = constant ⊥ , ⊥≤
    -- bottom sums:cat→ = constant ⊥ , λ _ → ⊥≤
    lub sums:cat→ F G .a∧b .ap x = ap F x ∨ ap G x
    lub sums:cat→ F G .a∧b .map x≤y = map∨ (map F x≤y) (map G x≤y)
    lub sums:cat→ F G .∧E₁ = in₁
    lub sums:cat→ F G .∧E₂ = in₂
    lub sums:cat→ F G .∧I F≤H G≤H = [ F≤H , G≤H ]
