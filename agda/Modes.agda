{-# OPTIONS --postfix-projections #-}
module Modes where

open import Prelude
open import Cat
open import Action
open import Tones

data Mode : Set where
  ID OP □ ◇ : Mode

data _≺_ : (T U : Mode) -> Set where
  ≺refl : ∀{T} -> T ≺ T
  □≺ : ∀{T} -> □ ≺ T
  ≺◇ : ∀{T} -> T ≺ ◇

instance
  -- Completely tedious decidability procedures.
  mode=? : (T U : Mode) -> Dec (T ≡ U)
  mode=? = λ { ID ID → yes refl ; ID OP → no (λ ()) ; ID □ → no (λ ()) ; ID ◇ → no (λ ()) ; OP ID → no (λ ()) ; OP OP → yes refl ; OP □ → no (λ ()) ; OP ◇ → no (λ ()) ; □ ID → no (λ ()) ; □ OP → no (λ ()) ; □ □ → yes refl ; □ ◇ → no (λ ()) ; ◇ ID → no (λ ()) ; ◇ OP → no (λ ()) ; ◇ □ → no (λ ()) ; ◇ ◇ → yes refl }
  _≺?_ : (T U : Mode) -> Dec (T ≺ U)
  _≺?_ = λ { ID ID → yes ≺refl ; ID OP → no λ () ; ID □ → no λ () ; ID ◇ → yes ≺◇ ; OP ID → no λ () ; OP OP → yes ≺refl ; OP □ → no λ () ; OP ◇ → yes ≺◇ ; □ y → yes □≺ ; ◇ ID → no λ () ; ◇ OP → no λ () ; ◇ □ → no λ () ; ◇ ◇ → yes ≺refl }

  modes : Proset
  modes = Cat: Mode _≺_ ≺refl λ { ≺refl g → g ; □≺ g → □≺ ; ≺◇ ≺refl → ≺◇ ; ≺◇ ≺◇ → ≺◇ }

  mode-sums : Sums modes
  bottom mode-sums = □ , □≺
  lub mode-sums ID ID = ID / ≺refl / ≺refl / λ x _ → x
  lub mode-sums OP OP = OP / ≺refl / ≺refl / λ x _ → x
  lub mode-sums ID OP = ◇ / ≺◇ / ≺◇ / λ { ≺refl () ; ≺◇ ≺◇ → ≺◇ }
  lub mode-sums OP ID = ◇ / ≺◇ / ≺◇ / λ { ≺refl () ; ≺◇ ≺◇ → ≺◇ }
  lub mode-sums □ U = U / □≺ / ≺refl / λ _ x → x
  lub mode-sums ◇ U = ◇ / ≺refl / ≺◇ / λ x _ → x
  lub mode-sums T □ = T / ≺refl / □≺ / λ x _ → x
  lub mode-sums T ◇ = ◇ / ≺◇ / ≺refl / λ _ x → x

  mode-products : Products modes
  top mode-products = ◇ , ≺◇
  glb mode-products □ b = □ / id / □≺ / const
  glb mode-products ◇ b = b / ≺◇ / id / ignore
  glb mode-products a □ = □ / □≺ / id / ignore
  glb mode-products a ◇ = a / id / ≺◇ / const
  glb mode-products ID ID = ID / id / id / const
  glb mode-products OP OP = OP / id / id / const
  glb mode-products ID OP = □ / □≺ / □≺ / λ { ≺refl () ; □≺ □≺ → □≺ }
  glb mode-products OP ID = □ / □≺ / □≺ / λ { ≺refl () ; □≺ □≺ → □≺ }

  mode-compose : Action Mode Mode
  action mode-compose ID T = T
  action mode-compose T ID = T
  action mode-compose T □ = □
  action mode-compose T ◇ = ◇
  action mode-compose □ OP = □
  action mode-compose ◇ OP = ◇
  action mode-compose OP OP = ID

-- Denotation of modes as tones.
den : ∀{i} → Fun modes (tones {i}{i})
ap den ID = tone-id; ap den OP = tone-op; ap den □ = tone-iso; ap den ◇ = tone-path
map den ≺refl = id
map den {□} {◇} _ = fun {id} (path-by ∘ proj₁)
map den {ID} ≺◇ = fun path-by
map den {OP} ≺◇ = fun (path⁻¹ ∘ path-by)
map den {◇} ≺◇ = id
map den {.□} {□} □≺ = id
map den {.□} {ID} □≺ = fun proj₁
map den {.□} {OP} □≺ = fun proj₂
