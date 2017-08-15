module Markov where

open import Prelude
open import Classical

module _ {i} {P : ℕ -> Set i} (P? : ∀ n -> Dec (P n)) .(terminates : Σ? ℕ P) where
  -- This is https://en.wikipedia.org/wiki/Markov%27s_principle.
  --
  -- This function will, in fact, terminate (assuming `terminates` has been
  -- proven legitimately), but Agda's termination checker won't accept it;
  -- Markov's principle is not provable constructively.
  --
  -- NON_TERMINATING makes Agda accept the definition anyway. However, Agda
  -- won't try to reduce it during typechecking, which is probably for the best.
  -- We could also mark it TERMINATING, in which case Agda *would* try to reduce
  -- it during typechecking.
  {-# NON_TERMINATING #-}
  markov : Σ ℕ P
  markov = search 0
    where
      search : ℕ -> Σ ℕ P
      search n with P? n
      ... | yes p  = n , p
      ... | no ¬p = search (ℕ.suc n)


-- Non-termination monad
mutual
  data NT {i} (A : Set i) : Set i where
    done : A -> NT A
    more : More A -> NT A

  record More {i} (A : Set i) : Set i where
    constructor More!
    coinductive
    field step : NT A

open More public

module _ {i} {A : Set i} where
  data Terminates : NT A -> ℕ -> Set i where
    done : ∀{x n} -> Terminates (done x) n
    more : ∀{p n} -> Terminates (step p) n -> Terminates (more p) (ℕ.suc n)

  -- You can extract the value of a terminating program.
  run : ∀ {p n} -> Terminates p n -> A
  run {done x} done = x
  run (more t) = run t

  -- Given a bound `n`, we can decide whether a program terminates in ≤ n steps.
  terminates? : ∀ p n -> Dec (Terminates p n)
  terminates? (done x)   _       = yes done
  terminates? (more x) ℕ.zero    = no λ {()}
  terminates? (more x) (ℕ.suc n) with terminates? (step x) n
  ... | yes indeed = yes (more indeed)
  ... | no  hardly = no λ { (more t) → hardly t }

  -- Markov implies that if a program weakly terminates, it terminates:
  markov-term : ∀{p} -> ∃? (Terminates p) -> ∃ (Terminates p)
  markov-term = markov (terminates? _)
