open import Prelude
open import Unused.Classical

module Unused.ClassicalAcc where

record Acc {i j} {A : Set i} (_<_ : Rel A j) (x : A) : Set (i ⊔ j) where
  inductive
  constructor acc
  field run : ∀ y -> y < x -> Acc _<_ y
open Acc public

Well-founded : ∀{i j} {A : Set i} (_<_ : Rel A j) -> Set _
Well-founded _<_ = ∀ x -> Acc _<_ x

data ω+1 : Set where
  ω : ω+1
  nat : ℕ -> ω+1

data _<_ : Rel ℕ zero where
  z<s : ∀{a} -> 0 < ℕ.suc a
  s<s : ∀{a b} -> a < b -> ℕ.suc a < ℕ.suc b

_<≡_ : Rel ℕ zero
a <≡ b = a ≡ b ⊎ a < b

<S? : ∀{a b} -> a < ℕ.suc b -> a <≡ b
<S? {b = ℕ.zero} z<s = inj₁ refl
<S? {b = ℕ.suc _} z<s = inj₂ z<s
<S? {ℕ.suc a} {b = ℕ.suc b} (s<s x) with <S? x
... | inj₁ a=b rewrite a=b = inj₁ refl
... | inj₂ a<b = inj₂ (s<s a<b)
<S? {b = ℕ.zero}  (s<s ())

wf< : Well-founded _<_
wf< ℕ.zero = acc λ { _ () }
wf< (ℕ.suc n) .run b b<Sa with <S? b<Sa
... | inj₁ a=b rewrite a=b = wf< n
... | inj₂ b<a = wf< n .run b b<a


-- ω+1 is well-founded, too!
data _<'_ : Rel ω+1 zero where
  n<ω : ∀{a} -> nat a <' ω
  n<n : ∀{a b} -> a < b -> nat a <' nat b

wf<'-nat : ∀ x -> Acc _<'_ (nat x)
wf<'-nat ℕ.zero = acc (λ { ω () ; (nat x) (n<n ()) })
wf<'-nat (ℕ.suc x) .run (nat y) (n<n y<Sx) with <S? y<Sx
... | inj₁ x=y rewrite x=y = wf<'-nat x
... | inj₂ y<x = wf<'-nat x .run (nat y) (n<n y<x)

wf<' : Well-founded _<'_
wf<' ω .run (nat n) n<ω = wf<'-nat n
wf<' (nat n) = wf<'-nat n

module Tests (P : ℕ -> Set) (P? : ∀ x -> Dec (P x)) where
  -- can I prove this? I think I can't, actually :(.
  --
  -- could I use accessibility and ω+1?
  markov : Σ? ℕ P -> Σ ℕ P
  markov ex? = {!!}

  foo : ∀ n -> Dec (∃ λ i → i < n × P i)
  foo = {!!}
