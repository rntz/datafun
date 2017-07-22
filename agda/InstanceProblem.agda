open import Level

postulate
  ℕ : Set

  HasId : ∀{i j} (A : Set i) (R : A -> A -> Set j) -> Set (i ⊔ j)
  id : ∀{i j A R} {{r : HasId {i}{j} A R}} {a} -> R a a
  instance
    set-has-id : HasId Set (λ a b -> a -> b)

works-fine : ℕ -> ℕ
works-fine = id

does-not-work : ℕ -> ℕ
does-not-work x = id x

also-works : ℕ -> ℕ
also-works x = id {{set-has-id}} x
