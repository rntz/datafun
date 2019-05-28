-- Hypothesis: this file is out-of-date and not used. When I opened it, it used
-- false≤ instead of f≤* from Prosets.agda.
module Unused.ACC where

open import Prelude
open import Cat
open import Decidability
open import Nats
open import Booleans

-- Observation: Maybe the nicest semantics of ACC for our purposes is over
-- *decidable* Prosets! We only invoke it on those, and on those, various
-- definitions become nicely interconvertible.

-- Maybe we should define ACC over prosets equipped with a notion of strong
-- ordering, <, such that (x < y) implies (x ≤ y) ∧ ¬ (y ≤ x)? And product on
-- such prosets says:
--
-- (a , x) < (b , y) = ((a < b) × (x ≤ y)) ⊎ ((a ≤ b) × (x < y))
--
-- bluh, some laws for x < y:
--
--     x < y -> x ≤ y
--     x < y -> ¬ (y ≤ x)
--
--     (x ≤ y) <-> (x < y) ⊎ ((x ≤ y) × (y ≤ x)) ?????


module DefnWf where
  module _ (A : Proset) where
    -- "strict Hom"
    Hom< : Rel (Obj A) zero
    Hom< x y = (Hom A x y) × ¬ (Hom A y x)

    -- bounded quantification.
    ∀> : ∀{i} -> Obj A -> (Obj A -> Set i) -> Set i
    ∀> a P = ∀{x} (p : Hom< a x) -> P x

    -- x is accessible if, inductively, everything strictly larger than x is
    -- also accessible.
    record Access (a : Obj A) : Set where
      constructor access
      inductive
      field acc : ∀> a Access -- ∀{x} (p : Hom< a x) -> Access x
    open Access public

    ACC : Set
    ACC = ∀ x -> Access x

  module _ {A : Proset} where
    private instance aa = A

    -- _<_ : 

    ≤∙< : ∀{a b c} -> a ≤ b -> Hom< A b c -> Hom< A a c
    ≤∙< a≤b b<c = a≤b ∙ proj₁ b<c , λ c≤a → proj₂ b<c (c≤a ∙ a≤b)

    access∙≤ : ∀{a b} -> Access A a -> a ≤ b -> Access A b
    access∙≤ acc-a a≤b .acc b<c = acc-a .acc (≤∙< a≤b b<c)

    module _ (≤? : Decidable≤ A) where
      Hom<? : Decidable (Hom< A)
      Hom<? a b = dec× (≤? a b) (dec¬ (≤? b a))

      -- do we ever use this?
      case≤ : ∀{a b} -> a ≤ b -> Hom< A a b ⊎ (b ≤ a)
      case≤ {a}{b} a≤b with ≤? b a
      ... | yes b≤a = inj₂ b≤a
      ... | no ¬b≤a = inj₁ (a≤b , ¬b≤a)

  -- TODO: prove this
  acc-rec : ∀{A l} -> ACC A -> (P : Obj A -> Set l)
          -> (∀ x -> ∀> A x P -> P x)
          -> ∀ a -> P a
  acc-rec acc P f a = {!!}

  module _ {A B} (P : ACC A) (Q : ACC B) where
    -- TODO: rename and prove
    -- I think I need decidability of A, B.
    lem : ∀{a b a' b'} -> Hom< (A ∧ B) (a , b) (a' , b')
        -> Hom< A a a' ⊎ Hom< B b b'
    lem = {!!}

    private
      bar : ∀{a b a' b'}
            (a-rec : ∀> A a λ a' -> ∀ b' -> Access (A ∧ B) (a' , b'))
            (b-rec : ∀> B b λ b' -> Access (A ∧ B) (a , b'))
            (p : Hom< (A ∧ B) (a , b) (a' , b'))
            -> Access (A ∧ B) (a' , b')
      bar {b' = b'} a-rec b-rec p with lem p
      ... | inj₁ a<a' = a-rec a<a' b'
      ... | inj₂ b<b' = access∙≤ (b-rec b<b') (proj₁ p .proj₁ , ident B)

      foo : ∀ a b -> Access (A ∧ B) (a , b)
      foo = acc-rec P (λ a → ∀ b → Access (A ∧ B) (a , b))
            λ a a-rec → acc-rec Q (λ b → Access (A ∧ B) (a , b))
            λ b b-rec → access
            -- want to split on lem here.
            λ { {x , y} p → bar a-rec b-rec p }


module DefnClassical where
  open import Unused.Classical

  module _  (P : Proset) where
    private instance pp = P

    Chain : Set
    Chain = ℕ≤ ⇒ P

    -- The definition we give in seminaive.tex, adjusted to use a "classical" Σ
    -- and ≤.
    Stops : Chain -> Set
    Stops f = Σ?[ i ∈ ℕ ] ∀ j → i ≤ j → ¬ ¬ (ap f j ≤ ap f i)

    -- ACC = "all chains stop".
    ACC : Set
    ACC = ∀ C -> Stops C

  -- TODO: determine whether this classical statement is strong enough to
  -- guarantee termination of fixed point processes when ≤ is decidable. I'm
  -- really not sure it is!

  -- Let's try proving it for some types and constructions.
  ¬3bools : ∀{a b c} -> ¬ bool≤ a b -> ¬ bool≤ b c -> ∅
  ¬3bools {false}         p q = p f≤*
  ¬3bools {true}  {false} p q = q f≤*
  ¬3bools {true}  {true}  p q = p id

  bool-acc : ACC bools
  bool-acc C non-stop =
    non-stop 0 λ j 0≤j Cj≰C0 →
    non-stop j λ k j≤ḱ Ck≰Cj →
    ¬3bools Ck≰Cj Cj≰C0

  module _ {A B} (P : ACC A) (Q : ACC B) where
    import Data.Nat as Nat
    private instance aa = A; bb = B

    -- this works but is ugly
    acc× : ACC (A ∧ B)
    acc× C non-stop =
      P (C ∙ π₁) λ i stops-at-i →
      Q (C ∙ π₂) λ j stops-at-j →
      let stop = i Nat.⊔ j in
      non-stop   stop λ k i⊔j≤k Ck≰Ci⊔j →
      stops-at-i k (in₁ ∙ i⊔j≤k) λ Ck₁≤Ci₁ →
      stops-at-j k (in₂ {a = i} ∙ i⊔j≤k) λ Ck₂≤Cj₂ →
      Ck≰Ci⊔j (Ck₁≤Ci₁ ∙ map C in₁ .proj₁ ,
               Ck₂≤Cj₂ ∙ map C (in₂ {a = i}) .proj₂)


module DefnStream where
  record Stream (A : Set) : Set where
    coinductive
    field head : A
    field tail : Stream A
  open Stream public

  record Always {A} (P : Stream A -> Set) (S : Stream A) : Set where
    coinductive
    field head : P S
    field tail : Always P (tail S)
  open Always public

  Chain : ∀ {A} (R : Rel A zero) (S : Stream A) -> Set
  Chain R = Always (λ S -> R (head S) (head (tail S)))

  data Eventually {A} (P : Stream A -> Set) (S : Stream A) : Set where
    now : P S -> Eventually P S
    later : Eventually P (tail S) -> Eventually P S

  module _ (P : Proset) where
    private instance pp = P

    _<_ : Rel (Obj P) zero
    x < y = (x ≤ y) ∧ ¬ (y ≤ x)

    -- ACC = "there are no strictly ascending chains"
    -- I don't think this is strong enough to prove fix halts!
    ACC : Set
    ACC = ∀ (S : Stream (Obj P)) (asc : Chain _<_ S) -> ∅

  -- -- Ok, let's prove some ACC constructions.
  -- module _ {A B} (A≤? : Decidable≤ A) (B≤? : Decidable≤ B) (P : ACC A) (Q : ACC B) where
  --   private instance aa = A; bb = B
  --   acc× : ACC (A ∧ B)
  --   acc× S asc = {!!}


module Defn1 where
  module _  (P : Proset) where
    private instance pp = P

    Chain : Set
    Chain = ℕ≤ ⇒ P

    -- -- This is the definition we give in seminaive.tex, but it has a problem:
    -- -- it's too strong! Try proving it for booleans, for example: you can't!
    -- Stops : Chain -> Set
    -- Stops f = Σ[ i ∈ ℕ ] (∀ j → i ≤′ j → ap f j ≤ ap f i)

    Stops : Chain -> Set
    Stops f = Σ[ i ∈ ℕ ] (ap f (ℕ.suc i) ≤ ap f i)

    -- "all chains stop"
    ACC : Set
    ACC = ∀ C → Stops C
