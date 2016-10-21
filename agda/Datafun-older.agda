module Datafun where

open import Data.Nat
open import Data.List
open import Data.Bool renaming (_∧_ to _&&_; _∨_ to _||_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym)
  renaming (subst to subst≡)
open import Data.Product
open import Data.Sum
open import Data.Unit using (⊤; tt)
open import Function using (_∘_)
open import Data.Maybe

infix 3 _⊢_ _⊢*_
-- infix 3 _⊣α_
infix 4 _∈_
infixr 4 _!_∷_
infixr 6 _[→]_
infix 7 _[x]_
infix 7 _[+]_


---------- Elements of lists ----------
-- data _∈_ {a : Set} (e : a) : List a → Set where
--   car : {xs : List a} → e ∈ (e ∷ xs)
--   cdr : {x : a}{xs : List a} → e ∈ xs → e ∈ (x ∷ xs)
-- -- a lisper was here

-- extend∈ᵣ : {a : Set} {x : a} {l : List a}
--          → (m : List a) → x ∈ l → x ∈ (l ++ m)
-- extend∈ᵣ m car = car
-- extend∈ᵣ m (cdr x∈l) = cdr (extend∈ᵣ m x∈l)


---------- Our fixed-point theorem ----------
record FixTheorem : Set₁ where
  -- The preconditions
  infix 5 _◁_
  field
    set : Set
    ε : set
    _◁_ : set → set → Set
    ε-least : (x : set) → ε ◁ x
    transitive : {a b c : set} → a ◁ b → b ◁ c → a ◁ c
    -- Is this the right statement of ACC?
    -- It feels too constructive.
    acc : (s : ℕ → set)
        → ((i : ℕ) → s i ◁ s (suc i))
        -- there is some prefix point `i' ≥ all subsequent points
        → Σ[ i ∈ ℕ ] ∀ (j : ℕ) → i ≤ j → s j ◁ s i
    f : set → set
    monotone : {x y : set} → x ◁ y → f x ◁ f y

  -- The construction itself.
  -- TODO: clean this messy code up.
  private
    s : ℕ → set
    s = fold ε f

    s-increases : (i : ℕ) → s i ◁ s (suc i)
    s-increases zero = ε-least (f ε)
    s-increases (suc i) = monotone (s-increases i)

    -- TODO: rename
    magic : Σ[ i ∈ ℕ ] ∀ (j : ℕ) → i ≤ j → s j ◁ s i
    magic = acc s s-increases

    i = proj₁ magic

    suc-increases : (i : ℕ) → i ≤ suc i
    suc-increases zero = z≤n
    suc-increases (suc n) = s≤s (suc-increases n)

  fixed-point : set
  fixed-point = s i

  is-prefix-point : f fixed-point ◁ fixed-point
  is-prefix-point = proj₂ magic (suc i) (suc-increases i)

  is-least : (x : set) → f x ◁ x → fixed-point ◁ x
  is-least x fx◁x = foo i
    where foo : (i : ℕ) → s i ◁ x
          foo zero = ε-least x
          foo (suc i) = transitive (monotone (foo i)) fx◁x


---------- Tones ----------
data Tone : Set where
  disc : Tone
  mono : Tone

untone : ∀{ℓ} {a : Set ℓ} → a → a → (t : Tone) → a
untone x y disc = x
untone x y mono = y

data _≼_ : Tone → Tone → Set where
  refl≼ : {tone : Tone} → tone ≼ tone
  disc≼any : {tone : Tone} → disc ≼ tone


---------- Types ----------
data Type : Set where
  tNat : Type
  tBool : Type
  tSet : Type → Type
  □ : Type → Type
  _[→]_ : Type → Type → Type
  _[x]_ : Type → Type → Type
  _[+]_ : Type → Type → Type

semilattice : Type → Bool
semilattice tNat = true
semilattice tBool = true
semilattice (tSet t) = true
semilattice (□ t) = false
semilattice (a [→] b) = semilattice b
semilattice (a [x] b) = semilattice a && semilattice b
semilattice (a [+] b) = false

finite : Type → Bool
finite tNat = false
finite tBool = true
finite (tSet t) = finite t
finite (□ t) = finite t
finite (a [→] b) = finite a && finite b
finite (a [x] b) = finite a && finite b
finite (a [+] b) = finite a && finite b

eqtype : Type → Bool
eqtype tNat = true
eqtype tBool = true
eqtype (tSet t) = eqtype t
eqtype (□ t) = eqtype t
eqtype (a [→] b) = false
eqtype (a [x] b) = eqtype a && eqtype b
eqtype (a [+] b) = eqtype a && eqtype b

acc : Type → Bool
acc tNat = false
acc tBool = true
acc (tSet t) = finite t
acc (□ t) = true
acc (a [→] b) = finite a && acc b
acc (a [x] b) = acc a && acc b
acc (a [+] b) = acc a && acc b

Holds? : Bool → Set
Holds? x = x ≡ true

Semilattice? : Type → Set
Semilattice? t = Holds? (semilattice t)

Fixtype? : Type → Set
Fixtype? t = Holds? (semilattice t && eqtype t && acc t)


-- -- Preorders
-- record Preorder : Set₁ where
--   field
--     set : Set
--     _◁_ : set → set → Set
--     refl◁ : (x : set) → x ◁ x
--     trans◁ : {x y z : set} → x ◁ y → y ◁ z → x ◁ z

-- Disc : Set → Preorder
-- Disc s = record { set = s ; _◁_ = _≡_ ; refl◁ = λ x → refl ; trans◁ = {!!} }

-- [[_]] : Type → Preorder
-- [[ tNat ]] = record { set = ℕ ; _◁_ = _≤_ ; refl◁ = {! !} ; trans◁ = {!!} }
-- [[ tBool ]] = record { set = Bool ; _◁_ = {!!} ; refl◁ = {!!} ; trans◁ = {!!} }
-- [[ tSet x ]] = record { set = {!!} ; _◁_ = {!!} ; refl◁ = {!!} ; trans◁ = {!!} }
-- [[ □ x ]] = Disc (Preorder.set [[ x ]])
-- [[ a [→] b ]] = {!!}
-- [[ a [x] b ]] = {!!}
-- [[ a [+] b ]] = {!!}


---------- Typing contexts ----------
Env : Set
-- Env = Tone → List Type
Env = List (Tone × Type)

∅ : Env
-- ∅ _ = []
∅ = []

wipe : Env → Env
wipe [] = []
wipe ((mono , e) ∷ Ω) = wipe Ω
wipe ((disc , e) ∷ Ω) = ((disc , e) ∷ wipe Ω)
-- wipe _ mono = []
-- wipe Ω disc = Ω disc

wipe-for : Tone → Env → Env
wipe-for disc Ω = wipe Ω
wipe-for mono Ω = Ω

_!_∷_ : Type → Tone → Env → Env
(a ! tone ∷ Ω) = (tone , a) ∷ Ω
-- (a ! mono ∷ Ω) mono = a ∷ Ω mono
-- (a ! disc ∷ Ω) disc = a ∷ Ω disc
-- (_ ! _ ∷ Ω) tone = Ω tone

-- record _∋_ (Ω : Env) (a : Type) : Set where
--   constructor is
--   field
--     tone : Tone
--     member : a ∈ Ω tone

data _∈_ (type : Type) : Env → Set where
  -- a lisper was here
  car : {Ω : Env}{tone : Tone} → type ∈ (tone , type) ∷ Ω
  cdr : {Ω : Env}{tone : Tone}{ignored-type : Type}
      → type ∈ Ω → type ∈ ((tone , ignored-type) ∷ Ω)

-- TODO: remove
_∋_ : Env → Type → Set
a ∋ b = b ∈ a

-- cons∋ disc (is disc member) = is disc (cdr member)
-- cons∋ disc (is mono member) = is mono member
-- cons∋ mono (is disc member) = is disc member
-- cons∋ mono (is mono member) = is mono (cdr member)

------ Old version -----
-- wipe (Ψ , Γ) = (Ψ , [])

-- env : Tone → Env → List Type
-- env disc = proj₁
-- env mono = proj₂

-- _disc∷_ _mono∷_ : Type → Env → Env
-- a disc∷ (Ψ , Γ) = (a ∷ Ψ , Γ)
-- a mono∷ (Ψ , Γ) = (Ψ , a ∷ Γ)

-- data _∋_ : Env → Type → Set where
--   is : {Ψ Γ : List Type} {a : Type}
--      → (tone : Tone) → a ∈ untone Ψ Γ tone → (Ψ , Γ) ∋ a


---------- Well-typed terms ----------
data _⊢_ (Ω : Env) : Tone → Type → Set where

  -- Variables
  var : {a : Type} → Ω ∋ a → Ω ⊢ a

  -- Fixed points
  fix : {type : Type}
        → Fixtype? type → (type ! mono ∷ Ω) ⊢ type
        → Ω ⊢ type

  -- Semilattices
  ε : {l : Type} (proof : Semilattice? l) → Ω ⊢ l
  vee : {l : Type}
      → Semilattice? l → Ω ⊢ l → Ω ⊢ l
      → Ω ⊢ l

  -- Products
  ⟨_,_⟩ : {a b : Type}
        → Ω ⊢ a → Ω ⊢ b
        → Ω ⊢ a [x] b
  π : {a b : Type} (left : Bool)
    → Ω ⊢ a [x] b
    → Ω ⊢ (if left then a else b)

  -- TODO: Sums

  -- Booleans
  bool : Bool → Ω ⊢ tBool
  if : {a : Type}
     → wipe Ω ⊢ tBool → Ω ⊢ a → Ω ⊢ a
     → Ω ⊢ a
  when : {l : Type}
       → Semilattice? l → Ω ⊢ tBool → Ω ⊢ l
       → Ω ⊢ l

  -- Finite sets
  singleton : {a : Type} → wipe Ω ⊢ a → Ω ⊢ tSet a
  ⋁ : {a l : Type}
    → Semilattice? l → Ω ⊢ tSet a → a ! disc ∷ Ω ⊢ l
    → Ω ⊢ l

  -- Functions
  lam : {a b : Type}
      → a ! mono ∷ Ω ⊢ b
      → Ω ⊢ a [→] b

  app : {a b : Type}
      → Ω ⊢ a [→] b → Ω ⊢ a
      → Ω ⊢ b

  -- Discrete comonad, □
  box : {a : Type}
      → wipe Ω ⊢ a
      → Ω ⊢ □ a

  letbox : {a b : Type}
         → Ω ⊢ □ a → a ! disc ∷ Ω ⊢ b
         → Ω ⊢ b

-- data _⊢_ (Ω : Env) : Type → Set where

--   -- Variables
--   var : {a : Type} → Ω ∋ a → Ω ⊢ a

--   -- Fixed points
--   fix : {type : Type}
--         → Fixtype? type → (type ! mono ∷ Ω) ⊢ type
--         → Ω ⊢ type

--   -- Semilattices
--   ε : {l : Type} (proof : Semilattice? l) → Ω ⊢ l
--   vee : {l : Type}
--       → Semilattice? l → Ω ⊢ l → Ω ⊢ l
--       → Ω ⊢ l

--   -- Products
--   ⟨_,_⟩ : {a b : Type}
--         → Ω ⊢ a → Ω ⊢ b
--         → Ω ⊢ a [x] b
--   π : {a b : Type} (left : Bool)
--     → Ω ⊢ a [x] b
--     → Ω ⊢ (if left then a else b)

--   -- TODO: Sums

--   -- Booleans
--   bool : Bool → Ω ⊢ tBool
--   if : {a : Type}
--      → wipe Ω ⊢ tBool → Ω ⊢ a → Ω ⊢ a
--      → Ω ⊢ a
--   when : {l : Type}
--        → Semilattice? l → Ω ⊢ tBool → Ω ⊢ l
--        → Ω ⊢ l

--   -- Finite sets
--   singleton : {a : Type} → wipe Ω ⊢ a → Ω ⊢ tSet a
--   ⋁ : {a l : Type}
--     → Semilattice? l → Ω ⊢ tSet a → a ! disc ∷ Ω ⊢ l
--     → Ω ⊢ l

--   -- Functions
--   lam : {a b : Type}
--       → a ! mono ∷ Ω ⊢ b
--       → Ω ⊢ a [→] b

--   app : {a b : Type}
--       → Ω ⊢ a [→] b → Ω ⊢ a
--       → Ω ⊢ b

--   -- Discrete comonad, □
--   box : {a : Type}
--       → wipe Ω ⊢ a
--       → Ω ⊢ □ a

--   letbox : {a b : Type}
--          → Ω ⊢ □ a → a ! disc ∷ Ω ⊢ b
--          → Ω ⊢ b


-- Explicit substitutions
-- See "Explicit substitions", Abadi, Cardelli, Curien, Lévy, 1996
-- seriously it's a great, underappreciated paper

data _⊢*_ : Env → Env → Set where
  id : {Ω : Env} → Ω ⊢* Ω
  _•_ : {Ωa Ωb Ωc : Env} → Ωa ⊢* Ωb → Ωb ⊢* Ωc → Ωa ⊢* Ωc
  ↑ : {Ω : Env} {tone : Tone} {type : Type}
    → (type ! tone ∷ Ω) ⊢* Ω
  _·_ : {a : Type} {Ωa Ωb : Env}
       → (what : Σ[ tone ∈ Tone ] wipe-for tone Ωa ⊢ a)
       → Ωa ⊢* Ωb
       → Ωa ⊢* (a ! proj₁ what ∷ Ωb)
  _∙□_ : {a : Type} {Ωa Ωb : Env}
       → ((Ω : Env) → Ω ≡ wipe Ωa → Ωa ⊢ a)
       → 
  -- s-wipe : {Ω : Env} → Ω ⊢* wipe Ω

-- weak head normal form substitutions
data _⊢*!_ : Env → Env → Set where
  ↑! : {Ω : Env} {tone : Tone} {type : Type}
     → (type ! tone ∷ Ω) ⊢*! Ω
  _·!_ : {a : Type} {Ωa ωb : Env}
       → 

wipe-idempotent : (Ω : Env) → wipe (wipe Ω) ≡ wipe Ω
wipe-idempotent [] = refl
wipe-idempotent ((disc , a) ∷ Ω) rewrite wipe-idempotent Ω = refl
wipe-idempotent ((mono , a) ∷ Ω) rewrite wipe-idempotent Ω = refl

map-wipe : {Ωa Ωb : Env} → Ωa ⊢* Ωb → wipe Ωa ⊢* wipe Ωb
map-wipe id = id
map-wipe (s • s₁) = map-wipe s • map-wipe s₁
map-wipe {(disc , type) ∷ Ω} ↑ = ↑
map-wipe {(mono , type) ∷ Ω} ↑ = id
map-wipe {Ω} ((disc , M) · s) = (disc , M′) · map-wipe s
  where M′ : wipe (wipe Ω) ⊢ _
        M′ rewrite wipe-idempotent Ω = M
map-wipe ((mono , term) · s) = map-wipe s

subst : {Ω Ω′ : Env}{a : Type} → Ω ⊢* Ω′ → Ω′ ⊢ a → Ω ⊢ a
subst id M = M
subst (s • t) M = subst s (subst t M)
subst ↑ (var x) = var (cdr x)
-- subst s-wipe (var x) = var (unwipe-var x)
subst ((disc , N) · s) (var car) = {!!}
subst ((mono , N) · s) (var car) = N
subst ((tone , N) · s) (var (cdr x)) = {!!}
subst s (fix x M) = fix x (subst {!!} M)
subst s (ε p) = ε p
subst s (vee p M M₁) = vee p (subst s M) (subst s M₁)
subst s ⟨ M , M₁ ⟩ = ⟨ subst s M , subst s M₁ ⟩
subst s (π left M) = π left (subst s M)
subst s (bool x) = bool x
subst s (if M M₁ M₂) = if (subst {!!} M) (subst s M₁) (subst s M₂)
subst s (when x M M₁) = when x (subst s M) (subst s M₁)
subst s (singleton M) = singleton (subst {!!} M)
subst s (⋁ x M M₁) = ⋁ x (subst s M) (subst {!!} M₁)
subst s (lam M) = lam (subst {!!} M)
subst s (app M M₁) = app (subst s M) (subst s M₁)
subst s (box M) = box (subst {!!} M)
subst s (letbox M M₁) = letbox (subst s M) (subst {!!} M₁)

-- unwipe : (Ω : Env) → Ω ⊢* wipe Ω
-- unwipe [] = id
-- unwipe ((mono , type) ∷ Ω) = ↑ • unwipe Ω
-- unwipe ((disc , type) ∷ Ω) = (disc , var car) · (↑ • unwipe Ω)

-- unwipe-var : {Ω : Env}{a : Type} → a ∈ wipe Ω → a ∈ Ω
-- unwipe-var {[]} ()
-- unwipe-var {(disc , _) ∷ Ω} car = car
-- unwipe-var {(disc , _) ∷ Ω} (cdr e) = cdr (unwipe-var e)
-- unwipe-var {(mono , _) ∷ Ω} e = cdr (unwipe-var e)

-- unwipe : {Ω : Env}{a : Type} → wipe Ω ⊢ a → Ω ⊢ a
-- unwipe (var x) = var (unwipe-var x)
-- unwipe (fix x M) = fix x {!!}
-- unwipe (ε proof) = {!!}
-- unwipe (vee x M M₁) = {!!}
-- unwipe ⟨ M , M₁ ⟩ = {!!}
-- unwipe (π left M) = {!!}
-- unwipe (bool x) = {!!}
-- unwipe (if M M₁ M₂) = {!!}
-- unwipe (when x M M₁) = {!!}
-- unwipe (singleton M) = {!!}
-- unwipe (⋁ x M M₁) = {!!}
-- unwipe (lam M) = {!!}
-- unwipe (app M M₁) = {!!}
-- unwipe (box M) = {!!}
-- unwipe (letbox M M₁) = {!!}

-- subst : {Ω Ω′ : Env}{a : Type} → Ω ⊢* Ω′ → Ω′ ⊢ a → Ω ⊢ a
-- subst id M = M
-- subst (s • t) M = subst s (subst t M)
-- subst ↑ (var x) = var (cdr x)
-- subst s-wipe (var x) = var (unwipe-var x)
-- subst ((disc , N) · s) (var car) = subst s-wipe N
-- subst ((mono , N) · s) (var car) = N
-- subst ((tone , N) · s) (var (cdr x)) = {!!}
-- subst s (fix x M) = fix x (subst {!!} M)
-- subst s (ε p) = ε p
-- subst s (vee p M M₁) = vee p (subst s M) (subst s M₁)
-- subst s ⟨ M , M₁ ⟩ = ⟨ subst s M , subst s M₁ ⟩
-- subst s (π left M) = π left (subst s M)
-- subst s (bool x) = bool x
-- subst s (if M M₁ M₂) = if (subst {!!} M) (subst s M₁) (subst s M₂)
-- subst s (when x M M₁) = when x (subst s M) (subst s M₁)
-- subst s (singleton M) = singleton (subst {!!} M)
-- subst s (⋁ x M M₁) = ⋁ x (subst s M) (subst {!!} M₁)
-- subst s (lam M) = lam (subst {!!} M)
-- subst s (app M M₁) = app (subst s M) (subst s M₁)
-- subst s (box M) = box (subst {!!} M)
-- subst s (letbox M M₁) = letbox (subst s M) (subst {!!} M₁)


---------- Renaming substitutions ----------
-- record _⊣α_ (Ω′ : Env) (Ω : Env) : Set where
--   constructor α[_,_]
--   field
--     rename-disc : {a : Type} → a ∈ Ω′ disc → a ∈ Ω disc
--     rename-mono : {a : Type} → a ∈ Ω′ mono → Ω ∋ a

-- open _⊣α_

-- -- Composing renamings
-- _•α_ : {Ω₁ Ω₂ Ω₃ : Env} → Ω₁ ⊣α Ω₂ → Ω₂ ⊣α Ω₃ → Ω₁ ⊣α Ω₃
-- _•α_ {Ω₁}{Ω₂}{Ω₃} t s = α[ rename-disc s ∘ rename-disc t , rm ]
--   where rm : {a : Type} → a ∈ Ω₁ mono → Ω₃ ∋ a
--         rm v with rename-mono t v
--         ... | is disc x = is disc (rename-disc s x)
--         ... | is mono x = rename-mono s x

-- -- α-wipe : {Ω : Env} → Ω ⊢α wipe Ω
-- -- α-wipe {Ω} = α[ (λ x → x) , (λ ()) ]

-- α-wipe : {Ω Ω′ : Env} → Ω′ ⊣α Ω → wipe Ω′ ⊣α wipe Ω
-- α-wipe σ = α[ rename-disc σ , is mono ]

-- -- wow is this ugly.
-- α-map : {Ω Ω′ : Env}
--       → (tone : Tone) (a : Type) → Ω′ ⊣α Ω
--       → a ! tone ∷ Ω′ ⊣α a ! tone ∷ Ω
-- α-map {Ω}{Ω′} mono a σ = α[ rename-disc σ , rm ]
--   where rm : {b : Type} → b ∈ a ∷ Ω′ mono → (a ! mono ∷ Ω) ∋ b
--         rm car = is mono car
--         rm (cdr e) = cons∋ mono (rename-mono σ e)
-- α-map {Ω}{Ω′} disc a σ = α[ rd , cons∋ disc ∘ rename-mono σ ]
--   where rd : {b : Type} → b ∈ a ∷ Ω′ disc → b ∈ a ∷ Ω disc
--         rd car = car
--         rd (cdr e) = cdr (rename-disc σ e)

-- rename : {Ω Ω′ : Env} {type : Type} → Ω′ ⊣α Ω → Ω′ ⊢ type → Ω ⊢ type
-- rename σ (var (is disc x)) = var (is disc (rename-disc σ x))
-- rename σ (var (is mono x)) = var (rename-mono σ x)
-- rename {Ω}{Ω′} σ (fix {type = a} p M)
--   = fix p (rename α[ rename-disc σ , rm ] M)
--   where rm : {b : Type} → b ∈ (a ! mono ∷ Ω′) mono → (a ! mono ∷ Ω) ∋ b
--         rm car = is mono car
--         rm (cdr x) with rename-mono σ x
--         ... | is disc a = is disc a
--         ... | is mono b = is mono (cdr b)
-- rename σ (ε proof) = ε proof
-- rename σ (vee x M M₁) = vee x (rename σ M) (rename σ M₁)
-- rename σ ⟨ M , M₁ ⟩ = ⟨ rename σ M , rename σ M₁ ⟩
-- rename σ (π left M) = π left (rename σ M)
-- rename σ (bool x) = bool x
-- rename σ (if M M₁ M₂) = if (rename (α-wipe σ) M) (rename σ M₁) (rename σ M₂)
-- rename σ (when p M M₁) = when p (rename σ M) (rename σ M₁)
-- rename σ (singleton M) = singleton (rename (α-wipe σ) M)
-- rename {Ω}{Ω′} σ (⋁ {a} p M M₁)
--   = ⋁ p (rename σ M) (rename α[ rd , rm ] M₁)
--   where rd : {b : Type} → b ∈ (a ∷ Ω′ disc) → b ∈ (a ∷ Ω disc)
--         rd car = car
--         rd (cdr p₁) = cdr (rename-disc σ p₁)
--         rm : {b : Type} → b ∈ Ω′ mono → (a ! disc ∷ Ω) ∋ b
--         rm {b} i with rename-mono σ i
--         ... | is disc x = is disc (cdr x)
--         ... | is mono x = is mono x
-- rename σ (lam M) = lam (rename (α-map mono _ σ) M)
-- rename σ (app M M₁) = app (rename σ M) (rename σ M₁)
-- rename σ (box M) = box (rename (α-wipe σ) M)
-- rename σ (letbox M M₁) = letbox (rename σ M) (rename (α-map disc _ σ) M₁)

-- -- rename σ (var x) = var (σ x)
-- -- rename {Ω}{Ω′} σ (fix {type = l} p e) = fix p (rename σ′ e)
-- --   where σ′ : (l ! mono ∷ Ω) ⊢α (l ! mono ∷ Ω′)
-- --         σ′ (is disc x) = {!σ (is disc x)!}
-- --         σ′ (is mono car) = is mono car
-- --         σ′ (is mono (cdr x₁)) = {!σ (is mono x₁)!}
-- -- rename σ (ε proof) = {!!}
-- -- rename σ (vee x e e₁) = {!!}
-- -- rename σ ⟨ e , e₁ ⟩ = {!!}
-- -- rename σ (π left e) = {!!}
-- -- rename σ (bool x) = {!!}
-- -- rename σ (if e e₁ e₂) = {!!}
-- -- rename σ (when x e e₁) = {!!}
-- -- rename σ (singleton e) = {!!}
-- -- rename σ (⋁ x e e₁) = {!!}
-- -- rename σ (lam e) = {!!}
-- -- rename σ (app e e₁) = {!!}
-- -- rename σ (box e) = {!!}
-- -- rename σ (letbox e e₁) = {!!}


---------- Substitutions ----------

-- lift-mono : {Ω : Env} {Γ : List Type} {a : Type}
--             → Ω ⊢ a
--             → (proj₁ Ω , proj₂ Ω ++ Γ) ⊢ a
-- lift-mono (var (is disc x)) = var (is disc x)
-- lift-mono (var (is mono x)) = var (is mono (extend∈ᵣ _ x))
-- lift-mono (fix p e) = fix p (lift-mono e)
-- lift-mono (ε p) = ε p
-- lift-mono (vee p e₁ e₂) = vee p (lift-mono e₁) (lift-mono e₂)
-- lift-mono ⟨ e₁ , e₂ ⟩ = ⟨ lift-mono e₁ , lift-mono e₂ ⟩
-- lift-mono (π dir e) = π dir (lift-mono e)
-- lift-mono (bool x) = bool x
-- lift-mono (if e e₁ e₂) = if (lift-mono e) (lift-mono e₁) (lift-mono e₂)
-- lift-mono (when p e e₁) = when p (lift-mono e) (lift-mono e₁)
-- lift-mono (singleton e) = singleton e
-- lift-mono (⋁ p e e₁) = ⋁ p (lift-mono e) (lift-mono e₁)
-- lift-mono (lam e) = lam (lift-mono e)
-- lift-mono (app e e₁) = app (lift-mono e) (lift-mono e₁)
-- lift-mono (box e) = box e
-- lift-mono (letbox e e₁) = letbox (lift-mono e) (lift-mono e₁)

-- unwipe : {Ω : Env} {a : Type} → wipe Ω ⊢ a → Ω ⊢ a
-- unwipe = lift-mono

-- _⊢*₁_ : Env → List Type → Set
-- Ω ⊢*₁ [] = ⊤
-- Ω ⊢*₁ (a ∷ Γ) = (Ω ⊢ a) × (Ω ⊢*₁ Γ)
-- -- An interesting possible alternative:
-- -- Ω ⊢*₁ Γ = {a : Type} → (a ∈ Γ) → Ω ⊢ a

-- subst₁ : {Ω : Env} {Γ : List Type} {a : Type}
--        → Ω ⊢*₁ Γ → a ∈ Γ → Ω ⊢ a
-- subst₁ (a , _) car = a
-- subst₁ (_ , rest) (cdr x) = subst₁ rest x

-- -- I'm not sure this definition of substitution is correct.
-- _⊢*_ : Env → Env → Set
-- Ω ⊢* (Ψ , Γ) = (wipe Ω ⊢*₁ Ψ) × (Ω ⊢*₁ Γ)

-- weaken-mono* : {Ω Ω′ : Env} {a : Type}
--              → Ω ⊢* Ω′ → (a ! mono ∷ Ω) ⊢* Ω′
-- weaken-mono* {Ω′ = _ , []} (ψ* , tt) = ψ* , tt
-- weaken-mono* {Ω′ = _ , x ∷ Γ} (ψ* , a , γ*) = ψ* , ({!!} , {!!})

-- subst-var : {Ω₁ Ω₂ : Env} {a : Type}
--           → Ω₁ ⊢* Ω₂ → Ω₂ ∋ a → Ω₁ ⊢ a
-- subst-var ω (is disc x) = unwipe (subst₁ (proj₁ ω) x)
-- subst-var ω (is mono x) = subst₁ (proj₂ ω) x

-- subst : {Ω₁ Ω₂ : Env} {a : Type}
--       → Ω₂ ⊢* Ω₁ → Ω₁ ⊢ a
--       → Ω₂ ⊢ a
-- subst ω (var x) = subst-var ω x
-- subst ω (fix p e) =
--   -- ugh
--   fix p (subst {!!} e)
-- subst ω (ε p) = ε p
-- subst ω (vee p e₁ e₂) = vee p (subst ω e₁) (subst ω e₂)
-- subst ω ⟨ e , e₁ ⟩ = ⟨ subst ω e , subst ω e₁ ⟩
-- subst ω (π left e) = π left (subst ω e)
-- subst ω (bool x) = bool x
-- subst ω (if e e₁ e₂) =
--   if {!!} (subst ω e₁) (subst ω e₂)
-- subst ω (when p e e₁) = when p (subst ω e) (subst ω e₁)
-- subst ω (singleton e) = singleton {!!}
-- subst ω (⋁ p e e₁) = ⋁ p (subst ω e) (subst {!!} e₁)
-- subst ω (lam e) = lam (subst {!!} e)
-- subst ω (app e e₁) = app (subst ω e) (subst ω e₁)
-- subst ω (box e) = box {!!}
-- subst ω (letbox e e₁) = letbox (subst ω e) (subst {!!} e₁)


---------- Derivatives ----------
-- record ChangeType (t : Type) : Set where
--   field
--     Δt : Type
--     nil : ∅ ⊢ t [→] Δt
--     _⊕_ : ∅ ⊢ t [→] (Δt [→] t)

-- change : (t : Type) → ChangeType t
-- change tNat = record
--   { Δt = tNat
--   ; nil = lam (var (is mono car))
--   ; _⊕_ = lam (lam (var (is mono (cdr car)))) }
-- change tBool = record
--   { Δt = tBool
--   ; nil = lam (bool false)
--   ; _⊕_ = lam (lam (vee refl (var (is mono car))
--                              (var (is mono (cdr car))))) }
-- change (tSet t) = record
--   { Δt = tSet t
--   ; nil = lam (ε refl)
--   ; _⊕_ = lam (lam (vee refl (var (is mono car))
--                              (var (is mono (cdr car))))) }
-- change (□ t) = record
--   { Δt = {!!}
--   ; nil = {!!}
--   ; _⊕_ = {!!} }
-- change (a [→] b) = record
--   { Δt = □ a [→] ChangeType.Δt Δa [→] ChangeType.Δt Δb
--   ; nil = lam (lam (lam {!!}))
--   ; _⊕_ = {!!} }
--   where Δa = change a
--         Δb = change b
-- change (t [x] t₁) = {!!}
-- change (t [+] t₁) = {!!}
