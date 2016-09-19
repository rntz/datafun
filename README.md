# FILES

`paper/`: ICFP 2016 paper.

`src/`: Implementation of Datafun in Racket. `src/repl.rkt` is most useful.

What follows is an *extremely* out-of-date description of Datafun's type theory.
For more up-to-date information,
[here's a paper preprint](http://www.rntz.net/files/datafun.pdf); or you can
clone the repository and run `make` in the `paper/` directory to produce
`datafun.pdf`.

# Datafun

    poset types     A,B ::= bool | nat | A × B | A → B | A →⁺ B | Set A | A + B
    lattice types   L,M ::= bool | nat | L × M | A → L | A →⁺ L | Set A
    expressions     e   ::= x | λx.e | e e
                          | (e, e) | πᵢ e
                          | true | false | if e then e else e
                          | inᵢ e | case e of in₁ x → e; in₂ x → e
                          | ∅ | e ∨ e | {e} | ⋁(x ∈ e) e
                          | fix x. e

    contexts        Δ   ::= · | Δ,x:A
    monotone ctxts  Γ   ::= · | Γ,x:A

## Semantic intuition

Types correspond to *partially ordered sets* (posets):

- `bool` is booleans; `false` < `true`.

- `nat` is the naturals, ordered 0 < 1 < 2 < ...

- `A × B` is pairs, ordered pointwise:
  `(a₁,b₁) ≤ (a₂,b₂)` iff `a₁ ≤ a₂` and `b₁ ≤ b₂`.

- `A + B` is sums, ordered disjointly. `in₁ a₁ ≤ in₁ a₂` iff `a₁ ≤ a₂`, and
  likewise for `in₂`; but `in₁ a` and `in₂ b` are not comparable to one another.

- `Set A` is *finite* sets of `A`s, ordered by inclusion:
  `x ≤ y` iff `∀(a ∈ x) a ∈ y`.

- `A → B` are functions, ordered pointwise: `f ≤ g` iff `∀(x : B) f x ≤ g x`.

- `A →⁺ B` are *monotone* functions; for any `f : A →⁺ B`, given `x,y : A` such
  that `x ≤ y` we know that `f x ≤ f y`. The type system enforces this
  monotonicity. Monotone functions are ordered pointwise, just like regular
  functions.

Lattice types `L` are a subset of all types, defined so that every lattice type
happens to be *unital semilattices* (usls) — that is, join-semilattices with a
least element. Any lattice type is a type, but not all types are lattice types.

Semantics of expressions, in brief:

- `x`, `(e₁, e₂)`, `πᵢ e`, `inᵢ e`, `if`, `true`, `false`, and `case` all do
  what you'd expect.

- `λx.e` and `e e` both do what you'd expect. However, it is left ambiguous
  whether they represent ordinary or monotone function creation/application.

  One could of course require the programmer to write ordinary and monotone
  functions differently (or even ordinary and monotone function *applications*
  differently). But for our purposes it's simplest to just give two typing rules
  (ordinary and monotone) for `λx.e` (and likewise `e e`).

  It is definitely possible to infer monotonicity in a bidirectional way, and
  possibly even in a Damas-Milner-ish way, but that's outside the scope of this
  README.

- `∅` represents the least element of a lattice type.

- `e₁ ∨ e₂` represents the least upper bound ("lattice join") of `e₁` and `e₂`.

- `{e}` represents the singleton set containing `e`.

- `⋁(x ∈ e₁) e₂` is set-comprehension. `e₁` must have a finite set type; `e₂`
  must have a lattice type. For each `x` in `e₁`, we compute `e₂`; then we
  lattice-join together all values of `e₂` computed this way, and that is our
  result. This generalizes the "bind" operation of the finite-set monad.

- `fix x. e` finds the least fixed-point of the monotone function `λx. e`.

## Typing judgment: `Δ;Γ ⊢ e : A`

Our typing judgment is `Δ;Γ ⊢ e : A`

We call `Δ` our *unrestricted* context and `Γ` our *monotone* context. Both
contexts obey the usual intuitionistic structural rules (weakening, exchange).

### Typing rules

     Δ,x:A; Γ ⊢ e : B       Δ;Γ ⊢ e₁ : A → B   Δ;· ⊢ e₂ : A
    ------------------ λ    -------------------------------- app
    Δ;Γ ⊢ λx.e : A → B             Δ;Γ ⊢ e₁ e₂ : B

     Δ; Γ,x:A ⊢ e : B       Δ;Γ ⊢ e₁ : A →⁺ B   Δ;Γ ⊢ e₂ : A
    ------------------- λ⁺  --------------------------------- app⁺
    Δ;Γ ⊢ λx.e : A →⁺ B            Δ;Γ ⊢ e₁ e₂ : B

NB. The monotone context of `e₂` in the rule `app` for applying ordinary
functions must be empty! Since `A → B` represents an *arbitrary* function, we
cannot rely on its output being monotone in its argument. Thus its argument must
be, not *monotone* in Γ, but *constant*.

The typing rules for tuples, sums, and booleans are *mostly* boring:

        Δ;Γ ⊢ eᵢ : Aᵢ            Δ;Γ ⊢ e : A₁ × A₂
    -----------------------      ------------------
    Δ;Γ ⊢ (e₁,e₂) : A₁ × A₂       Δ;Γ ⊢ πᵢ e : Aᵢ

                                           Δ;Γ ⊢ e : bool    Δ;Γ ⊢ eᵢ : A
    -----------------  ------------------  -------------------------------
    Δ;Γ ⊢ true : bool  Δ;Γ ⊢ false : bool  Δ;Γ ⊢ if e then e₁ else e₂ : A

        Δ;Γ ⊢ e : Aᵢ
    ---------------------
    Δ;Γ ⊢ inᵢ e : A₁ + A₂

However, there are *two* eliminators for sum types:

TODO

The typing rules get more interesting now:

                     Δ;Γ ⊢ eᵢ : L
    -----------    -----------------
    Δ;Γ ⊢ ∅ : L    Δ;Γ ⊢ e₁ ∨ e₂ : L

      Δ;· ⊢ e : A        Δ;Γ ⊢ e₁ : Set A  Δ,x:A; Γ ⊢ e₂ : L
    -----------------    ------------------------------------
    Δ;Γ ⊢ {e} : Set A          Δ;Γ ⊢ ⋁(x ∈ e₁) e₂ : L

    Δ; Γ,x:L ⊢ e : L   L equality
    ----------------------------- fix
          Δ;Γ ⊢ fix x.e : L

In the last rule, for `fix`, the premise `L equality` means that the type `L` at
which the fixed-point is computed must have decidable equality.

# Two-layer formulation
Alternative, two-layer formulation:

    set types       A,B ::= U P | A ⊗ B | A ⊕ B | A ⊃ B
    poset types     P,Q ::= bool | nat | P × Q | P →⁺ Q | Set A
                          | Disc A | P + Q
    lattice types   L,M ::= bool | nat | L × M | P →⁺ M | Set A
    expressions     e   ::= x | λx.e | e e | (e, e) | πᵢ e
                          | inᵢ e | case e of in₁ x → e; in₂ x → e
                          | U u
    lattice exprs   u   ::= x | λx.u | u u | (u, u) | πᵢ u
                          | ∅ | u ∨ u | {e} | ⋁(x ∈ u) u
                          | fix x. u
                          | D e | U⁻¹ e | let D x = u in u

    Δ;· ⊢ u : P               Δ ⊢ e : U P
    ------------- U         --------------- U⁻¹
    Δ ⊢ U u : U P           Δ;Γ ⊢ U⁻¹ e : P

      Δ ⊢ e : A             Δ;Γ ⊢ u₁ : D A   Δ,x:A; Γ ⊢ u₂ : P
    --------------- D       ----------------------------------- let-D
    Δ;Γ ⊢ D e : D A            Δ;Γ ⊢ let D x = u₁ in u₂ : P

I use `⊗` and `⊕` for set types not because they are linear, but simply to
distinguish them from the `×` and `+` operations on *poset* types.

This version needs to be fleshed out more fully. In particular, we need some
axioms to ensure that `U (P + Q) = U P ⊕ U Q`.
