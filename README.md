# Datafun

    types           A,B ::= ℕ | A × B | A → B | L ↝ M | FS A
    lattice types   L,M ::= ℕ | L × M | A → L | L ↝ M | FS A
    expressions     e   ::= x | λx.e | λ^x.e | e₁ e₂
                          | (e₁, e₂) | πᵢ e
                          | ∅ | e₁ ∨ e₂
                          | {e} | let x ∈ e₁ in e₂
                          | fix x. e

    contexts        Δ   ::= · | Δ,x:A
    monotone ctxts  Γ   ::= · | Δ,x:L

## Semantic intuition

Semantics of types, in brief:

- `ℕ`, `A × B`, and `A → B` all mean what you'd expect.

- So called "lattice types" `L` represent *unital semilattices* ─ that is,
  semilattices with a least element. Lattice types are simply a syntactic
  restriction of ordinary types: any lattice type is a type, but not all types
  are lattice types.

- The lattice type `FS A` represents *finite sets of `A`s*, with union as
  lattice join and ∅ as least element. This is how we represent datalog
  predicates; a predicate is a finite set of tuples.

- The lattice type `A → L` represents functions mapping `A` into `L`. The
  lattice join operation is pointwise; the least element is `λx.∅`, where `∅` is
  the least element of `L`.

- The lattice type `L ↝ M` represents *monotone functions* from `L` to `M`.
  These form a unital semilattice in the same way as ordinary functions.

Semantics of expressions, in brief:

- `x`, `λx.e`, `(e₁, e₂)`, and `πᵢ e` all do what you'd expect.

- `λ^x.e` is a *monotone lambda*, with type `L ↝ M` for appropriate `L`, `M`.
  That is, its body `e` must be *monotone* in `x`; this is enforced by the type
  system.

- `e₁ e₂` is function application ─ ordinary *or* monotone. In a language
  without quantified types, inferring which application is intended is easy.
  (With quantifiers, maybe it isn't. Future work!)

- `∅` represents the least element of a lattice type.

- `e₁ ∨ e₂` represents lattice join.

- `{e}` represents the singleton set containing `e`.

- `let x ∈ e₁ in e₂` is set-comprehension. `e₁` must have a finite set type;
  `e₂` must have a lattice type. For each `x` in `e₁`, we compute `e₂`; then we
  lattice-join together all values of `e₂` computed this way, and that is our
  result. This generalizes the "bind" operation of the finite-set monad.

- `fix x.e` finds the least-fixed-point of the monotone expression `e`. We can
  only find fixed-points at certain types; which types exactly is an open
  question. We know how to do it at least for `ℕ` and for `FS A` where A is an
  equality type. Finding least-fixed-points of finite-set-typed expressions is
  precisely Datalog-style recursion.

## Typing judgment: `Δ;Γ ⊢ e : A`

Our typing judgment is `Δ;Γ ⊢ e : A`

We call `Δ` our *unrestricted* context and `Γ` our *monotone* context.

There is an implicit restriction: Γ may only be nonempty if `A` is a lattice
type `L`. (This is effectively the same as having two judgments: `Δ ⊢ e : A` and
`Δ;Γ ⊢ e : L`, where `Δ ⊢ e : L` is implicitly equivalent to `Δ;· ⊢ e : L`.)

Both contexts obey the usual intuitionistic structural rules (weakening,
exchange). There is one additional (albeit rather useless) structural rule:

    Δ; Γ,x:L ⊢ e : M
    ---------------- forget
    Δ,x:L; Γ ⊢ e : M

Read forward, this says that if `e` *is* monotonic in `x`, then we may forget
this fact and treat it as if it is unrestricted in `x`. Read backward, this says
we may freely choose to bind ourselves to using an unrestricted variable only
monotonically within a subterm.

### Typing rules

     Δ,x:A; Γ ⊢ e : B      Δ; Γ,x:L ⊢ e : M
    ------------------    -------------------
    Δ;Γ ⊢ λx.e : A → B    Δ;Γ ⊢ λ^x.e : L ↝ M

    Δ;Γ ⊢ e₁ : A → B   Δ;· ⊢ e₂ : A
    -------------------------------- app
           Δ;Γ ⊢ e₁ e₂ : B

    Δ;Γ ⊢ e₁ : L ↝ M   Δ;Γ ⊢ e₂ : L
    ------------------------------- app^
           Δ;Γ ⊢ e₁ e₂ : M

NB. The monotone context of `e₂` in the rule `app` for applying ordinary
functions must be empty! Since `A → B` represents an *arbitrary* function, we
cannot rely on its output being monotone in its argument. Thus its argument must
be, not *monotone* relative to our current Γ, but *constant*.

                     Δ;Γ ⊢ eᵢ : L
    -----------    -----------------
    Δ;Γ ⊢ ∅ : L    Δ;Γ ⊢ e₁ ∨ e₂ : L

      Δ;Γ ⊢ e : A       Δ;Γ ⊢ e₁ : FS A   Δ,x:A; Γ ⊢ e₂ : L
    ----------------    -----------------------------------
    Δ;Γ ⊢ {e} : FS A        Δ;Γ ⊢ let x ∈ e₁ in e₂ : L

    Δ; Γ,x:L ⊢ e : L
    ----------------- fix
    Δ;Γ ⊢ fix x.e : L

The last rule, for `fix`, is overly permissive as stated; it needs to be
restricted to some computationally tractable class of lattice types.

# Two-layer formulation
Alternative, two-layer formulation:

    types           A,B ::= U L | A × B | A → B
    lattice types   L,M ::= F A | L × M | A → L | L ↝ M
                          | ℕ
    expressions     e   ::= x | λx.e | e₁ e₂
                          | (e₁, e₂) | πᵢ e
                          | U u
    lattice exprs   u   ::= x | λ^x.u | u₁ u₂
                          | λx.u | u e
                          | (u₁, u₂) | πᵢ u
                          | ∅ | u₁ ∨ u₂
                          | {e} | let x ∈ u₁ in u₂
                          | U⁻¹ e

    Δ;· ⊢ u : L               Δ ⊢ e : U L
    -------------           ---------------
    Δ ⊢ U u : U L           Δ;Γ ⊢ U⁻¹ e : L

NB. In this presentation, `FS` comes apart into `F` and `U`. `U` is the
*underlying* functor; given a semilattice, it gives the type of its underlying
values. `F` is the *free* functor: given a type `A` it produces the free unital
semilattice on `A`, which is to say, finite sets of `A`s under union.
