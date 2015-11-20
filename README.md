# Datafun

    types           A,B ::= ℕ | A × B | A → B | L ↝ M | FS A
    lattice types   L,M ::= ℕ | L × M | A → L | L ↝ M | FS A
    expressions     e   ::= x | λx.e | λ^x.e | e₁ e₂
                          | (e₁, e₂) | πᵢ e
                          | ∅ | e₁ ∨ e₂
                          | {e} | let x ∈ e₁ in e₂

NB. Lattice types are a syntactic restriction of types.

Alternative, two-layer formulation:

    types           A,B ::= U L | A × B | A → B
    lattice types   L,M ::= F A | ℕ | L × M | A → L | L ↝ M
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
