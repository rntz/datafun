# Datafun

    types           A,B ::= ℕ | A → B | A × B | L ↝ M | FS A
    lattice types   L,M ::= ℕ | L × M | A → L | L ↝ M | FS A
    expressions     e   ::= x | λx.e | λ^x.e | e₁ e₂
                          | (e₁, e₂) | πᵢ e
                          | ∅ | e ∨ e
                          | {e} | let x ∈ e₁ in e₂
