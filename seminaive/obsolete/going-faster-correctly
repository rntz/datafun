We might call our transformation "type-directed derivative-passing style".

# Changes to fast things are nothing new

types A = 2 | {A} | A + B | A × B | A → B | □A

Let Δ' = the original Δ for the derivative translation.
(TODO: rename Φ,Δ.)

**Theorem**: ΔA = Δ'ΦA (TODO: prove, inductively on types)

So we don't _need_ to define Δ directly at all! But it's useful for expository purposes.

## Proof sketch

Δ(A → B)  = □ΦA → ΔA → ΔB
Δ'(A → B) = □A → Δ'A → Δ'B
Δ'(Φ(A → B)) = Δ'(ΦA → ΦB) = □ΦA → Δ'ΦA → Δ'ΦB

Φ{A} = {ΦA}
Δ{A} = {ΦA}
Δ'{A} = {A}

Δ□A = □ΔA               Δ'□A = □Δ'A
Δ(A × B) = ΔA × ΔB      Δ'(A × B) = Δ'A × Δ'B
Δ(A + B) = ΔA + ΔB      Δ'(A + B) = Δ'A + Δ'B
Δ2 = Δ'2 = 2

# logical relations approach
RA ⊆ A × ΦA

x,y ∈ R2                when    x = y
(a,x),(b,y) ∈ R(A×B)    when    a,b ∈ RA and x,y ∈ RB
inᵢ x, inᵢ y ∈ R(A₁+A₂) when    x,y ∈ RAᵢ
[x], [y,dy] ∈ R□A       when    x,y ∈ RA and y ↝[dy] y : ΦA
f, g ∈ R(A → B)         when    ∀(x,y ∈ RA) f x, g y ∈ RB
s, t ∈ R{A} when ∃ a bijection (f : s → t) such that f ⊆ RA

Sets are a little confusing. Originally I wrote:

s, t ∈ R{A}             when    (∀x∈s.∃y∈t. x,y∈RA) and (∀y∈t.∃x∈s. x,y∈RA)

However, this suffers from a duplicates problem: Can we have {x},{y,z} ∈ R{A} where x,y ∈ RA and x,z ∈ RA? Can we prove that this implies y = z? I don't think so - we can put boxed things in sets, and there multiple valid zero changes for a given value (eg. {} and {1} are both zero-changes for {1})!

And this is a genuine problem if, say, we have a primitive function (size : {A} → ℕ)! So, our logical relation for sets needs to be a bit more careful. Hence the bijection.

## TO SHOW: Adequacy
If Ψ;Γ ⊢ e : A
(implying ΦΨ,ΔΨ;ΦΓ ⊢ φe : ΦA
 and      ΦΨ,ΔΨ,ΦΓ;ΔΓ ⊢ δe : ΔA)
then e,φe ∈ R(Ψ;Γ ⊢ A)

(e,φe) ∈ R(Ψ;Γ ⊢ A) iff:
  ∀(ψ : Ψ, φψ : ΦΨ, δψ : ΔΨ) [ψ],[φψ,δψ] ∈ R□Ψ →
  ∀(γ : Γ, φγ : ΨΓ) γ,φδ ∈ RΓ →
  e{ψ;γ}, φe{φψ,δψ;φγ} ∈ RA

Strategy: induction over Ψ;Γ ⊢ e : A?

Most cases should be easy, because φ just distributes.

### Case φ[e] = [φe,δe]
WTS: [e]{ψ;γ}, [φe,δe]{φψ,δψ;φγ} ∈ R□A
ie: [e{ψ;}], [φe{φψ,δψ;},δe{φψ,δψ;}] ∈ R□A
ie: e{ψ;}, φe{φψ,δψ;} ∈ RA                  (1)
and φe{φψ,δψ;} ↝[δe{φψ,δψ;}] φe{φψ,δψ;}     (2)

First by IH, second by lemma for δ.

## Adequacy for δ (mutually inductive w/ Adequacy)
If   ψ ↝[δψ] ψ and γ₁ ↝[δγ] γ₂
then φe{ψ,δψ;γ₁} ↝[δe{ψ,δψ,γ₁;δγ}] φe{ψ,δψ;γ₂}

The cases for this will actually be interesting. Can we reuse the semantic proof involving ΔPoset?


# elab/forget approach

_⊝_ : A → A → ΔA
x ⊝ y only defined when y ≤ x
(x ⊝ y)_2 = x
(x ⊝ y)_{A} = x ∖ y
((x,y) ⊝ (x',y')) = (x ⊝ x', y ⊝ y')
(inᵢ x ⊝ inᵢ y) = inᵢ (x ⊝ y)
[x] ⊝ [y] = [zero x]
(f ⊝ g)_{A → B} = λx dx. f (x ⊕ dx) ⊝ g x

zero : A → ΔA
zero x = x ⊝ x

elab : A → ΦA
elab (x : 2) = x
elab (x : {A}) : {ΦA} = {elab a | a ∈ x}
elab (x,y) = (elab x, elab y)
elab (inᵢ x) = inᵢ (elab x)
elab (f : A → B): ΦA → ΦB = forget . f . elab
elab ([x] : □A) : □(ΦA × ΔA) = [elab x, zero x]

forget : ΦA → A
forget (x : 2) = x
forget (x : {ΦA}) = {forget a | a ∈ x}
forget ([x,dx] : □(ΦA × ΔA)): □A = [forget x]
forget (x,y) = (forget x, forget y)
forget (inᵢ x) = inᵢ (forget x)
forget (f : ΦA → ΦB) = elab . f . forget

----------
LEMMA: elab;forget = id.

Note the other direction (id = forget;elab) is not true, because ΦA can contain "invalid" values, for example:

φ□A = □(φA × ΔA)
^ intended invariant: the ΔA is a zero change ^

SOUNDNESS THEOREM is something like:
- forget φM = M
- φM = elab M


split : □(A + B) → □A + □B

φsplit : φ□(A + B) → φ(□A + □B)

φsplit : □((φA + φB) × (ΔA + ΔB))
       → □(φA × ΔA) + □(φB × ΔB)

φ□A = □(φA × ΔA)
φ(A + B) = φA + φB
Δ(A + B) = ΔA + ΔB
Δ□A = □ΔA

φ(split e)
= let [x] = φe in
  -- x : (φA + φB) × (ΔA + ΔB)
  split [case x of
    (inᵢ y, inᵢ dy) → inᵢ (y, dy)
    (inᵢ y, _)      → inᵢ (y, dummy y)]

□((φA × ΔA) + (φB × ΔB))
--> □(φA × ΔA) + □(φB × ΔB)


