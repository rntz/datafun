In this note, I'll look at self-maintainable functions via the lens of linearity. 

We define a *change structure* as a triple (A ∈ Poset, ΔA ∈ Poset, ↝ ⊆ ΔA × A × A) 
and write da : a ↝ a' to mean that da is a valid change sending a to a'. 

A morphism between change structures f : (A, ΔA, ↝) → (B, ΔB, ↝) is 
a monotone function f : A → B such that there exists a monotone map 

   df : □A → ΔA → ΔB

with the property that for all a, a' and da such that 

   if da : a ↝ a' then df a da : f a ↝ f a' 

These derivatives are not *self-maintainable*, which means that the
value of a change can depend upon the particular point a. This is 
generally bad for efficient updates; we want self-maintainable 
functions when we can get them. 

To get them, let's run with the analogy between incremental 
lambda calculus and regular calculus. In regular calculus, a 
linear function is a function with a constant derivative. 

Therefore, we will say that a morphism f : (A, ΔA, ↝) → (B, ΔB, ↝)
between change structures is *linear* when there exists a monotone map

   df : ΔA → ΔB

with the property that for all a, a' and da such that 

   if da : a ↝ a' then df da : f a ↝ f a' 

Note that this is precisely the property of self-maintainability;
we can turn any linear morphism into a a regular morphism by writing
a function which ignores the base point. 

Since we used the word linear, the logical thing to do is to see if
change structures with linear maps form a *monoidal* closed category.

1. First, let's define the monoidal unit as

   I ≜ (1, 1, {(), (), ()})

This is obviously a change structure. 


2. Let's define the monoidal product as:

   (A, ΔA, ↝_A) ⊗ (B, ΔB, ↝_B) 

   as 

   (A × B, ΔA × ΔB, ↝)

   where we say

   (da, db) : (a,b) ↝ (a',b') 

   just when da : a ↝ a' and db : b ↝ b'. 

   The associator and unitor maps are the obvious thing, and are
   also obviously linear.

3. The interesting case is the linear function space. Let's define

   > (A, ΔA, ↝_A) ⊸ (B, ΔB, ↝_B) 

   as 

   > (A → B, ΔA → ΔB, ↝_{A ⊸ B})

   with 

   > df : f ↝ f' at A ⊸ B 

   just when 

   > for all a,a',da'. if da : a ↝ a' then df da : f a ↝ f' a'

  We will show this is a correct monoidal exponential by showing
  that Lin(A ⊗ B, C) ≃ Lin(A, B ⊸ C) via the usual currying/uncurrying maps. 

  a. From left to right: 

     Assume  f ∈ Lin(A ⊗ B, C). Then f : A × B → C and there
     is a df : ΔA × ΔB → ΔC such that if (da,db) : (a,b) ↝ (a',b') 
     then df (da,db) : f (a,b) ↝ f (a',b'). 

     We want to show that curry(f) ∈ Lin(A, B ⊸ C). This satisfies the
     object part trivially, and we will choose curry(df) as the witness
	 of linear differentiability. 

     So we have to show that for all da : a ↝ a', curry(df) da : curry(f) a ↝ curry(f) a'. 
     Assume da : a ↝ a'. 
     Now we want to show curry(df) da : curry(f) a ↝ curry(f) a' at B ⊸ C. 
     So we want to show that for all db : b ↝ b', curry(df) da db : curry(f) a b ↝ curry(f) a' b' at C. 
     Assume db : b ↝ b'. 
     We want to show: curry(df) da db : curry(f) a b ↝ curry(f) a' b' at C. 
     Now, note that since da : a ↝ a' and db : b ↝ b', we have (da,db) : (a,b) ↝ (a',b'). 
     Therefore we know that df (da,db) : f (a,b) ↝ f (a',b'). 
     By the definition of curry(-), curry(df) da db : curry(f) a b ↝ curry(f) a' b' at C.

  b. From right to left. 

     Assume f ∈ Lin(A, B ⊸ C). Then f : A → B → C and there
     is a df : ΔA → ΔB → ΔC such that if da : a ↝ a'
     then df da : f a ↝ f a' at B ⊸ C. 

     We want to show that uncurry(f) ∈ Lin(A ⊗ B, C). 

	 So we want to show uncurry(f) : A × B → C and there
     is a dg : ΔA × ΔB → ΔC such that if (da,db) : (a,b) ↝ (a',b') 
     then dg (da,db) : f (a,b) ↝ f (a',b'). 

     That uncurry(f) : A × B → C is trivial. 

     We choose uncurry(df) as the existential witness, so we need
	 to show that  if (da,db) : (a,b) ↝ (a',b') 
     then uncurry(df) (da,db) : f (a,b) ↝ f (a',b'). 

     Assume (da,db) : (a,b) ↝ (a',b'). 
     Therefore da : a ↝ a'. 
     Therefore db : b ↝ b'. 

     Hence we know that df da : f a ↝ f a' at B ⊸ C. 
     Therefore, for all b, b', db. if db : b ↝ b', then df da db : f a b ↝ f a' b'. 
     Hence df da db : f a b ↝ f a' b'. 
     By the definition of uncurry(-), uncurry(df) (da,db) : f (a,b) ↝ f (a',b'). 

As a result we have a natural isomorphism between the hom-sets, and so
change structures and linear (i.e., self-maintainable) functions form
a SMCC – i.e., a model of linear logic.
    
This fact is a curiosity, unless we can find an adjunction between
ΔPoset and Lin.  If we can, then we can use adjoint calculus trickery
to get a syntax for the language.

So, let's try. The obvious functor from Lin to ΔPoset is the inclusion
functor. 

We define 

  > G (A, ΔA, ↝) = (A, ΔA, ↝)
  > G (f : (A, ΔA, ↝) → (B, ΔB, ↝)) = f 

This is well-defined, since for each f, we can find an ordinary derivative
for it by taking f's linear derivative df : ΔA → ΔB and producing
the ordinary derivative 

  > dg ≜ λ(a, da). df da 

Next, we need a functor which is left adjoint to this one to get the 
structure we need for this to be a model of the LNL calculus. 

Let's try:
   
   > F(X, ΔX, ↝)  = (X, □X × ΔX, ⇒)

where 

   > (x₀, dx) : x ⇒ x'  when  x = x₀ and dx : x ↝ x' 

The idea is to make an ordinary change morphism "trivially linear" by
augmenting the type of changes to carry along the values that they
are changes for. To show this works, let's first look at the functorial
action:

   > F(f : (X, ΔX, ⇒) → (Y, ΔY, ↝)) = f 

Given a ΔPoset morphism f : (X, ΔX, ↝) → (Y, ΔY, ↝), we want to find
a Lin morphism F(f) : F(X, ΔX, ↝) → F(Y, ΔY, ↝). This means we need
to find a map 

    dg : □X × ΔX → □Y × ΔY

such that for every (x₀, dx) : x ⇒ x' at F(X), we have 
dg(x₀, dx) : f x ↝ f x' at F(Y).

Since f is a ΔPoset morphism, we have a df : □X × ΔX → ΔY such that
for every dx : x ⇒ x', df x dx : f x ↝ f x'. 

So we can now define dg ≜ <(π₁; □f), df> = λ(x,dx). (f x, df(x, dx)). 

Now we need to check that for every (x₀, dx) : x ⇒ x' at F(X), we have 
dg(x₀, dx) : f x ↝ f x' at F(Y).

Assume (x₀, dx) : x ⇒ x' at F(X). 
Therefore x₀ = x and dx : x ⇒ x' at X. 
We want to show that dg(x₀, dx) : f x ↝ f x'
By definition, dg(x₀, dx) = (f x, df(x, dx)). 
The properties of df tells us that df(x, dx) : f x ↝ f x' at Y. 
Hence (f x, df(x, dx)) : f x ↝ f x' at F(Y).
Hence dg(x₀, dx) : f x ↝ f x'

So this actually produces elements of 

Now, we can check whether

   Lin(F(X), A) ≃? ΔPoset(X, G(A))

We will take the witnessing isomorphism to be the
identity on elements of the hom-sets. To make sure this
works, we just need to check differentiability. 
vc
* Left to right: 
  
  Assume f ∈ Lin(F(X), A). 
  Therefore f : X → A. 
  Furthermore, there is a df : □X × ΔX → ΔA such that 
  for all for all (x₀, dx) : x ↝ x', we have df (x₀, dx) : f x ↝ f x'. 
  
  We want to show that f ∈ ΔPoset(X, G(A))
  We need a dg such that for all x, x' and dx such that 
  if dx : x ↝ x' then dx x dx : f x ↝ f x'. 
  
  We can take dg to be uncurry(df). 
  Now, assume that dx : x ↝ x' at X. 
  Therefore we know that (x, dx) : x ↝ x' at F(X). 
  Therefore df (x, dx) : f x ↝ f x'. 
  But by the definition of uncurry(-), we know uncurry(df) x dx : f x ↝ f x'. 
  
* Right to left: 

  Assume f ∈ ΔPoset(X, G(A))
  Therefore f : X → A. 
  Furthermore, we have a df such that 
  for all for all dx : x ↝ x', we have df x dx : f x ↝ f x'. 

  We want to show f ∈ Lin(F(X), A). 
  So we need a dg : □X × ΔX → ΔA such that 
  for all for all (x₀, dx) : x ↝ x' at F(X), we have dg (x₀, dx) : f x ↝ f x' at A. 

  Take dg to be curry(df). 
  Assume (x₀, dx) : x ↝ x' at F(X). 
  Hence x₀ = x and dx : x ↝ x' at X. 
  Therefore df x dx : f x ↝ f x' at A. 
  By the definition of curry(-). df x dx = curry(df) (x, dx). 
  So curry(df) (x, dx) : f x ↝ f x' at A. 
  So curry(df) (x₀, dx) : f x ↝ f x' at A. 

This shows that there is a linear/nonlinear adjunction between the
categories of self-maintainable and non-self-maintainable incremental 
functions. 
