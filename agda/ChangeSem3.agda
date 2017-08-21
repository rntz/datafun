{-# OPTIONS --postfix-projections #-}
module ChangeSem3 where

open import Cast
open import Cat
open import Monads
open import Prelude
open import Prosets
open import TreeSet

-- TODO: This file is taking too long to typecheck. Split it up.

juggle : ∀{i j k l} {A B C D}
       -> Σ {i}{j} A C × Σ {k}{l} B D
       -> Σ (A × B) λ { (a , b) -> C a × D b }
juggle ((a , c) , (b , d)) = (a , b) , (c , d)

isos∧ : ∀{A B} -> isos A ∧ isos B ⇒ isos (A ∧ B)
isos∧ = fun juggle

isos∨ : ∀{A B} -> isos (A ∨ B) ⇒ isos A ∨ isos B
isos∨ .ap = id
isos∨ .map (rel₁ p , rel₁ q) = rel₁ (p , q)
isos∨ .map (rel₂ p , rel₂ q) = rel₂ (p , q)

isojuggle : ∀{A B C D} -> (isos A ∧ B) ∧ (isos C ∧ D) ⇒ isos (A ∧ C) ∧ (B ∧ D)
isojuggle = fun juggle • ∧-map isos∧ id

constant : ∀{A B} -> Obj B -> A ⇒ B
constant {A}{B} x = Fun: (λ _ → x) (λ _ → ident B)

module _ {{A : Proset}} {{Sum : Sums A}} where
  juggle∨ : ∀{a b c d : Obj A} -> (a ∨ b) ∨ (c ∨ d) ≤ (a ∨ c) ∨ (b ∨ d)
  juggle∨ = [ ∨-map in₁ in₁ , ∨-map in₂ in₂ ]

  juggle∨≈ : ∀{a b c d : Obj A} -> (a ∨ b) ∨ (c ∨ d) ≈ (a ∨ c) ∨ (b ∨ d)
  juggle∨≈ = juggle∨ , juggle∨

  ∨≈ : ∀{a b a' b' : Obj A} -> a ≈ a' -> b ≈ b' -> (a ∨ b) ≈ (a' ∨ b')
  ∨≈ a≈a' b≈b' = ∨-map (proj₁ a≈a') (proj₁ b≈b') , ∨-map (proj₂ a≈a') (proj₂ b≈b')


-- Prosets equipped with change structures
record Change : Set1 where
  field {{𝑶}} : Proset          -- O for objects
  field 𝑫 : Proset              -- D for deltas
  object = Obj 𝑶
  delta  = Obj 𝑫

  -- this needs to respect equivalence of objects & deltas, doesn't it? I think
  -- for all the ones we actually construct this will be the case; I'm not sure
  -- if we need it for any of the proofs we're doing.
  field Path : (da : delta) (a b : object) -> Set

  -- This hack is needed to prove Change has coproducts. We need it for the
  -- derivative of case-analysis, [_,_], to invent values to use in the
  -- impossible case branches.
  field dummy : Obj 𝑫

open Change public

 -- Constructions on change structures
data rel3+ {A A' B B' C C' : Set} (R : A -> B -> C -> Set) (S : A' -> B' -> C' -> Set)
           : A ⊎ A' -> B ⊎ B' -> C ⊎ C' -> Set where
  rel₁ : ∀{a b c} -> R a b c -> rel3+ R S (inj₁ a) (inj₁ b) (inj₁ c)
  rel₂ : ∀{a b c} -> S a b c -> rel3+ R S (inj₂ a) (inj₂ b) (inj₂ c)

⊥-change : Change
𝑶 ⊥-change = init
𝑫 ⊥-change = ⊤-proset
Path ⊥-change _ (lift ())
dummy ⊥-change = tt

change-bool : Change
𝑶 change-bool = bools
𝑫 change-bool = bools
Path change-bool da a b = (a ∨ da) ≈ b
dummy change-bool = false

module _ (A B : Change) where
  change× : Change
  𝑶 change× = 𝑶 A ∧ 𝑶 B
  𝑫 change× = 𝑫 A ∧ 𝑫 B
  Path change× (da , db) = rel× (Path A da) (Path B db)
  dummy change× = (dummy A , dummy B)

  change+ : Change
  𝑶 change+ = 𝑶 A ∨ 𝑶 B
  𝑫 change+ = 𝑫 A ∨ 𝑫 B
  Path change+ = rel3+ (Path A) (Path B)
  dummy change+ = inj₁ (dummy A)

  change→ : Change
  𝑶 change→ = 𝑶 A ⇨ 𝑶 B
  𝑫 change→ = (isos (𝑶 A) ∧ 𝑫 A) ⇨ 𝑫 B
  Path change→ df f g = ∀{da a b} (da:a→b : Path A da a b)
                      -> Path B (ap df (a , da)) (ap f a) (ap g b)
  dummy change→ = constant (dummy B)

module _ (A : Change) where
  change□ : Change
  𝑶 change□ = isos (𝑶 A)
  𝑫 change□ = isos (𝑫 A)
  Path change□ da a b = Path A da a b ∧ (a ≈ b)
  dummy change□ = dummy A

  change-tree : Change
  𝑶 change-tree = trees (𝑶 A)
  𝑫 change-tree = trees (𝑶 A)
  Path change-tree da a b = Hom (isos (trees (𝑶 A))) (node a da) b
  dummy change-tree = empty

 -- Morphisms between change structures.
record ChangeFun (A B : Change) : Set where
  constructor cfun
  field func  : 𝑶 A ⇒ 𝑶 B
  field deriv : isos (𝑶 A) ∧ 𝑫 A ⇒ 𝑫 B
  field is-id : Path (change→ A B) deriv func func

  func&deriv : isos (𝑶 A) ∧ 𝑫 A ⇒ isos (𝑶 B) ∧ 𝑫 B
  func&deriv = ⟨ π₁ • map Isos func , deriv ⟩

open ChangeFun public

 -- Category of changes
instance
  changes : Cat _ _
  Obj changes = Change
  Hom changes = ChangeFun
  ident changes = cfun id π₂ id
  compo changes F@(cfun f df fok) (cfun g dg gok) =
    cfun (f • g) (func&deriv F • dg) (fok • gok)

  change-products : Products changes
  _∧_ {{change-products}} = change×
  π₁ {{change-products}} = cfun π₁ (π₂ • π₁) π₁
  π₂ {{change-products}} = cfun π₂ (π₂ • π₂) π₂
  ⟨_,_⟩ {{change-products}} (cfun f df fok) (cfun g dg gok) =
    cfun ⟨ f , g ⟩ ⟨ df , dg ⟩ ⟨ fok , gok ⟩

  change-sums : Sums changes
  _∨_ {{change-sums}} = change+
  in₁ {{change-sums}} = cfun in₁ (π₂ • in₁) rel₁
  in₂ {{change-sums}} = cfun in₂ (π₂ • in₂) rel₂
  [_,_] {{change-sums}} f g .func = [ func f , func g ]
  -- isos (𝑶 a ∨ 𝑶 b) ∧ (𝑫 a ∨ 𝑫 b) ⇒ 𝑫 c
  -- this is the bit where I have to invent values.
  [_,_] {{change-sums}} {A}{B}{C} f g .deriv = uncurry (isos∨ • [ flip [ use f , fail ]
                                                                , flip [ fail , use g ] ])
    where use : ∀{A} -> A ≤ C -> 𝑫 A ⇒ isos (𝑶 A) ⇨ 𝑫 C
          fail : ∀{A B} -> A ⇒ B ⇨ 𝑫 C
          use f = curry (swap • deriv f)
          fail = curry (constant (dummy C))
  [_,_] {{change-sums}} f g .is-id (rel₁ da) = is-id f da
  [_,_] {{change-sums}} f g .is-id (rel₂ db) = is-id g db
  init {{change-sums}} = ⊥-change
  init≤ {{change-sums}} = cfun init≤ (π₁ • Fun: init≤ λ { {lift ()} }) (λ { {_} {lift ()} })

  change-cc : CC changes
  CC.products change-cc = change-products
  _⇨_ {{change-cc}} = change→
  apply {{change-cc}} .func = apply
  -- ((f , a) , (df , da)) ↦ df (a , da)
  -- is there a simpler way to write this? one that typechecks faster?
  -- apply {{change-cc}} .deriv = ⟨ π₂ • π₁ , ⟨ π₁ • ∧isos • π₂ , π₂ • π₂ ⟩ ⟩ • apply
  apply {{change-cc}} .deriv .ap ((f , a) , df , da) = ap df (a , da)
  apply {{change-cc}} .deriv .map (fa≈gb , df≤df' , da≤da') =
    df≤df' (juggle fa≈gb .proj₂ , da≤da')
  apply {{change-cc}} .is-id (df:f→g , dx:x→y) = df:f→g dx:x→y
  curry {{change-cc}} (cfun f df ok) =
    cfun (curry f) (curry (isojuggle • df)) (λ da db → ok (da , db))


-- Showing that □ is a comonad on the category of changes.
Change□ : changes ≤ changes
ap  Change□ = change□
map Change□ (cfun f df ok) =
  cfun (map Isos f) (isos∧ • map Isos df) (∧-map ok (map Isos f .map))

instance
  Change□-comonad : Comonad Change□
  Comonad.dup Change□-comonad .func = dup Isos
  Comonad.dup Change□-comonad .deriv = π₂ • dup Isos
  -- agh.
  Comonad.dup Change□-comonad .is-id p@(da:a→b , a≈b) = p , a≈b , swap {{sets}} a≈b
  Comonad.extract Change□-comonad = cfun (extract Isos) (π₂ • extract Isos) proj₁


-- foo
module _ {A : Change} where
  instance trees-a = trees (𝑶 A); treesums-a = tree-sums (𝑶 A)
           isotrees = isos trees-a

  union : change-tree A ∧ change-tree A ≤ change-tree A
  union .func = Sums.∨-functor (tree-sums (𝑶 A))
  -- (isos (trees (𝑶 A) ∧ trees (𝑶 A))) ∧ (trees (𝑶 A) ∧ trees (𝑶 A))
  --       a               b                da            db
  -- ⇒ trees (𝑶 A)
  union .deriv = π₂ • func union
  union .is-id {da , db}{a , b}{a' , b'} (da:a→a' , db:b→b') =
    juggle∨≈ • ∨≈ da:a→a' db:b→b'
