{-# LANGUAGE FlexibleInstances #-}
module MiniToneInference where

import Prelude hiding ((&&))
import Control.Applicative
import Control.Monad
import Data.Maybe
import Data.List (intersperse, intercalate)
import Data.Map.Strict (Map, (!))
import Data.Monoid ((<>))
import Data.Set (Set, (\\), union, unions)
import qualified Data.Bool as Bool
import qualified Data.Map.Strict as M
import qualified Data.Set as S

-- Laws: (<:) is reflexive and transitive.
class Preorder a where (<:) :: a -> a -> Bool

-- Laws:
-- 1. (a <: b) iff (a && b == a).
-- 2. (&&) is idempotent, commutative, associative, and has top as identity.
class Preorder a => MeetSemilattice a where
  top :: a
  (&&) :: a -> a -> a
  meet :: [a] -> a
  meet = foldr (&&) top

infix  4 <:
infixr 3 &&
instance Preorder Bool where False <: True = False; x <: y = True
instance MeetSemilattice Bool where (&&) = (Bool.&&); top = True; meet = and


---------- Tones ----------
-- Tones modify the ordering on a preorder A:
--
-- 1. Id A = A.
--
-- 2. (x <= y : Op A) iff (y <= x : A).
--
-- 3. (x <= y : Iso A) iff (x <= y and y <= x : A).
--
-- 4. (x <= y : Path A) if (x <= y or y <= x : A). This is an "if", not an "if
-- and only if"; in general, (x <= y or y <= x) isn't transitive, so we have to
-- take its transitive closure. Because of this, actually *testing* inequality
-- at (Path A) is difficult for this reason. Luckily, we won't need to do that.
--
-- I use variables t,u,v to stand for tones. Tones have the following property:
-- if (f : A -> B) is monotone, then so is (f : t A -> t B) for any tone t.
-- This makes them endofunctors on the category of preorders & monotone maps.
data Tone = Id | Op | Iso | Path deriving (Show, Eq, Ord)

-- For preorders A, B, let (A <: B) iff A is a subpreorder of B; that is, if A ⊆
-- B and x ≤ y : A implies x ≤ y : B. Then tones form a lattice as follows: let
-- (t <= u) iff (t A <: u A) for all preorders A. The lattice is diamond-shaped:
--
--          Path                greatest: ∀A. (A <: Path)
--         /   \
--        Id   Op
--         \   /
--          Iso                 least: ∀A. (Iso <: A)
--
instance Preorder Tone where
  Iso <: _ = True
  _ <: Path = True
  x <: y | (x == y) = True
  _ <: _ = False

instance MeetSemilattice Tone where
  top = Path
  x && y | x <: y = x
         | y <: x = y
         | otherwise = Iso

-- Tones, as endofunctors on Preorder, form a monoid under composition.
-- I give composition in the same order as functions: for a preorder A,
-- (t <> u) A == t (u A).
instance Monoid Tone where
  mempty = Id
  mappend x Id = x
  mappend Id y = y
  mappend Op Op = Id
  -- the order of the remaining clauses matters.
  mappend x Iso  = Iso   -- hi priority
  mappend x Path = Path  -- hi priority
  mappend Iso  x = Iso   -- lo priority
  mappend Path y = Iso   -- lo priority

-- (&&) and (<>) form a semiring; that is, (<>) distributes over (&&):
--
--     t <> (u && v) == (t <> u) && (t <> v)
--     (t && u) <> v == (t <> v) && (u <> v)
--
-- A number of recent and not-so-recent type systems also use semiring
-- annotations on variables, including:
--
-- 1. "Linear Haskell" (POPL 2018)
-- 2. "I Got Plenty o' Nuttin" (McBride)
-- 3. "Monotonicity Types" (PMLDC 2017)
-- 4. "Bounded Linear Types in a Resource Semiring" (ESOP 2014)
-- 5. "The Next 700 Modal Type Assignment Systems" (TYPES 2015)
-- 6. Petricek, Orchard, et al's work on coeffects
-- 7. Provenance and information flow typing, possibly?
-- 8. "A Fibrational Framework for Substructural and Modal Logics" (FSCD 2017),
-- which massively generalizes this pattern.


---------- Types ----------
infixr 4 :->
data Type
  = Bool                  -- booleans
  | Prod [Type]           -- Tuples or product types
  | Sum (Map String Type) -- Sum types; values tagged with a constructor
  | (:->) Type Type       -- Functions

  -- Finally, a type can be wrapped with a tone. This doesn't change the type's
  -- values, but it alters how they're ordered for purposes of checking
  -- monotonicity. Datafun's type system ensures all functions are monotone, so
  -- to use something "non-monotonically", we have to wrap it with a tone.
  | Mode Tone Type
  -- invariant: in (Mode t a), t /= Path.
  -- This is because I don't know how to handle the (t = Path) case yet.
  -- I'm not sure there is a "good" way to do it.

instance Show Type where
  showsPrec _ Bool = showString "bool"
  showsPrec _ (Mode t a) = showString s . showsPrec 11 a
    where s = case t of Id -> "+"; Op -> "-"; Iso -> "!"; Path -> "?"
  showsPrec d (Prod as) =
    showParen True $ showString $ intercalate ", " $ map show as
  showsPrec d (Sum as) = showParen (d > 0) $ showString $ intercalate " | " list
    where list = [n ++ " " ++ showsPrec 11 a "" | (n,a) <- M.toList as]
  showsPrec d (Mode Iso a :-> b) = showParen (d > 9) $
    showsPrec 10 a . showString " -> " . showsPrec 9 b
  showsPrec d (a :-> b) = showParen (d > 9) $
    showsPrec 10 a . showString " => " . showsPrec 9 b

-- Returns True only if a type has a least element.
hasBottom :: Tone -> Type -> Bool
hasBottom t (Mode s a) = hasBottom (t <> s) a
hasBottom Id Bool = True
hasBottom Op Bool = True
hasBottom _  Bool = False
hasBottom t (Prod as) = all (hasBottom t) as
hasBottom t (Sum h) | [(_,a)] <- M.toList h = hasBottom t a
hasBottom _ (Sum _) = False
hasBottom t (a :-> b) = hasBottom t b


---------- Subtyping ----------
leftAdjoint :: Tone -> Tone
leftAdjoint Path = error "Path has no left adjoint"
leftAdjoint Iso = Path
leftAdjoint Id = Id
leftAdjoint Op = Op

-- stripTone t a = (u,b) such that (Mode t a) and (Mode u b) are equivalent,
-- and b /= (Mode _ _).
stripTone :: Tone -> Type -> (Tone, Type)
stripTone t (Mode u b) = stripTone (t <> u) b
stripTone t a = (t,a)

detune :: Type -> (Tone, Type)
detune a = (leftAdjoint t, b) where (t,b) = stripTone Id a

-- (subtype a b == Just t) implies (t a <: b), and t is the greatest tone for
-- which this is true.
subtype :: (Monad m, Alternative m) => Type -> Type -> m Tone
-- Mode introduction/elimination.
subtype a (Mode t b) = (t <>) <$> subtype a b
subtype (Mode t a) b = (<> leftAdjoint t) <$> subtype a b
-- More interesting types.
subtype Bool Bool = pure Id
subtype (Prod as) (Prod bs)
  | length as == length bs = meet <$> zipWithM subtype as bs
subtype (Sum as) (Sum bs)
  | S.isSubsetOf (M.keysSet as) (M.keysSet bs) =
    meet <$> sequence [subtype a (bs ! name) | (name, a) <- M.toList as]
subtype (a1 :-> b1) (a2 :-> b2) = do
  dom <- subtype a2 a1
  cod <- subtype b1 b2
  guard $ case cod of Path -> Path == (Path <> dom)
                      _ -> leftAdjoint cod <: dom
  pure cod
-- Failure cases.
subtype Bool _ = fail "nope"
subtype Prod{} _ = fail "nope"
subtype Sum{} _ = fail "nope"
subtype (:->){} _ = fail "nope"

instance Preorder Type where a <: b = isJust (subtype a b)


---------- Expressions and patterns ----------
type Var = String               -- a variable name
type Tag = String               -- a "tag", or constructor of a sum type

-- Patterns can be variables, tuples, or constructors.
data Pat = PVar Var | PTuple [Pat] | PTag Tag Pat deriving Show

-- Expressions whose types can be inferred:
data Expr = Var Var             -- variables,
          | LitBool Bool        -- literals,
          | The Type Term       -- any type-annotated term,
          | App Expr Term       -- and function applications.
  deriving Show

-- Terms, whose types can be checked:
data Term = Expr Expr              -- any expression whose type can be inferred,
          | If Term Term Term      -- conditionals,
          | When Term Term         -- monotone conditionals,
          | Lambda Var Term        -- functions,
          | Tag Tag Term           -- tagged values of a sum type,
          | Tuple [Term]           -- tuples,
          | Let Var Expr Term      -- let-bindings,
          | Case Expr [(Pat,Term)] -- and case-expressions.
  deriving Show

-- We could probably expand the set of inferrable expressions. But for the sake
-- of clarity, I don't, to avoid redundancy. For example, "let x = e1 in e2" can
-- infer if "e2" can infer; but then we need two cases for typechecking let - an
-- inferring case, and a checking case.


---------- Type checking ----------
-- Type & tone contexts. Type contexts map variables to their types; tone
-- contexts, to the tones at which they're used.
type Types = Map Var Type
type Tones = Map Var Tone

-- Composing a tone over a tone context.
(<@) :: Tone -> Tones -> Tones
t <@ ts = fmap (t <>) ts

-- Taking the meet of two tone contexts. Absent variables are regarded as if
-- mapped to Path.
instance MeetSemilattice Tones where top = M.empty; (&&) = M.unionWith (&&)
instance Preorder Tones where (<:) = error "Left as exercise for the reader."

-- (checkPat t a p == cx) means pattern `p` can match a value of type `a` at
-- tone `t`, producing variables with types in `cx`.
checkPat :: Tone -> Type -> Pat -> Types
checkPat t (Mode u b) p = checkPat (t <> u) b p
checkPat t a (PVar x) = M.singleton x (Mode t a)
checkPat t (Prod as) (PTuple ps)
  | length as == length ps = M.unionsWith uhoh $ zipWith (checkPat t) as ps
  where uhoh _ _ = error "cannot use same variable twice in pattern"
checkPat t (Sum arms) (PTag name p) = checkPat t (arms ! name) p
checkPat t _ PTuple{} = error "tuple must have product type"
checkPat t _ PTag{} = error "tagged pattern must have sum type"

-- (infer cx e == (a,ts)) means `e` infers type `a` using variables of types in
-- `cx` at tones given in `ts`.
infer :: Types -> Expr -> (Type, Tones)
infer cx (Var x) = (cx ! x, M.singleton x Id)
infer cx (LitBool b) = (Bool, M.empty)
infer cx (The a m) = (a, check cx a m)
infer cx (App e m) = let (tp, ts) = infer cx e
                         (t, a :-> b) = detune tp
                     in (b, (t <@ ts) && check cx a m)

-- (check cx a m == ts) means `e` checks at type `a` using variables of types
-- in `cx` at tones given in `ts`.
check :: Types -> Type -> Term -> Tones
-- first, deal with modes on the type.
check cx (Mode t a) m = t <@ check cx a m
-- then, examine the term.
check cx a (Expr e) = let (b,ts) = infer cx e
                      in fromJust (subtype a b) <@ ts
check cx a (If m n o) =
  check cx (Mode Iso Bool) m && check cx a n && check cx a o
check cx a (When m n)
  | hasBottom Id a = check cx Bool m && check cx a m
  | otherwise = error "use of `when` at non-pointed type"
check cx (a :-> b) (Lambda x m) =
  let ts = check (M.insert x a cx) b m
  in if Id <: ts ! x then M.delete x ts
     else error ("non-monotone use of variable " ++ x)
check cx (Sum as) (Tag name m) = check cx (as ! name) m
check cx (Prod as) (Tuple ms)
  | length as == length ms = meet $ zipWith (check cx) as ms
check cx expected (Let x e m) =
  let (a, eTones) = infer cx e
      mTones = check (M.insert x a cx) expected m
      xTone = M.findWithDefault Path x mTones
  in M.delete x mTones && (xTone <@ eTones)
check cx expected (Case e arms) =
  let (subjType, subjTones) = infer cx e in
  meet $ flip map arms $ \(p, m) ->
    let patCx = checkPat Id subjType p
        -- The monoid instance on Map is a left-biased union.
        armTones = check (patCx <> cx) expected m
        -- Split tones: are they on variables from subject, or external?
        (patTones, cxTones) =
          M.partitionWithKey (\x _ -> M.member x patCx) armTones
        -- The tone at which we use the subject.
        useTone = meet $ map snd $ M.toList patTones
    in cxTones && (useTone <@ subjTones)
-- Failure cases
check cx _ Lambda{} = error "lambda must have function type"
check cx _ Tag{} = error "tagged expression must have sum type"
check cx _ Tuple{} = error "tuple must have product type"
