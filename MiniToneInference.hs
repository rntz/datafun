{-# LANGUAGE TypeSynonymInstances, DeriveFoldable, DeriveFunctor, DeriveTraversable,
             LambdaCase #-}
module MiniToneInference where

import Prelude hiding ((&&), (||))

import Control.Applicative
import Control.Monad
import Control.Monad.RWS.Strict hiding (Sum)
import Data.Coerce
import Data.Foldable
import Data.List (intersperse, intercalate)
import Data.Map.Strict (Map)
import Data.Monoid ((<>))
import Data.Set (Set, (\\), union, unions)
import Data.Traversable
import qualified Data.Bool as Bool
import qualified Data.Map.Strict as M
import qualified Data.Set as S

-- Laws: (<:) is reflexive and transitive.
class Preord a where (<:) :: a -> a -> Bool

-- Laws:
-- 1. (a <: b) iff (a && b == a).
-- 2. (&&) is idempotent, commutative, associative, and has top as identity.
class Preord a => MeetSL a where
  top :: a
  (&&) :: a -> a -> a
  glb :: [a] -> a
  glb = foldr (&&) top

-- Laws:
-- 1. (leq a b) iff (a || b == b).
-- 2. (||) is idempotent, commutative, associative, and has bot as identity.
class Preord a => JoinSL a where
  bot :: a
  (||) :: a -> a -> a
  lub :: [a] -> a
  lub = foldr (||) bot

infixr 2 ||
infixr 3 &&
instance Preord Bool where False <: True = False; x <: y = True
instance MeetSL Bool where (&&) = (Bool.&&); top = True; glb = and
instance JoinSL Bool where (||) = (Bool.||); bot = False; lub = or


---------- TONES ----------
data Tone = Iso | Mono | Anti | Path deriving (Show, Eq, Ord)
instance Preord Tone where
  Iso <: _ = True
  _ <: Path = True
  x <: y | (x == y) = True
  _ <: _ = False

-- Tone conjunction / contraction. This is a meet-semilattice / greatest lower
-- bound operator.
instance MeetSL Tone where
  top = Path
  x && y | x <: y = x
         | y <: x = y
         | otherwise = Iso

-- Tone composition forms a monoid.
-- T_(s <> t) == (T_s . T_t)
-- where T_s : Preorder -> Preorder is the functor for tone s.
instance Monoid Tone where
  mempty = Mono
  mappend x Mono = x
  mappend Mono y = y
  mappend Anti Anti = Mono
  -- the order of the remaining clauses matters.
  mappend x Iso  = Iso   -- hi priority
  mappend x Path = Path  -- hi priority
  mappend Iso  x = Iso   -- lo priority
  mappend Path y = Iso   -- lo priority

-- Together, (&&) and mappend form a semiring, of sorts.


---------- Types ----------
infixr 4 :->
data BaseType = Bool | Str | Nat deriving (Show, Eq, Ord)
data Type
  = Base BaseType
  | Isos Type
  | Set Type
  | Prod [Type]
  | Sum (Map String Type)
  | (:->) Type Type

instance Show Type where
  showsPrec _ (Base b) = shows b
  showsPrec _ (Isos a) = showString "!" . showsPrec 11 a
  showsPrec d (Set a) = showParen (d > 10) $ showString "Set " . showsPrec 0 a
  showsPrec d (Prod as) =
    showParen True $ showString $ intercalate ", " $ map show as
  showsPrec d (Sum as) = showParen (d > 0) $ showString $ intercalate " | " list
    where list = [n ++ " " ++ showsPrec 11 a "" | (n,a) <- M.toList as]
  showsPrec d (Isos a :-> b) = showParen (d > 9) $
    showsPrec 10 a . showString " -> " . showsPrec 9 b
  showsPrec d (a :-> b) = showParen (d > 9) $
    showsPrec 10 a . showString " => " . showsPrec 9 b

-- returns True only if a type's ordering is an equivalence relation.
equiv :: Type -> Bool
equiv (Base Str) = True
equiv (Isos _) = True
equiv (Prod ts) = all equiv ts
equiv (Sum ts) = all equiv $ map snd $ M.toList ts
equiv (a :-> b) = equiv b
equiv _ = False

-- Since we don't have Paths as a type constructor, all our preorders are really
-- posets, and all our equivalences are really discrete.
discrete :: Type -> Bool
discrete = equiv

-- returns True only if a type's ordering is a join-semilattice.
semilattice :: Type -> Bool
semilattice (Base Bool) = True
semilattice (Base Nat) = True
semilattice Set{} = True
semilattice (Prod as) = all semilattice as
semilattice (a :-> b) = semilattice b
semilattice _ = False


---------- SUBTYPING, take 2 ----------
subset, subtype :: Type -> Type -> Bool
subtype (Base x) (Base y) = x == y
subtype (Set a)  (Set b)  = subset a b
subtype (Prod as) (Prod bs) =
  length as == length bs && and [subtype a b | (a,b) <- zip as bs]
subtype (Sum as)  (Sum bs) =
  and [maybe False (subtype a) (M.lookup name bs) | (name, a) <- M.toList as]
-- hm. if a2 is discrete, it seems like we might be able to do better than this?
subtype (a1 :-> b1) (a2 :-> b2) = subtype a2 a1 && subtype b1 b2
subtype (Isos a) b = subset a b
subtype a (Isos b) = discrete a && subset a b
subtype _ _ = False

subset (Base x) (Base y)   = x == y
subset (Set a)  (Set b)    = subset a b
subset (Prod as) (Prod bs) =
  length as == length bs && and [subset a b | (a,b) <- zip as bs]
subset (Sum as)  (Sum bs) =
  and [maybe False (subset a) (M.lookup name bs) | (name, a) <- M.toList as]
subset (Isos a) b = subset a b
subset a (Isos b) = subset a b
subset (a1 :-> b1) (a2 :-> b2) | discrete a2 = subset a2 a1 && subset b1 b2
subset (a1 :-> b1) (a2 :-> b2) =
  subset b1 b2 && subset a2 a1 && undefined -- TODO XXX: what goes here?!
subset _ _ = False

-- An even simpler notion of subtyping. Let's roll with this if I can't figure
-- out the above.
instance Preord Type where
  Base x  <: Base y  = x == y
  Set a   <: Set b   = a <: b     -- conservative
  Prod as <: Prod bs = length as == length bs && and (zipWith (<:) as bs)
  Sum as  <: Sum bs  = and [maybe False (a <:) (M.lookup name bs)
                           | (name, a) <- M.toList as]
  (a1 :-> b1) <: (a2 :-> b2) = a2 <: a1 && b1 <: b2 -- conservative
  Isos a  <: Isos b  = a <: b -- conservative
  Isos a  <: b       = a <: b -- conservative
  _ <: _ = False

-- -- TODO: quickcheck that (forall s a. equiv a == subtype (s, a) (Iso, a)).


---------- UNIFICATION / THE SUBTYPING LATTICE ----------
-- (typeUnify lub a b) finds the join/least-upper-bound of `a` and `b` if `lub`
-- is true; otherwise it finds their meet/greatest-lower-bound.
typeUnify :: Monad m => Bool -> Type -> Type -> m Type
typeUnify lub (Base x) (Base y)
    | x == y = pure (Base x)
    | otherwise = fail "base type mismatch"
typeUnify lub (Set a) (Set b) = Set <$> typeUnify lub a b
typeUnify lub (Prod as) (Prod bs)
    | length as == length bs = Prod <$> zipWithM (typeUnify lub) as bs
    | otherwise = fail "tuple length mismatch"
-- Ugh, the Sum cases are unreadable.
typeUnify True (Sum as) (Sum bs) = Sum <$>
  sequenceA (M.unionWith (\x y -> join (liftM2 (typeUnify True) x y))
                (M.map pure as) (M.map pure bs))
typeUnify False (Sum as) (Sum bs) =
  Sum <$> sequenceA (M.intersectionWith (typeUnify False) as bs)
typeUnify lub (a1 :-> b1) (a2 :-> b2) =
    (:->) <$> typeUnify (not lub) a1 a2 <*> typeUnify lub b1 b2

-- Okay, now the bits I'm not really sure about: handling Isos & equiv-ness.
-- I'm pretty sure this is ok, at least:
typeUnify lub (Isos a) (Isos b) = Isos <$> typeUnify lub a b

-- -- I think for the "simple subtyping" (<:) I give above, the next line should be
-- -- dropped.
-- typeUnify lub (Isos a) b | equiv b = Isos <$> typeUnify lub a b

-- (Isos a <: a), so isos can be dropped when joining, or added when meeting.
-- Reasonably confident about this.
typeUnify lub (Isos a) b = (if lub then id else Isos) <$> typeUnify lub a b

-- To avoid repeating ourselves.
typeUnify lub a (Isos b) = typeUnify lub (Isos b) a

typeUnify _ _ _ = error "cannot unify those types"

typeJoin, typeMeet :: Monad m => Type -> Type -> m Type
typeJoin = typeUnify True
typeMeet = typeUnify False


---------- Subtyping and the type lattice, old version ----------

-- -- IMPORTANT: Do we ever pass in the tone Path here?
-- -- I think we never do!
-- --
-- -- ALSO IMPORTANT: do we ever invoke this with (s /= t)?
-- -- I'm not sure we ever do.
-- -- YES, we do. see the case for (subtype (s,a) (t,Isos b)).
-- --
-- -- I still feel like this could be simpler, somehow.
-- subtype :: (Tone,Type) -> (Tone,Type) -> Bool
-- subtype (s, Base Str) (t, Base Str) = True -- strings are ordered discretely.
-- subtype (s, Base a) (t, Base b) = s <: t && a == b
-- subtype (s, Set a)  (t, Set b)  = s <: t && subtype (Iso, a) (Iso, b)
-- subtype (s, Isos a) (t, b)      = subtype (s <> Iso, a) (t, b)
-- subtype (s, a)      (t, Isos b) = subtype (s, a) (t <> Iso, b)
-- subtype (s,Prod as) (t,Prod bs) =
--   and ((length as == length bs)
--       : [subtype (s,a) (t,b) | (a,b) <- zip as bs])
-- subtype (s, Sum as)  (t, Sum bs) =
--   and [case M.lookup name bs of
--           Nothing -> False
--           Just b -> subtype (s,a) (t,b)
--       | (name, a) <- M.toList as]
-- subtype (s, a1 :-> b1) (t, a2 :-> b2) =
-- -- (a1 => b1)ˢ <: (a2 => b2)ᵗ
-- -- if? iff?
-- -- a1 => b1ˢ <: a2 => b2ᵗ ?!?!
-- --
-- -- TODO: Is this right?!
-- -- I really don't buy this. argh.
-- --
-- -- Can I find a counterexample? Types a1,a2,b1,b2 such that
-- --              a2 <: a1
-- --             b1ˢ <: b2ᵗ
-- --   ¬((a1 => b1)ˢ <: (a2 => b2)ᵗ)
-- -- i.e.
-- --  ∃(f ≤ g ∈ (a1 => b1)ˢ)
-- --   (f ≤ g ∉ (a2 => b2)ᵗ)
--   subtype (Mono, a2) (Mono, a1) && subtype (s, b1) (t, b2)
-- subtype _ _ = False

-- -- VVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVV --
-- -- TODO FIXME XXX: What does typeJoin have to say about subtype?
-- -- especially the function case?
-- -- (a ≤ b) iff (a ∨ b == b), right?
-- -- ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ --


---------- EXPRESSIONS ----------
type Var = String
type Nat = Int
data Lit = LBool Bool | LStr String | LNat Nat deriving (Show, Eq, Ord)

newtype Expr = E { unE :: (ExprF Expr) } deriving Show
data ExprF e
  = Var Var | The Type e
  | Lam Pat e | App e e
  | Box e | Unbox e
  | Tuple [e]
  | Tag String e
  | Case [(Pat, e)]
  | SetOf [e] | Lub [e] | For [CompF e] e
  | Lit Lit
  -- TODO: let-expressions.
  deriving (Show, Functor, Foldable)

data CompF e = In Pat e | When e deriving (Show, Functor, Foldable)

type ExprAlg a = ExprF a -> a
foldExpr :: ExprAlg a -> Expr -> a
foldExpr f (E e) = f (foldExpr f <$> e)

-- For things which can bind variables, e.g. patterns and comprehensions.
class Binder a where binds :: a -> Set Var

-- Note that if the expression contains invalid patterns this won't detect them.
-- Garbage in, garbage out.
free :: Expr -> Set Var
free = foldExpr fv
  where fv :: ExprF (Set Var) -> Set Var
        fv (Var v) = S.singleton v
        fv (Lam p v) = v \\ binds p
        fv (Case branches) = unions [binds p \\ e | (p,e) <- branches]
        fv (For [] inner) = inner
        fv (For (When e : cs) inner) = e `union` fv (For cs inner)
        fv (For (In p e : cs) inner) = e `union` (fv (For cs inner) \\ binds p)
        fv e = S.unions $ toList e


---------- PATTERNS ----------
-- A hack. Patterns are in a sense a strict subset of expressions.
-- This would not work if we wanted conjunct/disjunct patterns.
type Pat = Expr
instance Binder Pat where binds = free -- more hax
instance Binder (CompF e) where
  binds (In p _) = binds p
  binds When{} = S.empty


---------- TYPE INFERENCE ----------
-- Bidirectional type inference with tone synthesis.
type Ctx = Map Var Type

newtype Tones = Tones { unTones :: Map Var Tone } deriving (Show, Eq)
instance Monoid Tones where
  mempty = Tones mempty
  mappend (Tones x) (Tones y) = Tones $ M.unionWith (&&) x y

-- Reads a context mapping vars to their types;
-- writes a map from vars to the tones they are used with.
-- No state.
-- TODO: ExceptionT or whatever for type errors
type Infer a = RWS Ctx Tones () a

data Expect a = Synth | Check a
  deriving (Show, Eq, Functor, Foldable, Traversable)

withTone :: Tone -> Infer a -> Infer a
withTone tone = censor (coerce $ M.map (tone <>))

use :: Var -> Infer Type
use v = do tell (Tones (M.singleton v Mono))
           asks (M.! v)

synth :: Expect Type -> Type -> Infer Type
synth Synth inferred = return inferred
synth (Check expected) inferred
  | inferred <: expected = pure expected
  | otherwise = error "synth: type error"

infer :: Expr -> Expect Type -> Infer Type
infer = foldExpr (flip inf)

-- | Var Var | The Type e
-- | Lam Pat e | App e e
-- | Box e
-- | Tuple [e]
-- | Tag String e
-- | Case [(Pat, e)]
-- | SetOf [e] | Lub [e] | For [CompF e] e
-- | Lit Lit
inf :: Expect Type -> ExprF (Expect Type -> Infer Type) -> Infer Type
-- early error cases
inf Synth (SetOf []) = fail "cannot infer type of empty set"
inf Synth (Lub []) = fail "cannot infer type of empty lub"

-- main cases
inf t (Var x)   = synth t =<< use x
inf t (The a x) = synth t =<< x (Check a)
-- TODO: totality checking
inf (Check (a :-> b)) (Lam p x) = undefined
-- FIXME: decent type errors.
inf t (App x y) = do
  (a :-> b) <- x Synth
  synth t =<< y (Check b)
inf t (Lit l) = synth t (Base (case l of LBool{} -> Bool; LNat{} -> Nat; LStr{} -> Str))
inf Synth (Box x) = Isos <$> withTone Iso (x Synth)
-- crappity crap crap.
-- the box subtyping rules make checking box expressions awkward.
inf (Check a) (Box x) = undefined
inf t (Unbox x) = do Isos a <- withTone Path (x (Isos <$> t)); return a
inf Synth (Tuple xs) = Prod <$> mapM ($ Synth) xs
inf (Check (Prod as)) (Tuple xs)
  | length as == length xs = Prod <$> sequence [x (Check a) | (x,a) <- zip xs as]
  | otherwise = fail "type error (Prod as, length mismatch)"
inf t (Tag n xs) = undefined
-- TODO: totality checking
inf t (Case branches) = undefined
inf (Check (Set a)) (SetOf xs) = Set a <$ undefined
inf Synth (SetOf xs) = Set <$> undefined
-- inf t (SetOf xs)
--   | Just xt <- asSet t = error "wut" [x xt | x <- xs] -- need to take lub.
inf (Check a) (Lub xs)
  | semilattice a = a <$ mapM ($ Check a) xs
  | otherwise = fail "lub at non-semilattice type"
inf Synth (Lub xs)   = undefined
inf t (For comps xs)   = undefined

-- late error cases
inf Check{} Tuple{} = fail "type error checking Tuple"
inf Check{} Lam{} = fail "type error checking Lam"
inf Synth Lam{} = fail "type error inferring Lam"
inf Check{} SetOf{} = fail "type error checking SetOf"

-- asSet :: Monad m => Expect Type -> m (Expect Type)
-- -- asSet = traverse (\case Set a -> pure a; _ -> fail "type error (asSet)")
-- asSet (Check (Set a)) = pure (Check a)
-- asSet Synth = pure Synth
-- asSet _ = fail "type error (asSet)"
