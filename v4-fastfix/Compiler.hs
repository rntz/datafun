{-# LANGUAGE FunctionalDependencies, MultiParamTypeClasses, RankNTypes,
  FlexibleContexts, DataKinds, KindSignatures, GADTs #-}
module Compiler where

import Prelude hiding (guard, fix)
import Control.Monad.State
import Data.Map (Map)
import qualified Data.Map as Map

data Sym = Sym { symName :: String
               , symId :: Int
               , symDegree :: Int }
           deriving (Eq, Ord)

d :: Sym -> Sym
d (Sym name id d) = Sym name id (d+1)

instance Show Sym where
  show s = d ++ symName s ++ "_" ++ show (symId s)
    where d = case symDegree s of 0 -> ""; 1 -> "d"; d -> "d" ++ show d

-- class Monad m => Gensym m where gensym :: m Sym
gensym :: MonadState Int m => String -> m Sym
gensym name = state (\id -> (Sym name id 0, id+1))

-- Datafun types are complicated. They have three attributes we track with
-- phantom types:
--
-- 1. Is it simple, or modal? (modal = contains a use of Box)
-- 2. Is it a semilattice, or just a poset?
-- 3. Is it first-order, or higher-order?
data Kind = Simple | Modal deriving (Show, Eq, Ord)
data Lattice = SL | Poset deriving (Show, Eq, Ord)
data Order = FO | HO deriving (Show, Eq, Ord)

-- In each case, the first is a "subset" of the second: A simple type is allowed
-- where a modal one is permitted; a semilattice where a non-semilattice is
-- permitted; and a first-order type where a higher-order one is permitted.
--
--
-- However, Haskell lacks subtyping and co/contravariance. So we have to be
-- careful. We must use unconstrained type variables when we produce simple,
-- semilattice, or first-order types. I think there is more to it than this, but
-- my previous attempt to articulate rules for when to use variables & when
-- literals was wrong (eg. failed to make the φδ case for Box typecheck).
--
-- TODO: figure out the right approach. Heuristics/rules so far:
-- - If you can leave an output unconstrained, do so.
-- - In constructors, at least: Constrain input as much as possible.
--   No unnecessarily free type vars in yr input.
--   Is this necessary/useful for ordinary functions too?

data Type :: Kind -> Lattice -> Order -> * where
  Bool :: forall s l o. Type s l o
  String :: forall s o. Type s Poset o
  -- Sets may only contain first-order types.
  Set  :: forall s l o. Type s Poset FO -> Type s l o
  -- Functions are always higher-order, and inherit the codomain's semilattice.
  Fn   :: forall s l. Type s Poset HO -> Type s l HO -> Type s l HO
  Prod :: forall s l o. [Type s l o] -> Type s l o
  -- Boxes are always modal and never semilattices. (Technically □1 is a
  -- semilattice, but who cares?)
  Box  :: forall o. Type Modal Poset o -> Type Modal Poset o

  -- -- Sums are never semilattices (technically singleton sums can be, but
  -- -- who cares?)
  -- Sum  :: forall s l o. [Type s l o] -> Type s Poset o

-- Φ & Δ transforms on types.
φδ :: forall s l o. Type s l o -> (Type Simple l o, Type Simple l o)
phi, delta :: Type s l o -> Type Simple l o
phi = fst . φδ
delta = snd . φδ

φδ (Box a) = φδ a
φδ Bool = (Bool, Bool)
φδ String = (String, Prod [])
φδ (Set a) = (Set φa, Set φa) where φa = phi a
φδ (Prod ts) = (Prod φts, Prod δts)
  where (φts, δts) = unzip (map φδ ts)
φδ (Fn a b) = (Fn φa φb, Fn φa (Fn δa δb))
  where (φa,δa) = φδ a; (φb,δb) = φδ b

debox :: forall s l o. Type s l o -> Type Simple l o
debox (Box a) = debox a
debox Bool = Bool
debox String = String
debox (Set a) = Set (debox a)
debox (Prod ts) = Prod (map debox ts)
debox (Fn a b) = Fn (debox a) (debox b)

-- This could be made cleverer using constraint witnesses, if Haskell has them.
-- But it should be possible to make this typecheck, dammit!
firstOrder :: forall s l o1 o2. Type s l o1 -> Maybe (Type s l o2)
firstOrder Bool = Just Bool
firstOrder String = Just String
firstOrder (Fn a b) = Nothing
firstOrder (Box a) = Box <$> firstOrder a
firstOrder (Set a) = Set <$> firstOrder a
firstOrder (Prod ts) = Prod <$> mapM firstOrder ts

class BaseLang term where
  var :: Type s l o -> Sym -> term
  letIn :: Type s l o -> Type s2 l2 o2 -> Sym -> term -> term -> term
  lam :: Type s l o -> Type s2 l2 o2 -> Sym -> term -> term
  tuple :: [(Type s l o, term)] -> term
  proj :: [Type s l o] -> Int -> term -> term
  -- TODO letTuple
  string :: String -> term
  bool :: Bool -> term
  ifThenElse :: Type s l o -> term -> term -> term -> term
  set :: Type s l FO -> [term] -> term
  equals :: Type s l FO -> term -> term -> term
  -- For now, union, guard, & forIn only at first order types.
  union :: Type s SL FO -> [term] -> term
  guard :: Type s SL FO -> term -> term -> term
  forIn :: Type s l FO -> Type s SL FO -> Sym -> term -> term -> term
  fix :: Type s SL FO -> term -> term

-- NB. Calling it "Modal" would conflict with "Modal" Kind constructor.
class BaseLang term => ModalLang term where
  box :: Type s l o -> term -> term
  letBox :: Type s l o -> Type s l o -> Sym -> term -> term -> term

class BaseLang term => TargetLang term where
  fastFix :: Type s SL FO -> term -> term


-- The seminaive go-faster transform
data Seminaive term = S { φ :: term, δ :: term } deriving (Show, Eq, Ord)

instance TargetLang term => BaseLang (Seminaive term) where
  var a x = S (var φa x) (var δa (d x)) where (φa,δa) = φδ a
  letIn a b x (S φm δm) (S φn δn) =
    S (letIn φa φb x φm φn) (letIn φa δb x φm (letIn δa δb (d x) δm δn))
    where (φa,δa) = φδ a; (φb,δb) = φδ b
  lam = undefined
  tuple = undefined
  proj = undefined
  bool x = undefined
  string x = undefined
  ifThenElse = undefined
  set = undefined
  equals = undefined
  union = undefined
  guard = undefined
  forIn = undefined
  fix = undefined

instance TargetLang term => TargetLang (Seminaive term) where
  fastFix = undefined
