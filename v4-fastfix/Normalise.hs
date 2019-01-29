{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE DeriveFunctor #-}
module Normalise where

import Control.Monad.State.Strict
import qualified Data.Set as S
import qualified Data.Map as M
import Data.Set (Set)
import Data.Map (Map)
import Data.Monoid
import Data.Maybe (fromMaybe)
import Data.Functor.Identity

data Var = Sym { id :: Int, name :: String } deriving (Eq, Ord)
instance Show Var where show = name

data Type = Base | SetOf Type | Type :-> Type deriving (Show, Eq, Ord)

data Lat = LSet deriving (Show, Eq, Ord)
data Exp
  = Var Var
  | Lam Var Exp
  | App Exp Exp
  | Set [Exp]
  | Vee Lat [Exp]
  | For Lat Var Exp Exp
    deriving Show

data Norm
  = NE Neut
  | NLam Var Norm
  | NLat Lat (Dnf (Set Norm, Set Neut))
    deriving (Show, Eq, Ord)

data Neut = EVar Var | EApp Neut Norm deriving (Show, Eq, Ord)

data Dnf a = Dnf { imm :: a, kids :: Map Clause (Dnf a) }
             deriving (Show, Eq, Ord, Functor, Foldable, Traversable)

data Clause = CFor Var Neut deriving (Show, Eq, Ord)


-- Dnf is a monad over semilattices.
class Single m where single :: a -> m a
class Monoid a => SL a where
  isEmpty :: a -> Bool
  minus :: a -> a -> a
instance Single Dnf where single x = Dnf x M.empty

excludeEmpty :: SL a => a -> Maybe a
excludeEmpty x = if isEmpty x then Nothing else Just x

instance Monoid a => Monoid (Dnf a) where
  mempty = Dnf mempty M.empty
  mappend (Dnf ximm xkids) (Dnf yimm ykids) =
    Dnf (mappend ximm yimm) (mappend xkids ykids)

instance SL a => SL (Dnf a) where
  isEmpty (Dnf x xs) = isEmpty x && M.null xs
  minus x y = undefined         -- TODO

bind :: SL b => Dnf a -> (a -> Dnf b) -> Dnf b
bind d f = fromMaybe mempty (visit mempty d)
  where visit acc (Dnf x xs) = excludeEmpty $ Dnf (y `minus` acc) zs
          where Dnf y ys = f x
                zs = ys <> M.mapMaybe (visit (y <> acc)) xs


-- NBE.
type Gen a = State Int a
gen :: (Int -> a) -> Gen a
gen f = StateT (\i -> pure (f i, i+1))
gensym :: String -> Gen Var
gensym s = gen (`Sym` s)

data Val = VNeut Neut
         | VFn Int String (Val -> Gen Val)
         | VLat Lat (Dnf (Set Val, Set Neut))

instance Eq Val where a == b = compare a b == EQ
instance Ord Val where
  compare (VNeut x) (VNeut y) = compare x y
  compare (VFn x _ _) (VFn y _ _) = compare x y
  compare (VLat h1 d1) (VLat h2 d2) = compare (h1,d1) (h2,d2)
  compare VNeut{} _ = LT
  compare _ VNeut{} = GT
  compare VFn{} _ = LT
  compare _ VFn{} = GT

reify :: Val -> Gen Norm
reify v = undefined

type Env = Map Var Val
eval :: Exp -> Env -> Gen Val
eval (Var v) env = pure $ M.findWithDefault (VNeut (EVar v)) v env
eval (Lam x e) env = gen (\i -> VFn i (name x) runBody)
  where runBody v = eval e (M.insert x v env)
eval (App e f) env = join (app <$> eval e env <*> eval f env)
eval (Set es) env = error "todo"
eval (Vee how xs) env = error "todo"
eval (For how x expr body) env =
  do set <- toSet <$> eval expr env
     -- ah, fuck, monads
     bind set _asdf
     -- case set of
     --   VNeut e -> do
     --            v <- gensym (name x)
     --            -- FIXME: bodyx is a Val, not a Dnf!
     --            bodyx <- toSet <$> eval body (M.insert x (VNeut (EVar v)) env)
     --            pure $ VLat how $ Dnf (S.empty, S.empty) (M.singleton (CFor v e) bodyx)
     --   VLat LSet s -> _blub
     --   _ -> error "type error"

toSet :: Val -> Dnf (Set Val, Set Neut)
toSet (VNeut e) = Dnf (S.empty, S.singleton e) M.empty
toSet (VLat LSet d) = d
toSet _ = error "type error"

app :: Val -> Val -> Gen Val
app (VNeut e) arg = VNeut . EApp e <$> reify arg
app (VFn _ _ f) x = f x
app _ _ = error "type error"
