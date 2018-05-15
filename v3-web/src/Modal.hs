{-# LANGUAGE MultiParamTypeClasses, DeriveFunctor, TypeSynonymInstances,
    FlexibleInstances #-}
module ModalDatafun where

import Control.Monad.Reader
import Control.Monad.Writer.Strict hiding (Sum)
import Data.Coerce
import Data.Either (isRight)
import Data.List (foldl')
import Data.Map.Strict (Map)
import Data.Monoid hiding (Sum, Product)
import Data.Set (Set)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set


---------- TONES ----------
data Tone = Id | Op | Iso | Path deriving (Eq, Show)

-- Tones ordered by pointwise subtyping:
-- (s <: t) iff (forall A. A^s <: A^t).
(<:) :: Tone -> Tone -> Bool
Iso <: _ = True
_ <: Path = True
x <: y = x == y

-- Greatest lower bound on tones.
(&) :: Tone -> Tone -> Tone
s & t | s <: t = t
      | s <: t = s
      | otherwise = Iso

meet :: [Tone] -> Tone
meet = foldl' (&) Path

-- Tone composition.
instance Monoid Tone where
  mempty = Id
  mappend Id   s  = s
  mappend Op   Op = Id
  mappend Iso  s  = Iso
  mappend Path s  = Path
  -- Not commutative in general, but we've covered the noncommutative cases.
  mappend s t = mappend t s


---------- TYPES ----------
type Tag = String
data Type
  = Base
  | Fn Type Type
  | Tuple [Type]
  | Sum [(Tag, Type)]
  | Set Type | Box Type | Opp Type
    deriving Show

subtype :: Type -> Type -> Either (Type, Type) Tone
subtype a (Box b) = (<> Iso) <$> subtype a b
subtype (Box a) b = (Path <>) <$> subtype a b
subtype (Opp a) b = (Op <>) <$> subtype a b
subtype a (Opp b) = (Op <>) <$> subtype a b
subtype Base Base = pure Id
subtype (Set a) (Set b) = Id <$ subtype a b
subtype a@(Tuple as) b@(Tuple bs)
  | length as == length bs = meet <$> zipWithM subtype as bs
  | otherwise = Left (a,b)
subtype (Sum as) (Sum bs) = undefined -- TODO
subtype a@(Fn a1 b1) b@(Fn a2 b2) = do
  t <- subtype b1 b2
  s <- subtype a2 a1
  let ok = case t of Iso -> s == Path; Path -> s /= Iso; _ -> t <: s
  if ok then pure t else Left (a,b)
-- incongruous types
subtype a b = Left (a,b)

subset a b = isRight (subtype (Box a) (Box b))

seteq a b = subset a b && subset b a

-- equiv a b = isRight $ subtype a b >> subtype b a
-- The above definition of `equiv` is wrong! For example, it claims that
-- (Box a -> Box b) is equivalent to (Box a -> b).

-- Strips the modes off a type. Useful when typechecking an elimination form for
-- a non-modal type. Called "modal stripping" in tones.tex.
demode :: Type -> (Type, Tone)
demode (Box a) = (b, Path <> s) where (b,s) = demode a
demode (Opp a) = (b, Op <> s) where (b,s) = demode a
demode a = (a, Id)


---------- TERMS, TYPE CHECKING, and TONE INFERENCE ----------
type Var = String
data Check
  = CFn Var Check
  | CTuple [Check] | CTag Tag Check | CSet [Check]
  | CBox Check | COp Check
  -- Large eliminations
  | CCase Synth [(Tag, Var, Check)]
  | CFor Var Synth Check
    deriving Show

data Synth
  = SCheck Type Check
  | SVar Var
  -- Small eliminations
  | SApp Synth Check
  | SProj Synth Int
  | SUnbox Synth | SUnop Synth
    deriving Show

newtype Cx a = Cx (Map Var a) deriving (Show, Eq, Ord)
instance Monoid (Cx Tone) where
  mempty = Cx Map.empty
  Cx a `mappend` Cx b = Cx (Map.unionWith (&) a b)

type Infer = WriterT (Cx Tone) (Reader (Cx Type))

extend :: Var -> a -> Cx a -> Cx a
extend k v = coerce $ Map.insert k v

(!) :: Cx a -> Var -> a
(!) = (Map.!) . coerce

withTone :: Tone -> Cx Tone -> Cx Tone
withTone tone = coerce (Map.map (<> tone))

at :: Tone -> Infer a -> Infer a
at tone = censor (withTone tone)

bind :: Var -> Type -> Infer a -> Infer (a, Tone)
bind v tp action = censor drop $ listens (!v) $ local (extend v tp) action
  where drop (Cx a) = Cx (Map.delete v a)

bindAt :: Tone -> Var -> Type -> Infer a -> Infer a
bindAt allow v tp action = do
  (result, use) <- bind v tp action
  result <$ unless (allow <: use) (error "tone error")

check :: Type -> Check -> Infer ()
synth :: Synth -> Infer Type
synthDestruct :: Synth -> Infer Type
synthDestruct s = pass (remode . demode <$> synth s)
  where remode (a, s) = (a, withTone s)

check (Fn a b) (CFn v body) = bindAt Id v a $ check b body
check (Tuple tps) (CTuple es) | length tps == length es = zipWithM_ check tps es
check (Sum tagtps) (CTag tag e) | Just tp <- lookup tag tagtps = check tp e
-- TODO: Need `tp` to be an equality type!
check (Set tp) (CSet es) = at Iso $ mapM_ (check tp) es
check (Box tp) (CBox e) = at Iso $ check tp e
check (Opp tp) (COp e) = at Op $ check tp e
check tp (CCase subj arms) = undefined -- TODO
check tp@(Set a) (CFor v set body) =
  do Set a <- synth set; bindAt Iso v a $ check tp body

-- Auto-introductions.
check (Box tp) e = at Iso $ check tp e
check (Opp tp) e = at Op $ check tp e

check _ CFn{} = error "invalid type for function"
check _ CTuple{} = error "invalid type for tuple"
check _ CTag{} = error "invalid type for tagged expression"
check _ CSet{} = error "invalid type for set"
check _ CBox{} = error "invalid type for box"
check _ COp{} = error "invalid type for op"
check _ CFor{} = error "invalid type for for-expression"

synth (SCheck tp e) = tp <$ check tp e
synth (SVar v) = asks (! v)
synth (SApp func arg) = do Fn a b <- synthDestruct func; b <$ check a arg
synth (SProj exp i) = do Tuple tps <- synthDestruct exp; pure (tps !! i)
synth (SUnbox e) = do Box tp <- synth e; pure tp
synth (SUnop e) = do Opp tp <- synth e; pure tp



---------- EVALUATION ----------
data Value
  = VInt Int
  | VTuple [Value]
  | VTag Tag Value
  | VFn (Value -> Value)
  | VSet (Set Value)
    deriving Show

instance Show (a -> b) where show _ = "<fn>"
instance Eq Value where a == b = EQ == compare a b
instance Ord Value where
  compare (VInt i) (VInt j) = compare i j
  compare (VTuple x) (VTuple y) = compare x y
  compare (VTag n x) (VTag m y) = compare (n,x) (m,y)
  compare (VSet x) (VSet y) = compare x y
  compare (VFn _) (VFn _) = error "impossible to compare"
  compare _ _ = error "runtime type error"

type Env = Cx Value

evalC :: Check -> Reader Env Value
evalC (CFn x body) = reader $ \env -> VFn $ \a -> evalC body `runReader` extend x a env
evalC (CTuple xs) = VTuple <$> mapM evalC xs
evalC (CTag n x) = VTag n <$> evalC x
evalC (CSet xs) = VSet . Set.fromList <$> mapM evalC xs
evalC (CBox x) = evalC x
evalC (COp x) = evalC x
evalC (CCase subj arms) = undefined -- TODO
evalC (CFor v set body) = do
  elems <- Set.toList . deset <$> evalS set
  sets <- forM elems $ \e -> local (extend v e) (evalC body)
  pure $ VSet $ Set.unions $ map deset sets

evalS :: Synth -> Reader Env Value
evalS (SVar v) = asks (!v)
evalS (SCheck _ e) = evalC e
evalS (SApp func arg) = defn <$> evalS func <*> evalC arg
evalS (SProj exp i) = (!! i) . detuple <$> evalS exp
evalS (SUnbox e) = evalS e
evalS (SUnop e) = evalS e

defn (VFn f) = f; defn _ = error "runtime type error"
deset (VSet s) = s; deset _ = error "runtime type error"
detuple (VTuple xs) = xs; detuple _ = error "runtime type error"
