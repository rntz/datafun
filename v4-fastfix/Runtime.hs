-- The Datafun runtime.
module Runtime (Set, Preord (..), Semilat (..), set, guard, forIn, fix, semifix, semifixMinimized)
where

import Debug.Trace
import qualified Data.Set as Set
import Data.Set (Set)
import Data.Maybe (fromMaybe)

class Eq a => Preord a where
  (<:) :: a -> a -> Bool

class Preord a => Semilat a where
  empty :: a
  union :: a -> a -> a
  unions :: [a] -> a
  empty = unions []
  union x y = unions [x,y]
  -- difference minimization. union a (diff da a) = union a da.
  diff :: a -> a -> a
  diff x y = x -- always valid but not always efficient
  diffMin :: a -> a -> Maybe a -- FIXME: remove this

instance Preord Bool where x <: y = not x || y
instance Ord a => Preord (Set a) where (<:) = Set.isSubsetOf
instance Semilat Bool where empty = False; union = (||); unions = or
                            diffMin da a = if da <: a then Nothing else Just da
instance Ord a => Semilat (Set a) where
  empty = Set.empty; union = Set.union; unions = Set.unions; diff = Set.difference
  diffMin da a = if Set.null diff then Nothing else Just diff
    where diff = Set.difference da a
instance Preord () where () <: () = True
instance Semilat () where empty = (); unions _ = (); diffMin _ _ = Nothing
instance (Preord a, Preord b) => Preord (a,b) where
  (a,x) <: (b,y) = a <: b && x <: y
instance (Semilat a, Semilat b) => Semilat (a,b) where
  empty = (empty, empty)
  union (a,x) (b,y) = (union a b, union x y)
  unions ts = (unions lefts, unions rights)
    where (lefts, rights) = unzip ts
  diff (da,db) (a,b) = (diff da a, diff db b)
  diffMin (da,db) (a,b) =
    case (diffMin da a, diffMin db b) of
      (Nothing, Nothing) -> Nothing
      (da', db') -> Just (fromMaybe empty da', fromMaybe empty db')
-- Problem: what do I do about n-ary tuples?

set :: Ord a => [a] -> Set a
set = Set.fromList

guard :: Semilat a => Bool -> a -> a
guard True x = x
guard False x = empty

forIn :: Semilat b => Set a -> (a -> b) -> b
forIn set f = unions [f x | x <- Set.toList set]

-- Some debugging infrastructure. Currently disabled.
tracer name i =
  if True || i `mod` 13 /= 0 then id
  else trace (name ++ " " ++ show i)

fix :: Semilat a => (a -> a) -> a
fix f = loop 0 empty
  where loop i x = tracer "fix" i $
                   if x' <: x then x else loop (i+1) x'
          where x' = f x

-- Relies on the fact that the delta type of a semilattice type is itself.
semifix :: Semilat a => ((a -> a), (a -> a -> a)) -> a
semifix (f, df) = loop 0 empty (f empty)
  where loop i x dx =
          tracer "semifix" i $
          if dx <: x then x
          else loop (i+1) (union x dx) (df x dx)

semifixMinimized :: Semilat a => ((a -> a), (a -> a -> a)) -> a
semifixMinimized (f, df) = loop 0 empty (f empty)
  where loop i x dx =
          tracer "semifix" i $
          if dx <: x then x else
            let x' = union x dx in
            loop (i+1) x' (df x dx `diff` x')
