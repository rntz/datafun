-- The Datafun runtime.
module Runtime (Set, Preord (..), Semilat (..), set, guard, forIn, fix, fastfix)
where

import qualified Data.Set as Set
import Data.Set (Set)

class Eq a => Preord a where
  (<:) :: a -> a -> Bool

class Preord a => Semilat a where
  empty :: a
  union :: a -> a -> a
  unions :: [a] -> a
  empty = unions []
  union x y = unions [x,y]

instance Preord Bool where x <: y = not x || y
instance Ord a => Preord (Set a) where (<:) = Set.isSubsetOf
instance Semilat Bool where empty = False; union = (||); unions = or
instance Ord a => Semilat (Set a) where
  empty = Set.empty; union = Set.union; unions = Set.unions
instance Preord () where () <: () = True
instance Semilat () where empty = (); unions _ = ()
instance (Preord a, Preord b) => Preord (a,b) where
  (a,x) <: (b,y) = a <: b && x <: y
instance (Semilat a, Semilat b) => Semilat (a,b) where
  empty = (empty, empty)
  union (a,x) (b,y) = (union a b, union x y)
  unions ts = (unions lefts, unions rights)
    where (lefts, rights) = unzip ts
-- Problem: what do I do about n-ary tuples?

set :: Ord a => [a] -> Set a
set = Set.fromList

guard :: Semilat a => Bool -> a -> a
guard True x = x
guard False x = empty

forIn :: Semilat b => Set a -> (a -> b) -> b
forIn set f = unions [f x | x <- Set.toList set]

fix :: Semilat a => (a -> a) -> a
fix f = loop empty
  where loop x = if x <: x' then x else loop x'
          where x' = f x

-- Relies on the fact that the delta type of a semilattice type is itself.
fastfix :: Semilat a => ((a -> a), (a -> a -> a)) -> a
fastfix (f, df) = loop empty (f empty)
  where loop x dx = if dx <: x then x
                    else loop (union x dx) (df x dx)
