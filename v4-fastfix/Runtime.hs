module Runtime (Set, Semilat (..), set, guard, forIn,
                  fix, semifix, semifixMinimized) where
import qualified Data.Set as Set
import Data.Set (Set)

class Semilat a where
  (<:) :: a -> a -> Bool
  unions :: [a] -> a
  empty :: a
  empty = unions []
  union :: a -> a -> a
  union x y = unions [x,y]
  diff :: a -> a -> a -- Law: union a (diff da a) = union a da
  diff x y = x -- always lawful but not always efficient

instance Semilat () where
  () <: () = True
  unions _ = ()
instance (Semilat a, Semilat b) => Semilat (a,b) where
  (a,x) <: (b,y) = a <: b && x <: y
  unions ts = (unions lefts, unions rights) where (lefts, rights) = unzip ts
  diff (da,db) (a,b) = (diff da a, diff db b)
instance Semilat Bool where
  x <: y = not x || y
  unions = or
instance Ord a => Semilat (Set a) where
  (<:) = Set.isSubsetOf
  unions = Set.unions
  diff = Set.difference

set :: Ord a => [a] -> Set a
set = Set.fromList

guard :: Semilat a => Bool -> a -> a
guard c x = if c then x else empty

forIn :: Semilat b => Set a -> (a -> b) -> b
forIn set f = unions [f x | x <- Set.toList set]

fix :: Semilat a => (a -> a) -> a
fix f = loop empty
  where loop x = if x' <: x then x else loop x'
          where x' = f x

semifix, semifixMinimized :: Semilat a => ((a -> a), (a -> a -> a)) -> a
semifix (f, df) = loop empty (f empty)
  where loop x dx = if dx <: x then x else loop (union x dx) (df x dx)
semifixMinimized (f, df) = loop empty (f empty)
  where loop x dx = if dx <: x then x else
                      let x' = union x dx in loop x' (df x dx `diff` x')
