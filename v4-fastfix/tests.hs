import Runtime
import Control.Monad (forM_)
import System.IO
import System.Random
import Data.Set hiding (union, take)
import Text.Printf
import System.CPUTime

-- Transitive closure, naively.
trans :: Ord a => Set (a,a) -> Set (a,a)
trans edge_19 = (fix (\path_18 -> (union edge_19 (forIn edge_19 (\a_12 -> (forIn path_18 (\b_13 -> (guard ((snd a_12) == (fst b_13)) (set [((fst a_12), (snd b_13))])))))))))

-- Transitive closure, seminaively.
semiTrans :: Ord a => Set (a,a) -> Set (a,a)
semiTrans edge_9 =
  semifix ((\path_8 -> (union edge_9 (forIn edge_9 (\a_2 -> (forIn path_8 (\b_3 -> (guard ((snd a_2) == (fst b_3)) (set [((fst a_2), (snd b_3))])))))))),
           (\path_8 -> (\dpath_8 -> (forIn edge_9 (\a_2 -> (forIn dpath_8 (\b_3 -> (guard ((snd a_2) == (fst b_3)) (set [((fst a_2), (snd b_3))])))))))))

test :: Int -> IO ()
test i = do
  let n = 10 * i
  let edges = lineG n
  let numEdges = size edges
  let numNodes = size $ set $ do (x,y) <- toList edges; [x,y]
  printf "testing %i nodes %i edges\n" numNodes numEdges
  naiveT <- time (trans edges)
  semiT <- time (semiTrans edges)
  printf "  naive: %6.2fs\n" naiveT
  printf "  semi:  %6.2fs\n" semiT

-- This is kind of a hack, as you can tell from the type signature.
time :: a -> IO Double
time x = do
  t1 <- getCPUTime
  t2 <- seq x getCPUTime
  return (fromIntegral (t2-t1) * 1e-12)

main :: IO ()
main = mapM_ test [2..16]


-- Example graphs, parameterized by a size factor.
lineG :: Int -> Set (Int,Int)
lineG n = set [(i,i+1) | i <- [1..n-1]]

-- Makes a graph with n nodes and roughly (n sqrt n) edges. seminaive evaluation
-- doesn't seem to help on these! After debugging, it seems like the number of
-- iterations required stays basically constant (around 4). Naive evaluation
-- gets slower the more iterations you need; if the number of iterations isn't
-- going up, it's not slow!
randomG :: Int -> Set (Int,Int)
randomG n = set $ take numEdges $ pairUp $ randomRs (1,n) $ mkStdGen $ n * 2137
  where pairUp (x:y:zs) = (x,y) : pairUp zs
        numEdges = n * floor (sqrt (fromIntegral n))
