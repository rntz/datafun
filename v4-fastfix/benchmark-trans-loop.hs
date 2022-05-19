import Benchmark
import Runtime
import Data.Set (Set)
import qualified Data.Set

main :: IO ()
main = benchmark ["normal", "minimized", "normal_loopy", "minimized_loopy"] bench

powers :: [Double]
powers = 40 : [2 ** (7 + 0.5 * i) | i <- [0..]]

times :: [Int]
times = 40 : [120, 140 .. 400] ++ [440, 480 ..]

bench :: Bench
bench i = do
  -- let n = i * 20 + 80
  let n = times !! i
  -- let n = floor $ powers !! i
  edges <- evaluate (lineG n)   -- pre-compute the input graph.
  loopyEdges <- evaluate (loopyLineG n)
  normalT         <- time (trans (edges, Data.Set.empty))
  minimizedT      <- time (trans_minimized (edges, Data.Set.empty))
  normalLoopyT    <- time (trans (loopyEdges, Data.Set.empty))
  minimizedLoopyT <- time (trans_minimized (loopyEdges, Data.Set.empty))
  return (n, [normalT, minimizedT, normalLoopyT, minimizedLoopyT])

-- Example graphs, parameterized by number of nodes.
lineG :: Int -> Set (Int,Int)
lineG n = set [(i,i+1) | i <- [1..n-1]]

loopyLineG :: Int -> Set (Int,Int)
loopyLineG n = set ((n,n) : do i <- [1..n-1]; [(i,i+1), (i,i)])


-- Compiled and optimized Datafun code, using semifix vs semifixNaive.
trans, trans_minimized :: Ord a => (Set (a,a), Set (a,a)) -> Set (a,a)
trans = (\edgebox_0 -> (let (edge_1, dedge_1) = edgebox_0 in (semifix ((\path_2 -> (union edge_1 (forIn edge_1 (\a_3 -> (forIn path_2 (\b_4 -> (let (x_5, y1_6) = a_3 in (let (y2_7, z_8) = b_4 in (guard (y1_6 == y2_7) (set [(x_5, z_8)])))))))))), (\path_2 -> (\dpath_2 -> (forIn edge_1 (\a_3 -> (forIn dpath_2 (\b_4 -> (let (x_5, y1_6) = a_3 in (let (y2_7, z_8) = b_4 in (guard (y1_6 == y2_7) (set [(x_5, z_8)]))))))))))))))

trans_minimized = (\edgebox_0 -> (let (edge_1, dedge_1) = edgebox_0 in (semifixMinimized ((\path_2 -> (union edge_1 (forIn edge_1 (\a_3 -> (forIn path_2 (\b_4 -> (let (x_5, y1_6) = a_3 in (let (y2_7, z_8) = b_4 in (guard (y1_6 == y2_7) (set [(x_5, z_8)])))))))))), (\path_2 -> (\dpath_2 -> (forIn edge_1 (\a_3 -> (forIn dpath_2 (\b_4 -> (let (x_5, y1_6) = a_3 in (let (y2_7, z_8) = b_4 in (guard (y1_6 == y2_7) (set [(x_5, z_8)]))))))))))))))
