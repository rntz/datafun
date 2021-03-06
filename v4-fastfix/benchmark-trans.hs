import Benchmark
import Runtime
import Data.Set (Set)
import qualified Data.Set

main :: IO ()
main = benchmark bench

bench :: Benchmark
bench i = do
  let n = i * 20 + 80
  edges <- evaluate (lineG n)   -- pre-compute the input graph.
  semiT   <- time (trans_semi (edges, Data.Set.empty))
  simpleT <- time (trans_semi_simple (edges, Data.Set.empty))
  rawT    <- time (trans_semi_raw (edges, Data.Set.empty))
  naiveT  <- time (trans edges)
  return (n, semiT, simpleT, rawT, naiveT)

-- Example graphs, parameterized by number of nodes.
lineG :: Int -> Set (Int,Int)
lineG n = set [(i,i+1) | i <- [1..n-1]]

-- -- Makes a graph with n nodes and roughly (n sqrt n) edges. seminaive evaluation
-- -- doesn't seem to help on these! After debugging, it seems like the number of
-- -- iterations required stays basically constant (around 4). Naive evaluation
-- -- gets slower the more iterations you need; if the number of iterations isn't
-- -- going up, it's not slow!
-- randomG :: Int -> Set (Int,Int)
-- randomG n = set $ take numEdges $ pairUp $ randomRs (1,n) $ mkStdGen $ n * 2137
--   where pairUp (x:y:zs) = (x,y) : pairUp zs
--         numEdges = n * floor (sqrt (fromIntegral n))


-- Compiled Datafun code, naive and seminaive.
trans :: Ord a => Set (a,a) -> Set (a,a)
trans = (\edgebox_0 -> (let edge_1 = edgebox_0 in (fix (\path_2 -> (union edge_1 (forIn edge_1 (\a_3 -> (forIn path_2 (\b_4 -> (let (x_5, y1_6) = a_3 in (let (y2_7, z_8) = b_4 in (guard (y1_6 == y2_7) (set [(x_5, z_8)])))))))))))))

trans_semi, trans_semi_simple, trans_semi_raw :: Ord a => (Set (a,a), Set (a,a)) -> Set (a,a)
trans_semi = (\edgebox_0 -> (let (edge_1, dedge_1) = edgebox_0 in (semifix ((\path_2 -> (union edge_1 (forIn edge_1 (\a_3 -> (forIn path_2 (\b_4 -> (let (x_5, y1_6) = a_3 in (let (y2_7, z_8) = b_4 in (guard (y1_6 == y2_7) (set [(x_5, z_8)])))))))))), (\path_2 -> (\dpath_2 -> (forIn edge_1 (\a_3 -> (forIn dpath_2 (\b_4 -> (let (x_5, y1_6) = a_3 in (let (y2_7, z_8) = b_4 in (guard (y1_6 == y2_7) (set [(x_5, z_8)]))))))))))))))
trans_semi_simple = (\edgebox_0 -> (let (edge_1, dedge_1) = edgebox_0 in (semifix ((\path_2 -> (union edge_1 (forIn edge_1 (\a_3 -> (forIn path_2 (\b_4 -> (let (x_5, y1_6) = a_3 in (let (y2_7, z_8) = b_4 in (guard (y1_6 == y2_7) (set [(x_5, z_8)])))))))))), (\path_2 -> (\dpath_2 -> (forIn edge_1 (\a_3 -> (forIn dpath_2 (\b_4 -> (let (x_5, y1_6) = a_3 in (let (y2_7, z_8) = b_4 in (guard (y1_6 == y2_7) (set [(x_5, z_8)]))))))))))))))
trans_semi_raw = (\edgebox_0 -> (let (edge_1, dedge_1) = edgebox_0 in (semifix ((\path_2 -> (union edge_1 (forIn edge_1 (\a_3 -> (forIn path_2 (\b_4 -> (let (x_5, y1_6) = a_3 in (let (y2_7, z_8) = b_4 in (guard (y1_6 == y2_7) (set [(x_5, z_8)])))))))))), (\path_2 -> (\dpath_2 -> (union Data.Set.empty (union (forIn Data.Set.empty (\a_3 -> (forIn path_2 (\b_4 -> (let (x_5, y1_6) = a_3 in (let (y2_7, z_8) = b_4 in (guard (y1_6 == y2_7) (set [(x_5, z_8)])))))))) (forIn (union edge_1 Data.Set.empty) (\a_3 -> (union (forIn dpath_2 (\b_4 -> (let (x_5, y1_6) = a_3 in (let (y2_7, z_8) = b_4 in (guard (y1_6 == y2_7) (set [(x_5, z_8)])))))) (forIn (union path_2 dpath_2) (\b_4 -> (let (x_5, y1_6) = a_3 in (let (dx_5, dy1_6) = ((), ()) in (let (y2_7, z_8) = b_4 in (let (dy2_7, dz_8) = ((), ()) in (if (y1_6 == y2_7) then Data.Set.empty else (guard False (union (set [(x_5, z_8)]) Data.Set.empty))))))))))))))))))))
