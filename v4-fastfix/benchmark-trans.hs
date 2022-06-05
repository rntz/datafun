import Benchmark
import Runtime
import Data.Set (Set)
import qualified Data.Set

main :: IO ()
main = benchmark ["seminaive", "seminaive_simple", "seminaive_raw", "naive"] bench

bench :: Bench
bench i = do
  let n = i * 20 + 80
  edges <- evaluate (lineG n)   -- pre-compute the input graph.
  rawT    <- time (trans_semi_raw (edges, Data.Set.empty))
  simpleT <- time (trans_semi_simple (edges, Data.Set.empty))
  semiT   <- time (trans_semi (edges, Data.Set.empty))
  naiveT  <- time (trans edges)
  -- let (naiveT, rawT) = (0/0, 0/0)
  return (n, [semiT, simpleT, rawT, naiveT])

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
trans = (\e_0 -> (let edge_1 = e_0 in (fix (\p_2 -> (union edge_1 (forIn edge_1 (\a_3 -> (forIn p_2 (\b_4 -> (guard ((snd a_3) == (fst b_4)) (set [((fst a_3), (snd b_4))])))))))))))

trans_semi, trans_semi_simple, trans_semi_raw :: Ord a => (Set (a,a), Set (a,a)) -> Set (a,a)
trans_semi        = (\e_0 -> (let (edge_1, dedge_1) = e_0 in (semifix ((\p_2 -> (union edge_1 (forIn edge_1 (\a_3 -> (forIn p_2 (\b_4 -> (guard ((snd a_3) == (fst b_4)) (set [((fst a_3), (snd b_4))])))))))), (\p_2 -> (\dp_2 -> (forIn edge_1 (\a_3 -> (let da_3 = ((), ()) in (forIn dp_2 (\b_4 -> (let db_4 = ((), ()) in (guard ((snd a_3) == (fst b_4)) (set [((fst a_3), (snd b_4))]))))))))))))))
trans_semi_simple = (\e_0 -> (let (edge_1, dedge_1) = e_0 in (semifix ((\p_2 -> (union edge_1 (forIn edge_1 (\a_3 -> (forIn p_2 (\b_4 -> (guard ((snd a_3) == (fst b_4)) (set [((fst a_3), (snd b_4))])))))))), (\p_2 -> (\dp_2 -> (union dedge_1 (union (forIn dedge_1 (\a_3 -> (let da_3 = ((), ()) in (forIn p_2 (\b_4 -> (guard ((snd a_3) == (fst b_4)) (set [((fst a_3), (snd b_4))]))))))) (forIn (union edge_1 dedge_1) (\a_3 -> (let da_3 = ((), ()) in (forIn dp_2 (\b_4 -> (let db_4 = ((), ()) in (guard ((snd a_3) == (fst b_4)) (set [((fst a_3), (snd b_4))]))))))))))))))))
trans_semi_raw    = (\e_0 -> (let (edge_1, dedge_1) = e_0 in (semifix ((\p_2 -> (union edge_1 (forIn edge_1 (\a_3 -> (forIn p_2 (\b_4 -> (guard ((snd a_3) == (fst b_4)) (set [((fst a_3), (snd b_4))])))))))), (\p_2 -> (\dp_2 -> (union dedge_1 (union (forIn dedge_1 (\a_3 -> (let da_3 = ((), ()) in (forIn p_2 (\b_4 -> (guard ((snd a_3) == (fst b_4)) (set [((fst a_3), (snd b_4))]))))))) (forIn (union edge_1 dedge_1) (\a_3 -> (let da_3 = ((), ()) in (union (forIn dp_2 (\b_4 -> (let db_4 = ((), ()) in (guard ((snd a_3) == (fst b_4)) (set [((fst a_3), (snd b_4))]))))) (forIn (union p_2 dp_2) (\b_4 -> (let db_4 = ((), ()) in (if ((snd a_3) == (fst b_4)) then (set []) else (guard False (union (set [((fst a_3), (snd b_4))]) (set [])))))))))))))))))))

-- trans :: Ord a => Set (a,a) -> Set (a,a)
-- trans = (\edgebox_0 -> (let edge_1 = edgebox_0 in (fix (\path_2 -> (union edge_1 (forIn edge_1 (\a_3 -> (forIn path_2 (\b_4 -> (let (x_5, y1_6) = a_3 in (let (y2_7, z_8) = b_4 in (guard (y1_6 == y2_7) (set [(x_5, z_8)])))))))))))))

-- trans_semi, trans_semi_simple, trans_semi_raw :: Ord a => (Set (a,a), Set (a,a)) -> Set (a,a)
-- trans_semi        = (\edgebox_0 -> (let (edge_1, dedge_1) = edgebox_0 in (semifix ((\path_2 -> (union edge_1 (forIn edge_1 (\a_3 -> (forIn path_2 (\b_4 -> (let (x_5, y1_6) = a_3 in (let (y2_7, z_8) = b_4 in (guard (y1_6 == y2_7) (set [(x_5, z_8)])))))))))), (\path_2 -> (\dpath_2 -> (forIn edge_1 (\a_3 -> (let da_3 = ((), ()) in (forIn dpath_2 (\b_4 -> (let db_4 = ((), ()) in (let (x_5, y1_6) = a_3 in (let (y2_7, z_8) = b_4 in (guard (y1_6 == y2_7) (set [(x_5, z_8)]))))))))))))))))
-- trans_semi_simple = (\edgebox_0 -> (let (edge_1, dedge_1) = edgebox_0 in (semifix ((\path_2 -> (union edge_1 (forIn edge_1 (\a_3 -> (forIn path_2 (\b_4 -> (let (x_5, y1_6) = a_3 in (let (y2_7, z_8) = b_4 in (guard (y1_6 == y2_7) (set [(x_5, z_8)])))))))))), (\path_2 -> (\dpath_2 -> (union dedge_1 (union (forIn dedge_1 (\a_3 -> (let da_3 = ((), ()) in (forIn path_2 (\b_4 -> (let (x_5, y1_6) = a_3 in (let (y2_7, z_8) = b_4 in (guard (y1_6 == y2_7) (set [(x_5, z_8)]))))))))) (forIn (union edge_1 dedge_1) (\a_3 -> (let da_3 = ((), ()) in (forIn dpath_2 (\b_4 -> (let db_4 = ((), ()) in (let (x_5, y1_6) = a_3 in (let (y2_7, z_8) = b_4 in (guard (y1_6 == y2_7) (set [(x_5, z_8)]))))))))))))))))))
-- trans_semi_raw = (\edgebox_0 -> (let (edge_1, dedge_1) = edgebox_0 in (semifix ((\path_2 -> (union edge_1 (forIn edge_1 (\a_3 -> (forIn path_2 (\b_4 -> (let (x_5, y1_6) = a_3 in (let (y2_7, z_8) = b_4 in (guard (y1_6 == y2_7) (set [(x_5, z_8)])))))))))), (\path_2 -> (\dpath_2 -> (union dedge_1 (union (forIn dedge_1 (\a_3 -> (let da_3 = ((), ()) in (forIn path_2 (\b_4 -> (let (x_5, y1_6) = a_3 in (let (y2_7, z_8) = b_4 in (guard (y1_6 == y2_7) (set [(x_5, z_8)]))))))))) (forIn (union edge_1 dedge_1) (\a_3 -> (let da_3 = ((), ()) in (union (forIn dpath_2 (\b_4 -> (let db_4 = ((), ()) in (let (x_5, y1_6) = a_3 in (let (y2_7, z_8) = b_4 in (guard (y1_6 == y2_7) (set [(x_5, z_8)]))))))) (forIn (union path_2 dpath_2) (\b_4 -> (let db_4 = ((), ()) in (let (x_5, y1_6) = a_3 in (let (dx_5, dy1_6) = da_3 in (let (y2_7, z_8) = b_4 in (let (dy2_7, dz_8) = db_4 in (if (y1_6 == y2_7) then Data.Set.empty else (guard False (union (set [(x_5, z_8)]) Data.Set.empty))))))))))))))))))))))
