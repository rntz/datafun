import Benchmark
import Runtime
import Data.Set (Set, fromList)
import qualified Data.Set
import qualified Data.Char


-- Tools & types for interacting with our compiled Datafun code.
type DFString = Set (Int, Int)
type DFStringDelta = Set (Int, Int)
type Regexp = DFString -> Set (Int, Int)
type RegexpSemi = (DFString, DFStringDelta) -> Set (Int, Int)

makeDFString :: String -> DFString
makeDFString s = fromList (zip [0..] (map Data.Char.ord s))

main = benchmark bench
bench i = do
  let n = i * 20 + 80
  string <- evaluate (makeDFString (replicate n 'a')) -- compute input string
  semiT <- time (astar_semi (string, Data.Set.empty))
  naiveT <- time (astar string)
  return (n, naiveT, semiT)


-- Compiled Datafun code, naive and seminaive.
astar :: Regexp
astar = (let trans_0 = (\edgebox_1 -> (let edge_2 = edgebox_1 in (fix (\path_3 -> (union edge_2 (forIn edge_2 (\a_4 -> (forIn path_3 (\b_5 -> (let (x_6, y1_7) = a_4 in (let (y2_8, z_9) = b_5 in (guard (y1_7 == y2_8) (set [(x_6, z_9)]))))))))))))) in (let pos_10 = (\s_11 -> (forIn s_11 (\pair_12 -> (let (i_13, c_14) = pair_12 in (set [i_13, (i_13 + 1)]))))) in (let nil_15 = (\sbox_16 -> (let s_11 = sbox_16 in (forIn (pos_10 s_11) (\i_13 -> (set [(i_13, i_13)]))))) in (let star_17 = (\rbox_18 -> (let r_19 = rbox_18 in (\sbox_16 -> (let s_11 = sbox_16 in (union (nil_15 s_11) (trans_0 (r_19 s_11))))))) in (let sym_20 = (\c0box_21 -> (let c0_22 = c0box_21 in (\sbox_16 -> (let s_11 = sbox_16 in (forIn s_11 (\e_23 -> (let (i_13, c1_24) = e_23 in (guard (c0_22 == c1_24) (set [(i_13, (i_13 + 1))]))))))))) in (star_17 (sym_20 97)))))))

astar_semi :: RegexpSemi
astar_semi = (let trans_0 = (\edgebox_1 -> (let (edge_2, dedge_2) = edgebox_1 in (semifix ((\path_3 -> (union edge_2 (forIn edge_2 (\a_4 -> (forIn path_3 (\b_5 -> (let (x_6, y1_7) = a_4 in (let (y2_8, z_9) = b_5 in (guard (y1_7 == y2_8) (set [(x_6, z_9)])))))))))), (\path_3 -> (\dpath_3 -> (forIn edge_2 (\a_4 -> (forIn dpath_3 (\b_5 -> (let (x_6, y1_7) = a_4 in (let (y2_8, z_9) = b_5 in (guard (y1_7 == y2_8) (set [(x_6, z_9)])))))))))))))) in (let pos_10 = (\s_11 -> (forIn s_11 (\pair_12 -> (let (i_13, c_14) = pair_12 in (set [i_13, (i_13 + 1)]))))) in (let nil_15 = (\sbox_16 -> (let (s_11, ds_11) = sbox_16 in (forIn (pos_10 s_11) (\i_13 -> (set [(i_13, i_13)]))))) in (let star_17 = (\rbox_18 -> (let (r_19, dr_19) = rbox_18 in (\sbox_16 -> (let (s_11, ds_11) = sbox_16 in (union (nil_15 (s_11, Data.Set.empty)) (trans_0 ((r_19 (s_11, Data.Set.empty)), Data.Set.empty))))))) in (let (sym_20, dsym_20) = ((\c0box_21 -> (let (c0_22, dc0_22) = c0box_21 in (\sbox_16 -> (let (s_11, ds_11) = sbox_16 in (forIn s_11 (\e_23 -> (let (i_13, c1_24) = e_23 in (guard (c0_22 == c1_24) (set [(i_13, (i_13 + 1))]))))))))), (\__36 -> (\__35 -> (\__34 -> (\__33 -> Data.Set.empty))))) in (star_17 ((sym_20 (97, 0)), ((dsym_20 (97, 0)) ()))))))))
