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
bench n = do
  string <- evaluate (makeDFString (replicate n 'a')) -- compute input string
  semiT <- time (aplus_semi (string, Data.Set.empty))
  naiveT <- time (aplus string)
  return (naiveT, semiT)


-- Compiled Datafun code, naive and seminaive.
aplus :: Regexp
aplus = (let trans_0 = (\edgebox_1 -> (let edge_2 = edgebox_1 in (fix (\path_3 -> (union edge_2 (forIn edge_2 (\a_4 -> (forIn path_3 (\b_5 -> (let (x_6, y_7) = a_4 in (let (y1_8, z_9) = b_5 in (guard (y_7 == y1_8) (set [(x_6, z_9)]))))))))))))) in (let rplus_10 = (\rbox_11 -> (let r_12 = rbox_11 in (\sbox_13 -> (let s_14 = sbox_13 in (trans_0 (r_12 s_14)))))) in (let rchar_15 = (\c0box_16 -> (let c0_17 = c0box_16 in (\sbox_13 -> (let s_14 = sbox_13 in (forIn s_14 (\e_18 -> (let (i_19, c1_20) = e_18 in (guard (c0_17 == c1_20) (set [(i_19, (i_19 + 1))]))))))))) in (rplus_10 (rchar_15 97)))))

aplus_semi :: RegexpSemi
aplus_semi = (let trans_0 = (\edgebox_1 -> (let (edge_2, dedge_2) = edgebox_1 in (semifix ((\path_3 -> (union edge_2 (forIn edge_2 (\a_4 -> (forIn path_3 (\b_5 -> (let (x_6, y_7) = a_4 in (let (y1_8, z_9) = b_5 in (guard (y_7 == y1_8) (set [(x_6, z_9)])))))))))), (\path_3 -> (\dpath_3 -> (forIn edge_2 (\a_4 -> (forIn dpath_3 (\b_5 -> (let (x_6, y_7) = a_4 in (let (y1_8, z_9) = b_5 in (guard (y_7 == y1_8) (set [(x_6, z_9)])))))))))))))) in (let rplus_10 = (\rbox_11 -> (let (r_12, dr_12) = rbox_11 in (\sbox_13 -> (let (s_14, ds_14) = sbox_13 in (trans_0 ((r_12 (s_14, Data.Set.empty)), Data.Set.empty)))))) in (let (rchar_15, drchar_15) = ((\c0box_16 -> (let (c0_17, dc0_17) = c0box_16 in (\sbox_13 -> (let (s_14, ds_14) = sbox_13 in (forIn s_14 (\e_18 -> (let (i_19, c1_20) = e_18 in (guard (c0_17 == c1_20) (set [(i_19, (i_19 + 1))]))))))))), (\__32 -> (\__31 -> (\__30 -> (\__29 -> Data.Set.empty))))) in (rplus_10 ((rchar_15 (97, 0)), ((drchar_15 (97, 0)) ()))))))
