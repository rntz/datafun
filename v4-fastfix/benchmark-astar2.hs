import Benchmark
import Runtime
import Data.Set (Set, fromList)
import qualified Data.Set
import qualified Data.Char


-- Tools & types for interacting with our compiled Datafun code.
type DFString = Set (Int, Int)
type DFStringDelta = Set (Int, Int)
type Regexp = DFString -> Int -> Set Int
type RegexpSemi = (DFString, DFStringDelta) -> (Int, Int) -> Set Int

makeDFString :: String -> DFString
makeDFString s = fromList (zip [0..] (map Data.Char.ord s))

main = benchmark ["seminaive", "seminaive_simple", "seminaive_raw", "naive"] bench
bench i = do
  let n = 600 + 100 * i
  string <- evaluate (makeDFString (replicate n 'a')) -- compute input string
  semiT <- time (astar2_semi (string, Data.Set.empty) (0, 0))
  semiSimpleT <- time (astar2_semi_simple (string, Data.Set.empty) (0, 0))
  semiRawT <- time (astar2_semi_raw (string, Data.Set.empty) (0, 0))
  naiveT <- time (astar2 string 0)
  return (n, [semiT, semiSimpleT, semiRawT, naiveT])


-- Compiled Datafun code, naive and seminaive.
astar2 :: Regexp
astar2 = (let sym_0 = (\cbox_1 -> (let c_2 = cbox_1 in (\sbox_3 -> (let s_4 = sbox_3 in (\ibox_5 -> (let i_6 = ibox_5 in (forIn s_4 (\pair_7 -> (guard (i_6 == (let (j_8, d_9) = pair_7 in j_8)) (guard (c_2 == (let (j_8, d_9) = pair_7 in d_9)) (set [(i_6 + 1)]))))))))))) in (let star_10 = (\rbox_11 -> (let r_12 = rbox_11 in (\sbox_3 -> (let s_4 = sbox_3 in (\ibox_5 -> (let i_6 = ibox_5 in (fix (\self_13 -> (union (set [i_6]) (forIn self_13 (\j_8 -> ((r_12 s_4) j_8)))))))))))) in (star_10 (sym_0 97))))

astar2_semi, astar2_semi_raw, astar2_semi_simple :: RegexpSemi
astar2_semi = (let (sym_0, dsym_0) = ((\cbox_1 -> (let (c_2, dc_2) = cbox_1 in (\sbox_3 -> (let (s_4, ds_4) = sbox_3 in (\ibox_5 -> (let (i_6, di_6) = ibox_5 in (forIn s_4 (\pair_7 -> (guard (i_6 == (let (j_8, d_9) = pair_7 in j_8)) (guard (c_2 == (let (j_8, d_9) = pair_7 in d_9)) (set [(i_6 + 1)]))))))))))), (\__40 -> (\__39 -> (\__38 -> (\__37 -> (\__36 -> (\__35 -> Data.Set.empty))))))) in (let star_10 = (\rbox_11 -> (let (r_12, dr_12) = rbox_11 in (\sbox_3 -> (let (s_4, ds_4) = sbox_3 in (\ibox_5 -> (let (i_6, di_6) = ibox_5 in (semifix ((\self_13 -> (union (set [i_6]) (forIn self_13 (\j_8 -> ((r_12 (s_4, Data.Set.empty)) (j_8, 0)))))), (\self_13 -> (\dself_13 -> (forIn dself_13 (\j_8 -> ((r_12 (s_4, Data.Set.empty)) (j_8, 0)))))))))))))) in (star_10 ((sym_0 (97, 0)), ((dsym_0 (97, 0)) ())))))
astar2_semi_simple = (let (sym_0, dsym_0) = ((\cbox_1 -> (let (c_2, dc_2) = cbox_1 in (\sbox_3 -> (let (s_4, ds_4) = sbox_3 in (\ibox_5 -> (let (i_6, di_6) = ibox_5 in (forIn s_4 (\pair_7 -> (guard (i_6 == (let (j_8, d_9) = pair_7 in j_8)) (guard (c_2 == (let (j_8, d_9) = pair_7 in d_9)) (set [(i_6 + 1)]))))))))))), (\__40 -> (\__39 -> (\__38 -> (\__37 -> (\__36 -> (\__35 -> Data.Set.empty))))))) in (let star_10 = (\rbox_11 -> (let (r_12, dr_12) = rbox_11 in (\sbox_3 -> (let (s_4, ds_4) = sbox_3 in (\ibox_5 -> (let (i_6, di_6) = ibox_5 in (semifix ((\self_13 -> (union (set [i_6]) (forIn self_13 (\j_8 -> ((r_12 (s_4, Data.Set.empty)) (j_8, 0)))))), (\self_13 -> (\dself_13 -> (union (forIn dself_13 (\j_8 -> ((r_12 (s_4, Data.Set.empty)) (j_8, 0)))) (forIn (union self_13 dself_13) (\j_8 -> ((((dr_12 (s_4, Data.Set.empty)) ()) (j_8, 0)) ())))))))))))))) in (star_10 ((sym_0 (97, 0)), ((dsym_0 (97, 0)) ())))))
astar2_semi_raw = (let (sym_0, dsym_0) = ((\cbox_1 -> (let (c_2, dc_2) = cbox_1 in (\sbox_3 -> (let (s_4, ds_4) = sbox_3 in (\ibox_5 -> (let (i_6, di_6) = ibox_5 in (forIn s_4 (\pair_7 -> (guard (i_6 == (let (j_8, d_9) = pair_7 in j_8)) (guard (c_2 == (let (j_8, d_9) = pair_7 in d_9)) (set [(i_6 + 1)]))))))))))), (\cbox_1 -> (\dcbox_1 -> (let (c_2, dc_2) = cbox_1 in (\sbox_3 -> (\dsbox_3 -> (let (s_4, ds_4) = sbox_3 in (\ibox_5 -> (\dibox_5 -> (let (i_6, di_6) = ibox_5 in (union (forIn Data.Set.empty (\pair_7 -> (guard (i_6 == (let (j_8, d_9) = pair_7 in j_8)) (guard (c_2 == (let (j_8, d_9) = pair_7 in d_9)) (set [(i_6 + 1)]))))) (forIn (union s_4 Data.Set.empty) (\pair_7 -> (if (i_6 == (let (j_8, d_9) = pair_7 in j_8)) then (if (c_2 == (let (j_8, d_9) = pair_7 in d_9)) then Data.Set.empty else (guard False (union (set [(i_6 + 1)]) Data.Set.empty))) else (guard False (union (guard (c_2 == (let (j_8, d_9) = pair_7 in d_9)) (set [(i_6 + 1)])) (if (c_2 == (let (j_8, d_9) = pair_7 in d_9)) then Data.Set.empty else (guard False (union (set [(i_6 + 1)]) Data.Set.empty))))))))))))))))))) in (let star_10 = (\rbox_11 -> (let (r_12, dr_12) = rbox_11 in (\sbox_3 -> (let (s_4, ds_4) = sbox_3 in (\ibox_5 -> (let (i_6, di_6) = ibox_5 in (semifix ((\self_13 -> (union (set [i_6]) (forIn self_13 (\j_8 -> ((r_12 (s_4, Data.Set.empty)) (j_8, 0)))))), (\self_13 -> (\dself_13 -> (union Data.Set.empty (union (forIn dself_13 (\j_8 -> ((r_12 (s_4, Data.Set.empty)) (j_8, 0)))) (forIn (union self_13 dself_13) (\j_8 -> ((((dr_12 (s_4, Data.Set.empty)) ()) (j_8, 0)) ()))))))))))))))) in (star_10 ((sym_0 (97, 0)), ((dsym_0 (97, 0)) ())))))
