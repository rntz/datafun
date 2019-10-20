import Data.Char
import Runtime
import Control.Monad (forM_)
import System.IO
import System.Random
import Data.Set (size, fromList, toList)
import qualified Data.Set
import Text.Printf
import System.CPUTime
import Control.Exception (evaluate)

-- Tools & types for interacting with our compiled Datafun code.
type DFString = Set (Int, Int)
type DFStringDelta = Set (Int, Int)
type Regexp = DFString -> Set (Int, Int)
type RegexpSemi = (DFString, DFStringDelta) -> Set (Int, Int)

makeDFString :: String -> DFString
makeDFString s = fromList (zip [0..] (map Data.Char.ord s))


-- Compiled Datafun code, naive and seminaive.
trans :: Ord a => Set (a,a) -> Set (a,a)
trans = (\edgebox_0 -> (let edge_1 = edgebox_0 in (fix (\path_2 -> (union edge_1 (forIn edge_1 (\a_3 -> (forIn path_2 (\b_4 -> (let (x_5, y_6) = a_3 in (let (y1_7, z_8) = b_4 in (guard (y_6 == y1_7) (set [(x_5, z_8)])))))))))))))

trans_semi :: Ord a => (Set (a,a), Set (a,a)) -> Set (a,a)
trans_semi = (\edgebox_0 -> (let (edge_1, dedge_1) = edgebox_0 in (semifix ((\path_2 -> (union edge_1 (forIn edge_1 (\a_3 -> (forIn path_2 (\b_4 -> (let (x_5, y_6) = a_3 in (let (y1_7, z_8) = b_4 in (guard (y_6 == y1_7) (set [(x_5, z_8)])))))))))), (\path_2 -> (\dpath_2 -> (forIn edge_1 (\a_3 -> (forIn dpath_2 (\b_4 -> (let (x_5, y_6) = a_3 in (let (y1_7, z_8) = b_4 in (guard (y_6 == y1_7) (set [(x_5, z_8)]))))))))))))))

aplus :: DFString -> Set (Int, Int)
aplus = (let rplus_0 = (\rbox_1 -> (let r_2 = rbox_1 in (\sbox_3 -> (let s_4 = sbox_3 in (let edge_5 = (r_2 s_4) in (fix (\path_6 -> (union edge_5 (forIn edge_5 (\a_7 -> (forIn path_6 (\b_8 -> (let (x_9, y_10) = a_7 in (let (y1_11, z_12) = b_8 in (guard (y_10 == y1_11) (set [(x_9, z_12)])))))))))))))))) in (let rchar_13 = (\c0box_14 -> (let c0_15 = c0box_14 in (\sbox_3 -> (let s_4 = sbox_3 in (forIn s_4 (\e_16 -> (let (i_17, c1_18) = e_16 in (guard (c0_15 == c1_18) (set [(i_17, (i_17 + 1))]))))))))) in (rplus_0 (rchar_13 97))))

aplus_semi :: (DFString, DFStringDelta) -> Set (Int, Int)
aplus_semi = (let rplus_0 = (\rbox_1 -> (let (r_2, dr_2) = rbox_1 in (\sbox_3 -> (let (s_4, ds_4) = sbox_3 in (let (edge_5, dedge_5) = ((r_2 (s_4, Data.Set.empty)), Data.Set.empty) in (semifix ((\path_6 -> (union edge_5 (forIn edge_5 (\a_7 -> (forIn path_6 (\b_8 -> (let (x_9, y_10) = a_7 in (let (y1_11, z_12) = b_8 in (guard (y_10 == y1_11) (set [(x_9, z_12)])))))))))), (\path_6 -> (\dpath_6 -> (forIn edge_5 (\a_7 -> (forIn dpath_6 (\b_8 -> (let (x_9, y_10) = a_7 in (let (y1_11, z_12) = b_8 in (guard (y_10 == y1_11) (set [(x_9, z_12)]))))))))))))))))) in (let (rchar_13, drchar_13) = ((\c0box_14 -> (let (c0_15, dc0_15) = c0box_14 in (\sbox_3 -> (let (s_4, ds_4) = sbox_3 in (forIn s_4 (\e_16 -> (let (i_17, c1_18) = e_16 in (guard (c0_15 == c1_18) (set [(i_17, (i_17 + 1))]))))))))), (\__30 -> (\__29 -> (\__28 -> (\__27 -> Data.Set.empty))))) in (rplus_0 ((rchar_13 (97, 0)), ((drchar_13 (97, 0)) ())))))

aplus_trans :: DFString -> Set (Int, Int)
aplus_trans = (let trans_0 = (\edgebox_1 -> (let edge_2 = edgebox_1 in (fix (\path_3 -> (union edge_2 (forIn edge_2 (\a_4 -> (forIn path_3 (\b_5 -> (let (x_6, y_7) = a_4 in (let (y1_8, z_9) = b_5 in (guard (y_7 == y1_8) (set [(x_6, z_9)]))))))))))))) in (let rplus_10 = (\rbox_11 -> (let r_12 = rbox_11 in (\sbox_13 -> (let s_14 = sbox_13 in (trans_0 (r_12 s_14)))))) in (let rchar_15 = (\c0box_16 -> (let c0_17 = c0box_16 in (\sbox_13 -> (let s_14 = sbox_13 in (forIn s_14 (\e_18 -> (let (i_19, c1_20) = e_18 in (guard (c0_17 == c1_20) (set [(i_19, (i_19 + 1))]))))))))) in (rplus_10 (rchar_15 97)))))

aplus_trans_semi :: (DFString, DFStringDelta) -> Set (Int, Int)
aplus_trans_semi = (let trans_0 = (\edgebox_1 -> (let (edge_2, dedge_2) = edgebox_1 in (semifix ((\path_3 -> (union edge_2 (forIn edge_2 (\a_4 -> (forIn path_3 (\b_5 -> (let (x_6, y_7) = a_4 in (let (y1_8, z_9) = b_5 in (guard (y_7 == y1_8) (set [(x_6, z_9)])))))))))), (\path_3 -> (\dpath_3 -> (forIn edge_2 (\a_4 -> (forIn dpath_3 (\b_5 -> (let (x_6, y_7) = a_4 in (let (y1_8, z_9) = b_5 in (guard (y_7 == y1_8) (set [(x_6, z_9)])))))))))))))) in (let rplus_10 = (\rbox_11 -> (let (r_12, dr_12) = rbox_11 in (\sbox_13 -> (let (s_14, ds_14) = sbox_13 in (trans_0 ((r_12 (s_14, Data.Set.empty)), Data.Set.empty)))))) in (let (rchar_15, drchar_15) = ((\c0box_16 -> (let (c0_17, dc0_17) = c0box_16 in (\sbox_13 -> (let (s_14, ds_14) = sbox_13 in (forIn s_14 (\e_18 -> (let (i_19, c1_20) = e_18 in (guard (c0_17 == c1_20) (set [(i_19, (i_19 + 1))]))))))))), (\__32 -> (\__31 -> (\__30 -> (\__29 -> Data.Set.empty))))) in (rplus_10 ((rchar_15 (97, 0)), ((drchar_15 (97, 0)) ()))))))


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


-- What a weird type signature.
time :: a -> IO Double
time x = do
  t1 <- getCPUTime
  _ <- evaluate x
  t2 <- getCPUTime
  return (fromIntegral (t2-t1) * 1e-12)

test :: Int -> IO ()
test n = do
  -- Pre-compute the test inputs.
  edges <- evaluate (lineG n)
  string <- evaluate (makeDFString (replicate n 'a'))

  let numEdges = size edges
  let numNodes = size $ set $ do (x,y) <- toList edges; [x,y]
  printf "testing %i nodes %i edges\n" numNodes numEdges
  semiT <- time (trans_semi (edges, empty))
  naiveT <- time (trans edges)
  printf "  semi:  %6.2fs\n" semiT
  printf "  naive: %6.2fs\n" naiveT
  hFlush stdout

  printf "testing %i character string\n" n
  semiT <- time (aplus_semi (string, empty))
  naiveT <- time (aplus string)
  printf "  semi:  %6.2fs\n" semiT
  printf "  naive: %6.2fs\n" naiveT
  hFlush stdout

  printf "testing %i character string (separate trans)\n" n
  semiT <- time (aplus_trans_semi (string, empty))
  naiveT <- time (aplus_trans string)
  printf "  semi:  %6.2fs\n" semiT
  printf "  naive: %6.2fs\n" naiveT
  hFlush stdout

main :: IO ()
main = mapM_ test [80,100..]
