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

-- Transitive closure, naively.
trans :: Ord a => Set (a,a) -> Set (a,a)
trans edge_19 = (fix (\path_18 -> (union edge_19 (forIn edge_19 (\a_12 -> (forIn path_18 (\b_13 -> (guard ((snd a_12) == (fst b_13)) (set [((fst a_12), (snd b_13))])))))))))

-- Transitive closure, seminaively.
semiTrans :: Ord a => Set (a,a) -> Set (a,a)
semiTrans edge_9 =
  semifix ((\path_8 -> (union edge_9 (forIn edge_9 (\a_2 -> (forIn path_8 (\b_3 -> (guard ((snd a_2) == (fst b_3)) (set [((fst a_2), (snd b_3))])))))))),
           (\path_8 -> (\dpath_8 -> (forIn edge_9 (\a_2 -> (forIn dpath_8 (\b_3 -> (guard ((snd a_2) == (fst b_3)) (set [((fst a_2), (snd b_3))])))))))))


type DFString = Set (Int, Int)
type DFStringDelta = Set (Int, Int)
type Regexp = (DFString, DFStringDelta) -> Set (Int, Int)

makeDFString :: String -> (DFString, DFStringDelta)
makeDFString s = (fromList  (zip [0..] (fmap Data.Char.ord s)),
                  Data.Set.empty)

semiChar :: Regexp
semiChar = (let (rchar_0, drchar_0) = ((\c0box_1 -> (let (c0_2, dc0_2) = c0box_1 in (\sbox_3 -> (let (s_4, ds_4) = sbox_3 in (forIn s_4 (\e_5 -> (let (i_6, c1_7) = e_5 in (guard (c0_2 == c1_7) (set [(i_6, (i_6 + 1))]))))))))), (\__19 -> (\__18 -> (\__17 -> (\__16 -> Data.Set.empty))))) in (rchar_0 (97, 0)))

semiRplus :: (Regexp, a) -> Regexp 
semiRplus = (let rplus_0 = (\rbox_1 -> (let (r_2, dr_2) = rbox_1 in (\sbox_3 -> (let (s_4, ds_4) = sbox_3 in (let (edge_5, dedge_5) = ((r_2 (s_4, Data.Set.empty)), Data.Set.empty) in (semifix ((\path_6 -> (union edge_5 (forIn edge_5 (\a_7 -> (forIn path_6 (\b_8 -> (let (x_9, y_10) = a_7 in (let (y1_11, z_12) = b_8 in (guard (y_10 == y1_11) (set [(x_9, z_12)])))))))))), (\path_6 -> (\dpath_6 -> (forIn edge_5 (\a_7 -> (forIn dpath_6 (\b_8 -> (let (x_9, y_10) = a_7 in (let (y1_11, z_12) = b_8 in (guard (y_10 == y1_11) (set [(x_9, z_12)]))))))))))))))))) in rplus_0)

semiRplusChar :: (DFString, DFString) -> Set (Int, Int)
semiRplusChar = 
  (let rplus_0 = (\rbox_1 -> (let (r_2, dr_2) = rbox_1 in (\sbox_3 -> (let (s_4, ds_4) = sbox_3 in (let (edge_5, dedge_5) = ((r_2 (s_4, Data.Set.empty)), Data.Set.empty) in (semifix ((\path_6 -> (union edge_5 (forIn edge_5 (\a_7 -> (forIn path_6 (\b_8 -> (let (x_9, y_10) = a_7 in (let (y1_11, z_12) = b_8 in (guard (y_10 == y1_11) (set [(x_9, z_12)])))))))))), (\path_6 -> (\dpath_6 -> (forIn edge_5 (\a_7 -> (forIn dpath_6 (\b_8 -> (let (x_9, y_10) = a_7 in (let (y1_11, z_12) = b_8 in (guard (y_10 == y1_11) (set [(x_9, z_12)]))))))))))))))))) in (let (rchar_13, drchar_13) = ((\c0box_14 -> (let (c0_15, dc0_15) = c0box_14 in (\sbox_3 -> (let (s_4, ds_4) = sbox_3 in (forIn s_4 (\e_16 -> (let (i_17, c1_18) = e_16 in (guard (c0_15 == c1_18) (set [(i_17, (i_17 + 1))]))))))))), (\__30 -> (\__29 -> (\__28 -> (\__27 -> Data.Set.empty))))) in (rplus_0 ((rchar_13 (0, 0)), ((drchar_13 (0, 0)) ())))))




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
test i = do
  let n = 10 * i
  let edges = lineG n
  let testString = makeDFString (replicate n 'a')
  let numEdges = size edges
  let numNodes = size $ set $ do (x,y) <- toList edges; [x,y]
--  printf "testing %i nodes %i edges\n" numNodes numEdges
--  naiveT <- time (trans edges)
--  printf "  naive: %6.2fs\n" naiveT
--  semiT <- time (semiTrans edges)
--  printf "  semi:  %6.2fs\n" semiT
  printf "testing %i character string\n" n 
  semiRplusCharTime <- time (semiRplusChar testString)
  printf "  semi: %6.2f sec\n" semiRplusCharTime
  hFlush stdout

main :: IO ()
main = mapM_ test [2,4..]
