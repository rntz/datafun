module Benchmark (Benchmark, time, benchmark, evaluate) where

import Text.Printf
import System.CPUTime
import Control.Exception (evaluate)
import System.IO

-- Given a test size, produces a naive & seminaive time.
type Benchmark = Int -> IO (Double, Double)

-- What a weird type signature.
time :: a -> IO Double
time x = do
  t1 <- getCPUTime
  _ <- evaluate x
  t2 <- getCPUTime
  return (fromIntegral (t2-t1) * 1e-12)

benchmark :: Benchmark -> IO ()
benchmark run = do
  -- Use line buffering to make sure (or at least make it more likely) that we
  -- generate a valid .dat file.
  hSetBuffering stdout LineBuffering
  printf "n\tnaive\tseminaive\tspeedup\n"
  mapM_ (test run) [80,100..]
  hFlush stdout

test :: Benchmark -> Int -> IO ()
test run n = do
  (naiveT, semiT) <- run n
  let speedup = naiveT / semiT -- the speedup ratio
  printf "%i\t%.2f\t%.2f\t%.2f\n" n naiveT semiT speedup
