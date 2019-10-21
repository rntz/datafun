module Benchmark (Benchmark, time, benchmark, evaluate) where

import Text.Printf
import System.CPUTime
import Control.Exception (evaluate)
import System.IO
import System.Environment

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
  -- Figure out how many benchmarks to run. If no argument, we run "forever"
  -- (eg. until the user interrupts us via Ctrl-C).
  args <- getArgs
  benches <- case args of
               [] -> return [80,100..]
               [x] -> do n <- evaluate (read x); return [80,100..60 + 20 * n]
               _ -> error "too many program arguments"
  -- Use line buffering to make sure (or at least make it more likely) that we
  -- generate a valid .dat file.
  hSetBuffering stdout LineBuffering
  printf "n\tnaive\tseminaive\tspeedup\n"
  mapM_ (test run) benches
  hFlush stdout

test :: Benchmark -> Int -> IO ()
test run n = do
  (naiveT, semiT) <- run n
  let speedup = naiveT / semiT -- the speedup ratio
  printf "%i\t%.2f\t%.2f\t%.2f\n" n naiveT semiT speedup
