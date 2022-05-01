module Benchmark (Bench, time, benchmark, evaluate) where

import Text.Printf
import System.CPUTime
import Control.Exception (evaluate)
import System.IO
import System.Environment
import Data.List (intercalate)

-- What a weird type signature.
time :: a -> IO Double
time x = do
  t1 <- getCPUTime
  _ <- evaluate x
  t2 <- getCPUTime
  return (fromIntegral (t2-t1) * 1e-12)


-- -- Given a "run index", a benchmark produces an input size and a quadruple of
-- -- runtimes: (n, seminaive, seminaive_simple, seminaive_raw, naive). Increasing
-- -- the run index should increase the input size by some appropriate amount.
-- type Benchmark = Int -> IO (Int, Double, Double, Double, Double)

-- benchmark :: Benchmark -> IO ()
-- benchmark run = do
--   -- Figure out how many benchmarks to run. If no argument, we run "forever"
--   -- (eg. until the user interrupts us via Ctrl-C).
--   args <- getArgs
--   benches <- case args of
--                [] -> return [0..]
--                [x] -> do n <- evaluate (read x); return [0..n-1]
--                _ -> error "too many program arguments"
--   -- Use line buffering to make sure (or at least make it more likely) that we
--   -- generate a valid .dat file.
--   hSetBuffering stdout LineBuffering
--   printf "n\tseminaive\tseminaive_simple\tseminaive_raw\tnaive\n"
--   -- Do a ridiculously simple warmup by running the first benchmark & discarding
--   -- the results.
--   run 0
--   mapM_ (test run) benches
--   hFlush stdout

-- test :: Benchmark -> Int -> IO ()
-- test run i = do
--   (n, semi, simple, raw, naive) <- run i
--   printf "%i\t%.6f\t%.6f\t%.6f\t%.6f\n" n semi simple raw naive


-- Given a "run index", a bench returns an input size and a list of times, one
-- for each column. Increasing the run index should increase the input size by
-- some appropriate amount.
type Bench = Int -> IO (Int, [Double])

--data Benchmark = Benchmark { benchmarkColumns :: [String], benchmarkRun :: Bench }

benchmark :: [String] -> Bench -> IO ()
benchmark columns run = do
  -- Figure out how many benchmarks to run. If no argument, we run "forever"
  -- (eg. until the user interrupts us via Ctrl-C).
  args <- getArgs
  benches <- case args of
               [] -> return [0..]
               [x] -> do n <- evaluate (read x); return [0..n-1]
               _ -> error "too many program arguments"
  -- Use line buffering to make sure (or at least make it more likely) that we
  -- generate a valid .dat file.
  hSetBuffering stdout LineBuffering
  putStrLn $ intercalate "\t" ("n" : columns)
  -- Do a ridiculously simple warmup by running the first benchmark three times
  -- and discarding the results.
  mapM_ (\_ -> run 0) [1..3]
  let test i = do (n, times) <- run i
                  printf "%i" n
                  mapM_ (printf "\t%.6f") times
                  putStrLn ""
  mapM_ test benches
  hFlush stdout
