{-# LANGUAGE OverloadedStrings #-}

-- | criterion driver comparing typed-peg against megaparsec on four grammars
-- of increasing complexity.  Each grammar is written twice, rule for rule
-- (see "Bench.Peg" and "Bench.Mega"), and both libraries consume the exact
-- same input strings.
module Main (main) where

import Control.DeepSeq   (NFData, force)
import Control.Exception (evaluate)
import Criterion.Main
import qualified Data.Text as T
import GHC.Stats          (RTSStats (..), getRTSStats)
import System.Environment (getArgs)
import System.Mem         (performGC)

import qualified Bench.Inputs as I
import qualified Bench.Mega   as M
import qualified Bench.Peg    as P

-- | Build a @peg vs. megaparsec@ comparison group for one input.
compareOn
  :: String                 -- ^ group label
  -> (String -> Int)        -- ^ typed-peg runner
  -> (String -> Int)        -- ^ megaparsec runner over String
  -> (T.Text -> Int)        -- ^ megaparsec runner over Text
  -> String                 -- ^ the input
  -> Benchmark
compareOn label peg megaS megaT input =
  env (prepare input) $ \ ~(s, t) ->
    bgroup (label ++ " [" ++ show (length input) ++ "B]")
      [ bench "typed-peg   (String)" $ whnf peg   s
      , bench "megaparsec  (String)" $ whnf megaS s
      , bench "megaparsec  (Text)"   $ whnf megaT t
      ]

prepare :: String -> IO (String, T.Text)
prepare s = do
  s' <- evaluate (force s)
  t' <- evaluate (force (T.pack s))
  pure (s', t')

-- criterion's 'env' needs NFData on the payload; (String, Text) already has it.
_unusedNFData :: NFData a => a -> a
_unusedNFData = id

-- | Sanity check: both libraries must agree on every benchmark input,
-- otherwise the timings are comparing different amounts of work.
verify :: String -> (String -> Int) -> (String -> Int) -> (T.Text -> Int) -> String -> IO ()
verify label peg megaS megaT input = do
  let a = peg input
      b = megaS input
      c = megaT (T.pack input)
  if a == b && b == c
    then putStrLn ("  ok  " ++ label ++ " [" ++ show (length input) ++ "B] -> " ++ show a)
    else error ("MISMATCH in " ++ label ++ ": peg=" ++ show a
                  ++ " megaString=" ++ show b ++ " megaText=" ++ show c)

verifyAll :: IO ()
verifyAll = do
  putStrLn "== cross-checking typed-peg against megaparsec =="
  mapM_ (verify "arith"  P.runArith  M.runArith  M.runArith . I.arithInput) [50, 200, 800]
  mapM_ (verify "csv"    P.runCsv    M.runCsv    M.runCsv   . flip I.csvInput 8) [20, 100, 400]
  mapM_ (verify "idents" P.runIdents M.runIdents M.runIdents . I.identInput) [100, 500, 2000]
  mapM_ (verify "json"   P.runJson   M.runJson   M.runJson  . I.jsonInput) [10, 50, 200]
  mapM_ (verify "nested" P.runArith  M.runArith  M.runArith . I.nestedInput) [50, 200]
  mapM_ (verify "quoted !.  " P.runQuotedNot M.runQuoted M.runQuoted . I.quotedInput) [50, 200]
  mapM_ (verify "quoted [^\"]" P.runQuotedCls M.runQuoted M.runQuoted . I.quotedInput) [50, 200]
  putStrLn ""

--------------------------------------------------------------------------------
-- Allocation report
--
-- @cabal bench --benchmark-options=--alloc@ prints bytes allocated per parse
-- instead of running criterion.  Allocation is what separates the two
-- libraries once the algorithmic differences are gone, so it is worth being
-- able to read it directly.
--------------------------------------------------------------------------------

allocFor :: (a -> Int) -> a -> IO Integer
allocFor f x = do
  performGC
  before <- getRTSStats
  n <- evaluate (f x)
  n `seq` performGC
  after <- getRTSStats
  pure (fromIntegral (allocated_bytes after - allocated_bytes before))

allocRow :: String -> (String -> Int) -> (String -> Int) -> (T.Text -> Int)
         -> String -> IO ()
allocRow label peg megaS megaT input = do
  s <- evaluate (force input)
  t <- evaluate (force (T.pack input))
  ap <- allocFor peg   s
  as <- allocFor megaS s
  at <- allocFor megaT t
  let n = fromIntegral (length input) :: Double
  putStrLn (concat
    [ pad 22 (label ++ " [" ++ show (length input) ++ "B]")
    , rjust 12 (show ap), rjust 12 (show as), rjust 12 (show at)
    , rjust 10 (showF (fromIntegral ap / n))
    , rjust 10 (showF (fromIntegral as / n))
    ])
  where
    pad k x   = x ++ replicate (k - length x) ' '
    rjust k x = replicate (k - length x) ' ' ++ x
    showF v   = show (fromIntegral (round (v * 10) :: Int) / 10 :: Double)

allocReport :: IO ()
allocReport = do
  putStrLn "bytes allocated per parse (and per input byte)"
  putStrLn (concat [ replicate 22 ' ', "     peg", "  mega(Str)"
                   , "  mega(Txt)", "   peg/B", "  mega/B" ])
  mapM_ (allocRow "arith"  P.runArith  M.runArith  M.runArith . I.arithInput) [50, 200, 800]
  mapM_ (allocRow "csv"    P.runCsv    M.runCsv    M.runCsv   . flip I.csvInput 8) [20, 100, 400]
  mapM_ (allocRow "idents" P.runIdents M.runIdents M.runIdents . I.identInput) [100, 500, 2000]
  mapM_ (allocRow "json"   P.runJson   M.runJson   M.runJson  . I.jsonInput) [10, 50, 200]
  mapM_ (allocRow "nested" P.runArith  M.runArith  M.runArith . I.nestedInput) [50, 200]
  mapM_ (allocRow "quoted-lookahead" P.runQuotedNot M.runQuoted M.runQuoted . I.quotedInput) [50, 200]
  mapM_ (allocRow "quoted-class"     P.runQuotedCls M.runQuoted M.runQuoted . I.quotedInput) [50, 200]

main :: IO ()
main = do
  args <- getArgs
  if "--alloc" `elem` args
    then allocReport
    else verifyAll >> defaultMain benchmarks

benchmarks :: [Benchmark]
benchmarks =
  [ bgroup "arith"
      [ compareOn "arith" P.runArith M.runArith M.runArith (I.arithInput n)
      | n <- [50, 200, 800]
      ]
  , bgroup "csv"
      [ compareOn "csv" P.runCsv M.runCsv M.runCsv (I.csvInput r 8)
      | r <- [20, 100, 400]
      ]
  , bgroup "idents"
      [ compareOn "idents" P.runIdents M.runIdents M.runIdents (I.identInput n)
      | n <- [100, 500, 2000]
      ]
  , bgroup "json"
      [ compareOn "json" P.runJson M.runJson M.runJson (I.jsonInput n)
      | n <- [10, 50, 200]
      ]
  , bgroup "nested"
      [ compareOn "nested" P.runArith M.runArith M.runArith (I.nestedInput d)
      | d <- [50, 200]
      ]
    -- The same language spelled two ways in typed-peg, against one megaparsec
    -- parser: this isolates the cost of the negative-lookahead idiom.
  , bgroup "quoted"
      [ bgroup ("quoted [" ++ show (length inp) ++ "B]")
          [ bench "typed-peg   (!'\"' .)*" $ whnf P.runQuotedNot inp
          , bench "typed-peg   [^\"]*"     $ whnf P.runQuotedCls inp
          , bench "megaparsec  (String)"   $ whnf (M.runQuoted :: String -> Int) inp
          , bench "megaparsec  (Text)"     $ whnf (M.runQuoted :: T.Text -> Int) (T.pack inp)
          ]
      | n <- [50, 200], let inp = I.quotedInput n
      ]
  ]
