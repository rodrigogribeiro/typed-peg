{-# LANGUAGE OverloadedStrings #-}

-- | criterion driver comparing typed-peg against megaparsec.
--
-- Each grammar is written twice, rule for rule (see "Bench.Peg" and
-- "Bench.Mega"), and both libraries consume the exact same input.
--
-- typed-peg is measured over 'String', 'Data.Text.Text' and
-- 'Data.ByteString.ByteString'; megaparsec over 'String' and
-- 'Data.Text.Text' only, because its @Token ByteString@ is 'Data.Word.Word8'
-- rather than 'Char', so the same grammars do not typecheck over it.
module Main (main) where

import Control.DeepSeq   (force)
import Control.Exception (evaluate)
import Criterion.Main
import qualified Data.ByteString.Char8 as BC
import qualified Data.ByteString       as B
import qualified Data.Text             as T
import GHC.Stats          (RTSStats (..), getRTSStats)
import System.Environment (getArgs)
import System.Mem         (performGC)

import qualified Bench.Inputs as I
import qualified Bench.Mega   as M
import qualified Bench.Peg    as P

-- | Everything needed to measure one grammar on every library and stream.
data Group = Group
  { gName  :: String
  , gPegS  :: String        -> Int
  , gPegT  :: T.Text        -> Int
  , gPegB  :: B.ByteString  -> Int
  , gMegaS :: String        -> Int
  , gMegaT :: T.Text        -> Int
  }

groups :: [(Group, [String])]
groups =
  [ ( Group "arith"  P.arithS  P.arithT  P.arithB  M.runArith  M.runArith
    , map I.arithInput [50, 200, 800] )
  , ( Group "csv"    P.csvS    P.csvT    P.csvB    M.runCsv    M.runCsv
    , map (`I.csvInput` 8) [20, 100, 400] )
  , ( Group "idents" P.identsS P.identsT P.identsB M.runIdents M.runIdents
    , map I.identInput [100, 500, 2000] )
  , ( Group "json"   P.jsonS   P.jsonT   P.jsonB   M.runJson   M.runJson
    , map I.jsonInput [10, 50, 200] )
  , ( Group "nested" P.arithS  P.arithT  P.arithB  M.runArith  M.runArith
    , map I.nestedInput [50, 200] )
    -- The same language spelled two ways in typed-peg, against one megaparsec
    -- parser: this isolates the cost of the negative-lookahead idiom.
  , ( Group "quoted-lookahead" P.quotedNotS P.quotedNotT P.quotedNotB
                               M.runQuoted  M.runQuoted
    , map I.quotedInput [50, 200] )
  , ( Group "quoted-class"     P.quotedClsS P.quotedClsT P.quotedClsB
                               M.runQuoted  M.runQuoted
    , map I.quotedInput [50, 200] )
  ]

label :: Group -> String -> String
label g input = gName g ++ " [" ++ show (length input) ++ "B]"

--------------------------------------------------------------------------------
-- Cross-check: every library and every stream must agree before anything is
-- timed, otherwise the measurements compare different amounts of work.
--------------------------------------------------------------------------------

verify :: Group -> String -> IO ()
verify g input = do
  let ps = gPegS  g input
      pt = gPegT  g (T.pack input)
      pb = gPegB  g (BC.pack input)
      ms = gMegaS g input
      mt = gMegaT g (T.pack input)
  if all (== ps) [pt, pb, ms, mt]
    then putStrLn ("  ok  " ++ label g input ++ " -> " ++ show ps)
    else error ("MISMATCH in " ++ label g input
                  ++ ": peg(String)=" ++ show ps
                  ++ " peg(Text)="    ++ show pt
                  ++ " peg(BS)="      ++ show pb
                  ++ " mega(String)=" ++ show ms
                  ++ " mega(Text)="   ++ show mt)

verifyAll :: IO ()
verifyAll = do
  putStrLn "== cross-checking typed-peg against megaparsec, on every stream =="
  sequence_ [ verify g i | (g, is) <- groups, i <- is ]
  putStrLn ""

--------------------------------------------------------------------------------
-- Allocation report
--
-- @cabal bench --benchmark-options=--alloc@ prints bytes allocated per parse
-- instead of running criterion.  Allocation is deterministic, so it is the
-- measurement to trust when the timings are noisy.
--------------------------------------------------------------------------------

allocFor :: (a -> Int) -> a -> IO Integer
allocFor f x = do
  performGC
  before <- getRTSStats
  n <- evaluate (f x)
  n `seq` performGC
  after <- getRTSStats
  pure (fromIntegral (allocated_bytes after - allocated_bytes before))

allocRow :: Group -> String -> IO ()
allocRow g input = do
  s <- evaluate (force input)
  t <- evaluate (force (T.pack input))
  b <- evaluate (force (BC.pack input))
  aps <- allocFor (gPegS  g) s
  apt <- allocFor (gPegT  g) t
  apb <- allocFor (gPegB  g) b
  ams <- allocFor (gMegaS g) s
  amt <- allocFor (gMegaT g) t
  let n = fromIntegral (length input) :: Double
      per v = rjust 9 (showF (fromIntegral v / n))
  putStrLn (concat
    [ pad 24 (label g input)
    , per aps, per apt, per apb, per ams, per amt ])
  where
    pad k x   = x ++ replicate (k - length x) ' '
    rjust k x = replicate (k - length x) ' ' ++ x
    showF v   = show (fromIntegral (round (v * 10) :: Int) / 10 :: Double)

allocReport :: IO ()
allocReport = do
  putStrLn "bytes allocated per input byte"
  putStrLn (concat [ replicate 24 ' '
                   , "  peg/Str", "  peg/Txt", "   peg/BS"
                   , " mega/Str", " mega/Txt" ])
  sequence_ [ allocRow g i | (g, is) <- groups, i <- is ]

--------------------------------------------------------------------------------

main :: IO ()
main = do
  args <- getArgs
  if "--alloc" `elem` args
    then allocReport
    else verifyAll >> defaultMain benchmarks

benchmarks :: [Benchmark]
benchmarks =
  [ bgroup (gName g)
      [ env (prepare input) $ \ ~(s, t, b) ->
          bgroup (label g input)
            [ bench "typed-peg   (String)"     $ whnf (gPegS  g) s
            , bench "typed-peg   (Text)"       $ whnf (gPegT  g) t
            , bench "typed-peg   (ByteString)" $ whnf (gPegB  g) b
            , bench "megaparsec  (String)"     $ whnf (gMegaS g) s
            , bench "megaparsec  (Text)"       $ whnf (gMegaT g) t
            ]
      | input <- is
      ]
  | (g, is) <- groups
  ]

prepare :: String -> IO (String, T.Text, B.ByteString)
prepare s = do
  s' <- evaluate (force s)
  t' <- evaluate (force (T.pack s))
  b' <- evaluate (force (BC.pack s))
  pure (s', t', b')
