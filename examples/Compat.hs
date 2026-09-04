{-# LANGUAGE OverloadedStrings      #-}
{-# LANGUAGE PartialTypeSignatures  #-}
{-# LANGUAGE QuasiQuotes            #-}
{-# LANGUAGE RankNTypes             #-}
{-# LANGUAGE ScopedTypeVariables    #-}
{-# OPTIONS_GHC -Wno-partial-type-signatures #-}

-- | A differential test: it renders the complete 'Result' (value, consumed
-- prefix and remaining suffix) for a fixed battery of inputs.
--
-- It serves two purposes.
--
-- * The output is compared byte-for-byte between successive versions of the
--   evaluator, which is how the optimisation work was checked for behavioural
--   drift — including the layout-sensitive paths that the other examples do
--   not exercise.
--
-- * The same battery is run over 'String', 'Data.Text.Text' and
--   'Data.ByteString.ByteString', and the three renderings must agree.  That
--   is what pins the "PEG.Stream" instances to each other: a stream whose
--   @spanS@ or column bookkeeping is wrong shows up here as a diff.
--
-- The renderings can be compared directly because 'Show' for 'Data.Text.Text'
-- and 'Data.ByteString.ByteString' agrees with 'Show' for 'String' on the
-- Latin-1 range, which is all these inputs use.
module Compat (compatMain) where

import qualified Data.ByteString.Char8 as BC
import qualified Data.Text             as T

import PEG
import PEG.QQ (pegExpr, pegRules)
import Arith  (arith, Exp)
import Layout (DoStmt, doExp, layoutOpts)

showR :: (Show s, Show a) => Result s a -> String
showR (OK a c r) = "OK " ++ show a ++ " consumed=" ++ show c ++ " rest=" ++ show r
showR Fail       = "Fail"

arithCases :: [String]
arithCases =
  [ "1+2*3", "(1+2)*3", "42", "-7", "1+", "", "((((1))))"
  , "1+2)rest", "12*34/5-6", "9"
  , "1+2*3+4*5+6/7-8", "(((1+2)*(3+4))-(5*6))"
  , "0000123", "1--2", "-(1+2)"
  ]

layoutCases :: [String]
layoutCases =
  [ "do\n  foo\n  bar"
  , "do\n  foo\n  bar\nbaz"
  , "do { foo ; bar }"
  , "do\n  foo\n  do\n    bar\n  baz"
  , "do\n foo\n  bar"
  , "do\n\tfoo\n\tbar"
  , "do foo bar"
  , "do"
  , "  do\n    a\n    b"
  , "do\n  a\n b"
  , "do { a }"
  , "do\n  do\n    x"
  ]

-- Several option sets, so tab expansion and the token relation are covered.
optSets :: [(String, Opts)]
optSets =
  [ ("layout(ge,tab8)" , layoutOpts)
  , ("layout(ge,tab4)" , layoutOpts  { optTabWidth  = 4 })
  , ("layout(ge,tab1)" , layoutOpts  { optTabWidth  = 1 })
  , ("layout(gt)"      , layoutOpts  { optTokenMode = relD gtR })
  , ("layout(eq)"      , layoutOpts  { optTokenMode = relD eqR })
  , ("layout(any)"     , defaultOpts)
  , ("layout(off2)"    , layoutOpts  { optTokenMode = relD (offsetR 2) })
  , ("layout(cands)"   , layoutOpts  { optCands     = Interval 1 (Fin 20) })
  ]

-- | Chunk primitives and the lookaheads over them.
--
-- @Span@ and @Span1@ are what a character-class repetition compiles to, and
-- @!c+@ / @!c*@ have dedicated compile cases; nothing else in the battery
-- reaches them.  @!c*@ can never succeed, because the star matches the empty
-- run.
type SpanEnv s =
  '[ '("digits", 'EnvEntry ('MkTy 'True  '[]) s)
   , '("digits1", 'EnvEntry ('MkTy 'False '[]) s)
   ]

spanG :: Stream s => Grammar s (SpanEnv s) _ (s, s)
spanG =
  Grammar
    [pegRules|
       digits  <- ds:[0-9]*   { ds }
       digits1 <- ds:[0-9]+   { ds }
    |]
    [pegExpr| a:digits '/' b:digits1 |]

-- @!'x'+ .@ accepts any character that is not an @x@; @!'x'* .@ accepts
-- nothing at all.
notSpan1G :: Stream s => Grammar s '[] _ Char
notSpan1G = Grammar RNil [pegExpr| !'x'+ c:. |]

notSpanG :: Stream s => Grammar s '[] _ Char
notSpanG = Grammar RNil [pegExpr| !'x'* c:. |]

spanCases :: [String]
spanCases = ["/1", "12/34", "/", "12/", "abc", "", "007/8"]

notCases :: [String]
notCases = ["y", "x", "", "yx"]

-- | The whole battery, rendered as lines, for one stream type.
--
-- @pack@ is the only stream-specific part; everything else is the same code
-- running at a different instance.
battery :: forall s. (Stream s, Show s) => (String -> s) -> [String]
battery pack =
  [ "### arith (defaultOpts)" ]
  ++ [ show s ++ " => " ++ showR (parse arith (pack s) :: Result s Exp)
     | s <- arithCases ]
  ++ [ "### arith (varying Opts)" ]
  ++ [ nm ++ " " ++ show s ++ " => "
         ++ showR (parseWith o arith (pack s) :: Result s Exp)
     | (nm, o) <- optSets, s <- arithCases ]
  ++ [ "### span primitives" ]
  ++ [ show c ++ " => " ++ showR (parse spanG (pack c) :: Result s (s, s))
     | c <- spanCases ]
  ++ [ "### !c+ (peek) and !c* (never succeeds)" ]
  ++ [ show c ++ " => " ++ showR (parse notSpan1G (pack c) :: Result s Char)
         ++ " | " ++ showR (parse notSpanG (pack c) :: Result s Char)
     | c <- notCases ]
  ++ [ "### layout" ]
  ++ [ nm ++ " " ++ show s ++ " => "
         ++ showR (parseWith o doExp (pack s) :: Result s [DoStmt])
     | (nm, o) <- optSets, s <- layoutCases ]

-- | Print the 'String' rendering — this is the output compared against
-- previous versions of the evaluator — then check the other two streams
-- against it.
compatMain :: IO ()
compatMain = do
  let reference = battery id
  mapM_ putStrLn reference

  putStrLn "### stream agreement"
  agree "Data.Text.Text"             reference (battery T.pack)
  agree "Data.ByteString.ByteString" reference (battery BC.pack)

-- | Report the first disagreement, if any.  A count alone would say that
-- something is wrong without saying what, and these are 234 dense lines.
agree :: String -> [String] -> [String] -> IO ()
agree name reference actual =
  case [ (i, r, a)
       | (i, r, a) <- zip3 [1 :: Int ..] reference actual, r /= a ] of
    [] | length reference == length actual ->
           putStrLn (name ++ ": agrees with String on all "
                       ++ show (length reference) ++ " lines")
       | otherwise ->
           putStrLn (name ++ ": MISMATCH in length, " ++ show (length reference)
                       ++ " vs " ++ show (length actual))
    ((i, r, a) : rest) -> do
      putStrLn (name ++ ": MISMATCH on " ++ show (length rest + 1)
                  ++ " line(s), first at line " ++ show i)
      putStrLn ("  String: " ++ r)
      putStrLn ("  " ++ name ++ ": " ++ a)
