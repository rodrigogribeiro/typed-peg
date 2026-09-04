-- | A differential test: it prints the complete 'Result' (value, consumed
-- prefix and remaining suffix) for a fixed battery of inputs.  The output is
-- compared byte-for-byte between the old and the new evaluator, which is how
-- the optimisation work was checked for behavioural drift — including the
-- layout-sensitive paths that the other examples do not exercise.
module Compat (compatMain) where

import PEG
import Arith  (arith, Exp)
import Layout (DoStmt, doExp, layoutOpts)

showR :: Show a => Result a -> String
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

compatMain :: IO ()
compatMain = do
  putStrLn "### arith (defaultOpts)"
  mapM_ (\s -> putStrLn (show s ++ " => " ++ showR (parse arith s :: Result Exp)))
        arithCases

  putStrLn "### arith (varying Opts)"
  sequence_
    [ putStrLn (nm ++ " " ++ show s ++ " => "
                  ++ showR (parseWith o arith s :: Result Exp))
    | (nm, o) <- optSets, s <- arithCases ]

  putStrLn "### layout"
  sequence_
    [ putStrLn (nm ++ " " ++ show s ++ " => "
                  ++ showR (parseWith o doExp s :: Result [DoStmt]))
    | (nm, o) <- optSets, s <- layoutCases ]
