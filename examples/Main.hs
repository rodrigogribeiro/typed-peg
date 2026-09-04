module Main where

import PEG (parse, parseWith, Result(..))
import Arith (arith, evalExp)
import Layout (doExp, layoutOpts)
import Compat (compatMain)
import Patterns (patternsMain)

showResult :: Show a => Result String a -> String
showResult (OK a _ _) = "OK " ++ show a
showResult Fail        = "Fail"

main :: IO ()
main = do
  putStrLn "=== Arith ==="
  let testArith s =
        let r = case parse arith s of
                  OK e _ _ -> "OK " ++ show (evalExp e)
                  Fail      -> "Fail"
        in putStrLn $ s ++ " => " ++ r
  testArith "1+2*3"
  testArith "(1+2)*3"
  testArith "42"

  putStrLn "\n=== Layout (do-notation) ==="
  let testLayout s = putStrLn $ showResult (parseWith layoutOpts doExp s)
  testLayout "foo\n  bar\n  baz\nqux"

  putStrLn "\n=== Patterns (see peg-patterns.md) ==="
  patternsMain

  putStrLn "\n=== Differential battery ==="
  compatMain
