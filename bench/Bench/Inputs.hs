-- | Deterministic input generators shared by the typed-peg and megaparsec
-- benchmark groups.  Everything is pure and reproducible (a small LCG), so
-- both libraries are always measured on byte-identical inputs.
module Bench.Inputs
  ( arithInput
  , csvInput
  , identInput
  , jsonInput
  , nestedInput
  , quotedInput
  ) where

-- | A tiny linear congruential generator (glibc constants) so the benchmark
-- inputs do not depend on @random@.
lcg :: Int -> Int
lcg s = (1103515245 * s + 12345) `mod` 2147483648

randoms :: Int -> [Int]
randoms = drop 1 . iterate lcg

-- | @arithInput n@ builds an arithmetic expression with @n@ operands, mixing
-- binary operators, parentheses and unary minus.
arithInput :: Int -> String
arithInput n = go n (randoms 7)
  where
    go k rs
      | k <= 1    = operand rs
      | otherwise = case drop 2 rs of
          (r : rs') -> operand rs ++ ["+-*/" !! (r `mod` 4)] ++ go (k - 1) rs'
          []        -> operand rs

    operand (r : s : _) = case r `mod` 8 of
      0 -> "(" ++ show (s `mod` 1000) ++ "+" ++ show (s `mod` 97) ++ ")"
      1 -> "-" ++ show (s `mod` 1000)
      _ -> show (s `mod` 100000)
    operand _ = "0"

-- | @csvInput rows cols@ builds @rows@ lines of @cols@ comma-separated
-- integers.
csvInput :: Int -> Int -> String
csvInput rows cols =
  intercalate' "\n"
    [ intercalate' "," [ show (v `mod` 1000000) | v <- take cols (drop (r * cols) vs) ]
    | r <- [0 .. rows - 1]
    ]
  where
    vs = randoms 42

-- | @identInput n@ builds @n@ space-separated identifiers.  Identifiers use a
-- wide character class (@[a-zA-Z0-9_]@), which is the worst case for a parser
-- that expands classes into a chain of ordered choices.
identInput :: Int -> String
identInput n = unwords' [ ident v | v <- take n (randoms 3) ]
  where
    alphabet = ['a' .. 'z'] ++ ['A' .. 'Z'] ++ ['0' .. '9'] ++ "_"
    ident v  = 'z' : [ alphabet !! ((v `div` (7 ^ k)) `mod` length alphabet)
                     | k <- [1 .. 6 :: Int] ]

-- | @jsonInput n@ builds a JSON array of @n@ small objects.
jsonInput :: Int -> String
jsonInput n =
  "[" ++ intercalate' ",\n " [ obj v | v <- take n (randoms 11) ] ++ "]"
  where
    obj v = "{\"id\": " ++ show (v `mod` 100000)
         ++ ", \"name\": \"item" ++ show (v `mod` 997) ++ "\""
         ++ ", \"tags\": [" ++ intercalate' ", " [ show (t :: Int) | t <- [1 .. 3] ] ++ "]"
         ++ ", \"ok\": " ++ (if even v then "true" else "false")
         ++ ", \"extra\": null}"

-- | @quotedInput n@ builds @n@ space-separated double-quoted strings.  Used to
-- compare the two ways of spelling \"any character but a quote\": the PEG
-- idiom @(!'\"' .)*@, which scans every character twice, against the negated
-- character class @[^\"]*@.
quotedInput :: Int -> String
quotedInput n = unwords' [ "\"" ++ body v ++ "\"" | v <- take n (randoms 23) ]
  where
    body v = [ alphabet !! ((v `div` (5 ^ k)) `mod` length alphabet)
             | k <- [1 .. 12 :: Int] ]
    alphabet = ['a' .. 'z'] ++ ['A' .. 'Z'] ++ " ,.;:!?-"

-- | @nestedInput d@ builds @d@ nested parentheses around a literal.  This is
-- the deep-recursion / backtracking stress case for the arithmetic grammar.
nestedInput :: Int -> String
nestedInput d = replicate d '(' ++ "1" ++ replicate d ')'

intercalate' :: String -> [String] -> String
intercalate' _   []       = []
intercalate' _   [x]      = x
intercalate' sep (x : xs) = x ++ sep ++ intercalate' sep xs

unwords' :: [String] -> String
unwords' = intercalate' " "
