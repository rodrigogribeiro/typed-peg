{-# LANGUAGE DataKinds        #-}
{-# LANGUAGE QuasiQuotes      #-}
{-# LANGUAGE TemplateHaskell  #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators    #-}

module Arith
  ( Exp (..)
  , evalExp
  , showExp
  , ArithEnv
  , arith
  ) where

import PEG
import PEG.QQ (pegGrammar)

data Exp
  = Lit Int
  | Neg Exp
  | Add Exp Exp
  | Sub Exp Exp
  | Mul Exp Exp
  | Div Exp Exp
  deriving (Eq, Show)

evalExp :: Exp -> Int
evalExp (Lit n)   = n
evalExp (Neg e)   = negate (evalExp e)
evalExp (Add a b) = evalExp a + evalExp b
evalExp (Sub a b) = evalExp a - evalExp b
evalExp (Mul a b) = evalExp a * evalExp b
evalExp (Div a b) = evalExp a `div` evalExp b

showExp :: Exp -> String
showExp (Lit n)   = show n
showExp (Neg e)   = "(-" ++ showExp e ++ ")"
showExp (Add a b) = bin "+" a b
showExp (Sub a b) = bin "-" a b
showExp (Mul a b) = bin "*" a b
showExp (Div a b) = bin "/" a b

bin :: String -> Exp -> Exp -> String
bin op a b = "(" ++ showExp a ++ " " ++ op ++ " " ++ showExp b ++ ")"

addOp :: Exp -> (Char, Exp) -> Exp
addOp l ('+', r) = Add l r
addOp l ('-', r) = Sub l r
addOp l ('*', r) = Mul l r
addOp l ('/', r) = Div l r
addOp _ (c  , _) = error ("addOp: unexpected operator " ++ show c)

-- | The environment, the signature and the grammar are all declared by the
-- quasi-quoter.  A rule's result type is the one thing the grammar does not
-- determine, which is what the @:: T@ annotations are for; left recursion and
-- the rest are checked by 'PEG.Analysis' at the splice.
--
-- The annotations are still claims that GHC checks, not assertions:
-- 'PEG.Grammar.Grammar' demands @Rules s env env@, so an annotation that
-- disagrees with what the rule body actually returns is a type error here.
--
-- Being polymorphic in the stream has a cost: this is a function of a
-- 'Stream' dictionary rather than a constant, so the compiled parser is not
-- shared between calls.  Bind a monomorphic parser
-- (@arithString = parse arith :: String -> Result String Exp@) where that
-- matters.
[pegGrammar|
  %name  arith
  %start expr

  expr   :: Exp <- t:term ts:(o:[+-] u:term)* { foldl addOp t ts }
  term   :: Exp <- f:factor fs:(o:[*/] g:factor)*
                     { foldl (\acc (op, r) -> addOp acc (op, r)) f fs }
  factor :: Exp <- n:number
                 / '(' e:expr ')'
                 / '-' f:factor { Neg f }
  number :: Exp <- ds:[0-9]+ { Lit (read (chunkToString ds) :: Int) }
|]
