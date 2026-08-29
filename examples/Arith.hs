{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE QuasiQuotes           #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# OPTIONS_GHC -Wno-partial-type-signatures #-}

module Arith
  ( Exp (..)
  , evalExp
  , showExp
  , ArithEnv
  , arith
  ) where

import PEG
import PEG.QQ (pegRules)

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

type ArithEnv =
  '[ '("expr"  , 'EnvEntry ('MkTy 'False '["term", "factor", "number"]) Exp)
   , '("term"  , 'EnvEntry ('MkTy 'False '["factor", "number"])         Exp)
   , '("factor", 'EnvEntry ('MkTy 'False '["number"])                   Exp)
   , '("number", 'EnvEntry ('MkTy 'False '[])                           Exp)
   ]

arith :: Grammar ArithEnv _ Exp
arith =
  Grammar
    [pegRules|
       expr   <- t:term ts:(o:[+-] u:term)* { foldl addOp t ts }
       term   <- f:factor fs:(o:[*/] g:factor)*
                   { foldl (\acc (op, r) -> addOp acc (op, r)) f fs }
       factor <- n:number
               / '(' e:expr ')'
               / '-' f:factor { Neg f }
       number <- ds:[0-9]+ { Lit (read ds :: Int) }
    |]
    (nt @"expr")
