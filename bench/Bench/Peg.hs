{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE QuasiQuotes           #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# OPTIONS_GHC -Wno-partial-type-signatures #-}
{-# OPTIONS_GHC -Wno-missing-signatures #-}

-- | The typed-peg side of the benchmark suite.  Every grammar here has a
-- structurally identical megaparsec counterpart in "Bench.Mega".
module Bench.Peg
  ( Exp (..)
  , evalExp
  , arith
  , csv
  , idents
  , JValue (..)
  , json
  , runArith
  , runCsv
  , runIdents
  , runJson
  , runQuotedNot
  , runQuotedCls
  ) where

import PEG
import PEG.QQ (pegRules)

--------------------------------------------------------------------------------
-- Arithmetic expressions
--------------------------------------------------------------------------------

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
evalExp (Div a b) = let d = evalExp b in if d == 0 then 0 else evalExp a `div` d

addOp :: Exp -> (Char, Exp) -> Exp
addOp l ('+', r) = Add l r
addOp l ('-', r) = Sub l r
addOp l ('*', r) = Mul l r
addOp l ('/', r) = Div l r
addOp _ (c  , _) = error ("addOp: unexpected operator " ++ show c)

foldOps :: Exp -> [(Char, Exp)] -> Exp
foldOps = foldl addOp

readInt :: String -> Exp
readInt ds = Lit (read ds)

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
       expr   <- t:term ts:(o:[+-] u:term)*   { foldOps t ts }
       term   <- f:factor fs:(o:[*/] g:factor)* { foldOps f fs }
       factor <- n:number
               / '(' e:expr ')'
               / '-' f:factor                 { Neg f }
       number <- ds:[0-9]+                    { readInt ds }
    |]
    (nt @"expr")

--------------------------------------------------------------------------------
-- CSV of integers
--------------------------------------------------------------------------------

type CsvEnv =
  '[ '("csv", 'EnvEntry ('MkTy 'False '["row", "num"]) [[Int]])
   , '("row", 'EnvEntry ('MkTy 'False '["num"])        [Int])
   , '("num", 'EnvEntry ('MkTy 'False '[])             Int)
   ]

csv :: Grammar CsvEnv _ [[Int]]
csv =
  Grammar
    [pegRules|
       csv <- r:row rs:('\n' t:row)* { r : rs }
       row <- n:num ns:(',' m:num)*  { n : ns }
       num <- ds:[0-9]+              { readNat ds }
    |]
    (nt @"csv")

readNat :: String -> Int
readNat = read

--------------------------------------------------------------------------------
-- Identifier list (wide character classes)
--------------------------------------------------------------------------------

type IdentEnv =
  '[ '("idents", 'EnvEntry ('MkTy 'False '["ident"]) [String])
   , '("ident" , 'EnvEntry ('MkTy 'False '[])        String)
   ]

idents :: Grammar IdentEnv _ [String]
idents =
  Grammar
    [pegRules|
       idents <- i:ident is:(' ' j:ident)*     { i : is }
       ident  <- c:[a-zA-Z_] cs:[a-zA-Z0-9_]*  { c : cs }
    |]
    (nt @"idents")

--------------------------------------------------------------------------------
-- Mini JSON
--------------------------------------------------------------------------------

data JValue
  = JNull
  | JBool Bool
  | JNum  Int
  | JStr  String
  | JArr  [JValue]
  | JObj  [(String, JValue)]
  deriving (Eq, Show)

mkNum :: Maybe Char -> String -> JValue
mkNum Nothing  ds = JNum (read ds)
mkNum (Just _) ds = JNum (negate (read ds))

orEmpty :: Maybe [a] -> [a]
orEmpty Nothing   = []
orEmpty (Just xs) = xs

type JsonEnv =
  '[ '("json"   , 'EnvEntry ('MkTy 'False '["ws","value","object","array","strlit","number"]) JValue)
   , '("value"  , 'EnvEntry ('MkTy 'False '["object","array","strlit","number"])              JValue)
   , '("object" , 'EnvEntry ('MkTy 'False '[])                                                JValue)
   , '("members", 'EnvEntry ('MkTy 'False '["pair","strlit"])                    [(String, JValue)])
   , '("pair"   , 'EnvEntry ('MkTy 'False '["strlit"])                             (String, JValue))
   , '("array"  , 'EnvEntry ('MkTy 'False '[])                                                JValue)
   , '("elems"  , 'EnvEntry ('MkTy 'False '["value","object","array","strlit","number"])    [JValue])
   , '("strlit" , 'EnvEntry ('MkTy 'False '[])                                                String)
   , '("number" , 'EnvEntry ('MkTy 'False '[])                                                JValue)
   , '("ws"     , 'EnvEntry ('MkTy 'True  '[])                                                    ())
   ]

json :: Grammar JsonEnv _ JValue
json =
  Grammar
    [pegRules|
       json    <- ws v:value ws                    { v }
       value   <- o:object                         { o }
                / a:array                          { a }
                / s:strlit                         { JStr s }
                / n:number                         { n }
                / "true"                           { JBool True }
                / "false"                          { JBool False }
                / "null"                           { JNull }
       object  <- '{' ws ms:members? ws '}'        { JObj (orEmpty ms) }
       members <- p:pair ps:(ws ',' ws q:pair)*    { p : ps }
       pair    <- k:strlit ws ':' ws v:value       { (k, v) }
       array   <- '[' ws es:elems? ws ']'          { JArr (orEmpty es) }
       elems   <- e:value es:(ws ',' ws f:value)*  { e : es }
       strlit  <- '"' cs:(!'"' c:.)* '"'           { cs }
       number  <- s:'-'? ds:[0-9]+                 { mkNum s ds }
       ws      <- [ \t\r\n]*
    |]
    (nt @"json")

--------------------------------------------------------------------------------
-- Quoted strings: negative lookahead vs. negated character class
--
-- Two grammars that accept exactly the same language.  The first spells
-- \"any character but a quote\" the way a PEG traditionally does, with a
-- negative lookahead; the second uses a negated character class, which
-- compiles to one 'Sat' node.
--------------------------------------------------------------------------------

type QuotedEnv =
  '[ '("qs", 'EnvEntry ('MkTy 'False '["q"]) [String])
   , '("q" , 'EnvEntry ('MkTy 'False '[])    String)
   ]

quotedNot :: Grammar QuotedEnv _ [String]
quotedNot =
  Grammar
    [pegRules|
       qs <- s:q ss:(' ' t:q)*      { s : ss }
       q  <- '"' cs:(!'"' c:.)* '"' { cs }
    |]
    (nt @"qs")

quotedCls :: Grammar QuotedEnv _ [String]
quotedCls =
  Grammar
    [pegRules|
       qs <- s:q ss:(' ' t:q)*      { s : ss }
       q  <- '"' cs:[^"]* '"'       { cs }
    |]
    (nt @"qs")

--------------------------------------------------------------------------------
-- Runners (force the result so criterion measures the whole parse)
--------------------------------------------------------------------------------

-- Bind the compiled parser once, exactly as a megaparsec user binds a
-- top-level parser value.  NOINLINE keeps it a shared CAF so the measurement
-- is of parsing, not of re-traversing the grammar.
parseArith :: String -> Result Exp
parseArith = parse arith
{-# NOINLINE parseArith #-}

parseCsv :: String -> Result [[Int]]
parseCsv = parse csv
{-# NOINLINE parseCsv #-}

parseIdents :: String -> Result [String]
parseIdents = parse idents
{-# NOINLINE parseIdents #-}

parseJson :: String -> Result JValue
parseJson = parse json
{-# NOINLINE parseJson #-}

parseQuotedNot :: String -> Result [String]
parseQuotedNot = parse quotedNot
{-# NOINLINE parseQuotedNot #-}

parseQuotedCls :: String -> Result [String]
parseQuotedCls = parse quotedCls
{-# NOINLINE parseQuotedCls #-}

runArith :: String -> Int
runArith s = case parseArith s of
  OK e _ _ -> evalExp e
  Fail     -> error "runArith: parse failed"

runCsv :: String -> Int
runCsv s = case parseCsv s of
  OK rs _ _ -> sum (map sum rs)
  Fail      -> error "runCsv: parse failed"

runIdents :: String -> Int
runIdents s = case parseIdents s of
  OK is _ _ -> sum (map length is)
  Fail      -> error "runIdents: parse failed"

runJson :: String -> Int
runJson s = case parseJson s of
  OK v _ _ -> sizeJ v
  Fail     -> error "runJson: parse failed"

runQuotedNot :: String -> Int
runQuotedNot s = case parseQuotedNot s of
  OK xs _ _ -> sum (map length xs)
  Fail      -> error "runQuotedNot: parse failed"

runQuotedCls :: String -> Int
runQuotedCls s = case parseQuotedCls s of
  OK xs _ _ -> sum (map length xs)
  Fail      -> error "runQuotedCls: parse failed"

sizeJ :: JValue -> Int
sizeJ JNull      = 1
sizeJ (JBool _)  = 1
sizeJ (JNum n)   = n
sizeJ (JStr t)   = length t
sizeJ (JArr xs)  = 1 + sum (map sizeJ xs)
sizeJ (JObj ps)  = 1 + sum [ length k + sizeJ v | (k, v) <- ps ]
