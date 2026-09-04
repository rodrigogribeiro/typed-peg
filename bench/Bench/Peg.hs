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
  , arithS, csvS, identsS, jsonS, quotedNotS, quotedClsS
  , arithT, csvT, identsT, jsonT, quotedNotT, quotedClsT
  , arithB, csvB, identsB, jsonB, quotedNotB, quotedClsB
  ) where

import qualified Data.ByteString as B
import qualified Data.Text       as T

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

readInt :: Stream s => s -> Exp
readInt ds = Lit (read (chunkToString ds))

type ArithEnv =
  '[ '("expr"  , 'EnvEntry ('MkTy 'False '["term", "factor", "number"]) Exp)
   , '("term"  , 'EnvEntry ('MkTy 'False '["factor", "number"])         Exp)
   , '("factor", 'EnvEntry ('MkTy 'False '["number"])                   Exp)
   , '("number", 'EnvEntry ('MkTy 'False '[])                           Exp)
   ]

{-# INLINABLE arith #-}
arith :: Stream s => Grammar s ArithEnv _ Exp
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

{-# INLINABLE csv #-}
csv :: Stream s => Grammar s CsvEnv _ [[Int]]
csv =
  Grammar
    [pegRules|
       csv <- r:row rs:('\n' t:row)* { r : rs }
       row <- n:num ns:(',' m:num)*  { n : ns }
       num <- ds:[0-9]+              { readNat ds }
    |]
    (nt @"csv")

readNat :: Stream s => s -> Int
readNat = read . chunkToString

--------------------------------------------------------------------------------
-- Identifier list (wide character classes)
--------------------------------------------------------------------------------

-- The environment is parameterised by the stream: @ident@ is a character
-- class, so its result is a chunk of the input.
type IdentEnv s =
  '[ '("idents", 'EnvEntry ('MkTy 'False '["ident"]) [s])
   , '("ident" , 'EnvEntry ('MkTy 'False '[])        s)
   ]

{-# INLINABLE idents #-}
idents :: Stream s => Grammar s (IdentEnv s) _ [s]
idents =
  Grammar
    [pegRules|
       idents <- i:ident is:(' ' j:ident)*     { i : is }
       ident  <- &[a-zA-Z_] cs:[a-zA-Z0-9_]+   { cs }
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

mkNum :: Stream s => Maybe Char -> s -> JValue
mkNum Nothing  ds = JNum (read (chunkToString ds))
mkNum (Just _) ds = JNum (negate (read (chunkToString ds)))

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

{-# INLINABLE json #-}
json :: Stream s => Grammar s JsonEnv _ JValue
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

-- @(!'"' .)*@ is a compound repetition, so it still yields a @['Char']@ ...
type QuotedNotEnv =
  '[ '("qs", 'EnvEntry ('MkTy 'False '["q"]) [String])
   , '("q" , 'EnvEntry ('MkTy 'False '[])    String)
   ]

-- ... whereas @[^"]*@ is a character class and yields a chunk.
type QuotedClsEnv s =
  '[ '("qs", 'EnvEntry ('MkTy 'False '["q"]) [s])
   , '("q" , 'EnvEntry ('MkTy 'False '[])    s)
   ]

{-# INLINABLE quotedNot #-}
quotedNot :: Stream s => Grammar s QuotedNotEnv _ [String]
quotedNot =
  Grammar
    [pegRules|
       qs <- s:q ss:(' ' t:q)*      { s : ss }
       q  <- '"' cs:(!'"' c:.)* '"' { cs }
    |]
    (nt @"qs")

{-# INLINABLE quotedCls #-}
quotedCls :: Stream s => Grammar s (QuotedClsEnv s) _ [s]
quotedCls =
  Grammar
    [pegRules|
       qs <- s:q ss:(' ' t:q)*      { s : ss }
       q  <- '"' cs:[^"]* '"'       { cs }
    |]
    (nt @"qs")

--------------------------------------------------------------------------------
-- Runners (force the result so criterion measures the whole parse)
--
-- Each parser is bound monomorphically at each stream type.  That matters: a
-- grammar left polymorphic in its stream is a function of a 'Stream'
-- dictionary rather than a constant, so the compiled parser would be rebuilt
-- on every call.  NOINLINE keeps each one a shared CAF, so the measurement is
-- of parsing rather than of re-traversing the grammar.
--------------------------------------------------------------------------------

runArith :: Stream s => (s -> Result s Exp) -> s -> Int
runArith p s = case p s of
  OK e _ _ -> evalExp e
  Fail     -> error "runArith: parse failed"
{-# INLINE runArith #-}

runCsv :: Stream s => (s -> Result s [[Int]]) -> s -> Int
runCsv p s = case p s of
  OK rs _ _ -> sum (map sum rs)
  Fail      -> error "runCsv: parse failed"
{-# INLINE runCsv #-}

runIdents :: Stream s => (s -> Result s [s]) -> s -> Int
runIdents p s = case p s of
  OK is _ _ -> sum (map lengthS is)
  Fail      -> error "runIdents: parse failed"
{-# INLINE runIdents #-}

runJson :: Stream s => (s -> Result s JValue) -> s -> Int
runJson p s = case p s of
  OK v _ _ -> sizeJ v
  Fail     -> error "runJson: parse failed"
{-# INLINE runJson #-}

runQuotedNot :: Stream s => (s -> Result s [String]) -> s -> Int
runQuotedNot p s = case p s of
  OK xs _ _ -> sum (map length xs)
  Fail      -> error "runQuotedNot: parse failed"
{-# INLINE runQuotedNot #-}

runQuotedCls :: Stream s => (s -> Result s [s]) -> s -> Int
runQuotedCls p s = case p s of
  OK xs _ _ -> sum (map lengthS xs)
  Fail      -> error "runQuotedCls: parse failed"
{-# INLINE runQuotedCls #-}

sizeJ :: JValue -> Int
sizeJ JNull      = 1
sizeJ (JBool _)  = 1
sizeJ (JNum n)   = n
sizeJ (JStr t)   = length t
sizeJ (JArr xs)  = 1 + sum (map sizeJ xs)
sizeJ (JObj ps)  = 1 + sum [ length k + sizeJ v | (k, v) <- ps ]

--------------------------------------------------------------------------------
-- Monomorphic entry points, one set per stream.
--
-- The parser must be bound as its own CAF.  Writing @arithS = runArith (parse
-- arith)@ instead lets GHC eta-expand to @\s -> case parse arith s of ...@,
-- which rebuilds the compiled parser on every single call -- a 2.5x slowdown
-- that no amount of specialisation recovers.
--------------------------------------------------------------------------------

pArithS :: String -> Result String Exp
pArithS = parse arith
{-# NOINLINE pArithS #-}

arithS :: String -> Int
arithS = runArith pArithS

pCsvS :: String -> Result String [[Int]]
pCsvS = parse csv
{-# NOINLINE pCsvS #-}

csvS :: String -> Int
csvS = runCsv pCsvS

pJsonS :: String -> Result String JValue
pJsonS = parse json
{-# NOINLINE pJsonS #-}

jsonS :: String -> Int
jsonS = runJson pJsonS

pQuotedNotS :: String -> Result String [String]
pQuotedNotS = parse quotedNot
{-# NOINLINE pQuotedNotS #-}

quotedNotS :: String -> Int
quotedNotS = runQuotedNot pQuotedNotS

pIdentsS :: String -> Result String [String]
pIdentsS = parse idents
{-# NOINLINE pIdentsS #-}

identsS :: String -> Int
identsS = runIdents pIdentsS

pQuotedClsS :: String -> Result String [String]
pQuotedClsS = parse quotedCls
{-# NOINLINE pQuotedClsS #-}

quotedClsS :: String -> Int
quotedClsS = runQuotedCls pQuotedClsS

pArithT :: T.Text -> Result T.Text Exp
pArithT = parse arith
{-# NOINLINE pArithT #-}

arithT :: T.Text -> Int
arithT = runArith pArithT

pCsvT :: T.Text -> Result T.Text [[Int]]
pCsvT = parse csv
{-# NOINLINE pCsvT #-}

csvT :: T.Text -> Int
csvT = runCsv pCsvT

pJsonT :: T.Text -> Result T.Text JValue
pJsonT = parse json
{-# NOINLINE pJsonT #-}

jsonT :: T.Text -> Int
jsonT = runJson pJsonT

pQuotedNotT :: T.Text -> Result T.Text [String]
pQuotedNotT = parse quotedNot
{-# NOINLINE pQuotedNotT #-}

quotedNotT :: T.Text -> Int
quotedNotT = runQuotedNot pQuotedNotT

pIdentsT :: T.Text -> Result T.Text [T.Text]
pIdentsT = parse idents
{-# NOINLINE pIdentsT #-}

identsT :: T.Text -> Int
identsT = runIdents pIdentsT

pQuotedClsT :: T.Text -> Result T.Text [T.Text]
pQuotedClsT = parse quotedCls
{-# NOINLINE pQuotedClsT #-}

quotedClsT :: T.Text -> Int
quotedClsT = runQuotedCls pQuotedClsT

pArithB :: B.ByteString -> Result B.ByteString Exp
pArithB = parse arith
{-# NOINLINE pArithB #-}

arithB :: B.ByteString -> Int
arithB = runArith pArithB

pCsvB :: B.ByteString -> Result B.ByteString [[Int]]
pCsvB = parse csv
{-# NOINLINE pCsvB #-}

csvB :: B.ByteString -> Int
csvB = runCsv pCsvB

pJsonB :: B.ByteString -> Result B.ByteString JValue
pJsonB = parse json
{-# NOINLINE pJsonB #-}

jsonB :: B.ByteString -> Int
jsonB = runJson pJsonB

pQuotedNotB :: B.ByteString -> Result B.ByteString [String]
pQuotedNotB = parse quotedNot
{-# NOINLINE pQuotedNotB #-}

quotedNotB :: B.ByteString -> Int
quotedNotB = runQuotedNot pQuotedNotB

pIdentsB :: B.ByteString -> Result B.ByteString [B.ByteString]
pIdentsB = parse idents
{-# NOINLINE pIdentsB #-}

identsB :: B.ByteString -> Int
identsB = runIdents pIdentsB

pQuotedClsB :: B.ByteString -> Result B.ByteString [B.ByteString]
pQuotedClsB = parse quotedCls
{-# NOINLINE pQuotedClsB #-}

quotedClsB :: B.ByteString -> Int
quotedClsB = runQuotedCls pQuotedClsB
