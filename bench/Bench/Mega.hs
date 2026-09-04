{-# LANGUAGE ConstraintKinds     #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies        #-}

-- | The megaparsec side of the benchmark suite.
--
-- The grammars mirror "Bench.Peg" rule-for-rule.  Because PEG ordered choice
-- backtracks unconditionally while megaparsec's '<|>' only backtracks when the
-- left branch consumed nothing, every alternative that can consume input
-- before failing is wrapped in 'try'.  Without that the two libraries would
-- not be recognising the same language.
--
-- Parsers are polymorphic in the stream so the same code can be measured over
-- 'String' (the input type typed-peg supports) and over 'Data.Text.Text' (what
-- a megaparsec user would actually reach for).
module Bench.Mega
  ( runArith
  , runCsv
  , runIdents
  , runJson
  , runQuoted
  ) where

import Data.Char             (isAlphaNum, isAlpha, isDigit)
import Data.String           (IsString)
import Data.Void             (Void)
import Text.Megaparsec
import Text.Megaparsec.Char  (char, string)

import Bench.Peg (Exp (..), JValue (..), evalExp)

type Str s = ( Stream s, VisualStream s, TraversableStream s
              , Token s ~ Char, IsString (Tokens s), Ord (Token s) )

type P s = Parsec Void s

--------------------------------------------------------------------------------
-- Arithmetic expressions
--------------------------------------------------------------------------------

addOp :: Exp -> (Char, Exp) -> Exp
addOp l ('+', r) = Add l r
addOp l ('-', r) = Sub l r
addOp l ('*', r) = Mul l r
addOp l ('/', r) = Div l r
addOp _ (c  , _) = error ("addOp: unexpected operator " ++ show c)

exprP :: Str s => P s Exp
exprP = foldl addOp <$> termP <*> many (try ((,) <$> satisfy addSym <*> termP))
  where addSym c = c == '+' || c == '-'

termP :: Str s => P s Exp
termP = foldl addOp <$> factorP <*> many (try ((,) <$> satisfy mulSym <*> factorP))
  where mulSym c = c == '*' || c == '/'

factorP :: Str s => P s Exp
factorP =
      try numberP
  <|> try (char '(' *> exprP <* char ')')
  <|> (Neg <$> (char '-' *> factorP))

numberP :: Str s => P s Exp
numberP = (Lit . read) <$> some (satisfy isDigit)

--------------------------------------------------------------------------------
-- CSV of integers
--------------------------------------------------------------------------------

csvP :: Str s => P s [[Int]]
csvP = (:) <$> rowP <*> many (try (char '\n' *> rowP))

rowP :: Str s => P s [Int]
rowP = (:) <$> natP <*> many (try (char ',' *> natP))

natP :: Str s => P s Int
natP = read <$> some (satisfy isDigit)

--------------------------------------------------------------------------------
-- Identifier list
--------------------------------------------------------------------------------

identsP :: Str s => P s [String]
identsP = (:) <$> identP <*> many (try (char ' ' *> identP))

identP :: Str s => P s String
identP = (:) <$> satisfy startC <*> many (satisfy contC)
  where
    startC c = isAlpha c || c == '_'
    contC  c = isAlphaNum c || c == '_'

--------------------------------------------------------------------------------
-- Mini JSON
--------------------------------------------------------------------------------

wsP :: Str s => P s ()
wsP = () <$ takeWhileP Nothing isSpace'
  where isSpace' c = c == ' ' || c == '\t' || c == '\r' || c == '\n'

jsonP :: Str s => P s JValue
jsonP = wsP *> valueP <* wsP

valueP :: Str s => P s JValue
valueP =
      try objectP
  <|> try arrayP
  <|> try (JStr <$> strP)
  <|> try numberJP
  <|> try (JBool True  <$ string "true")
  <|> try (JBool False <$ string "false")
  <|> (JNull <$ string "null")

objectP :: Str s => P s JValue
objectP =
  JObj . orEmpty
    <$> (char '{' *> wsP *> optional (try membersP) <* wsP <* char '}')

membersP :: Str s => P s [(String, JValue)]
membersP = (:) <$> pairP <*> many (try (wsP *> char ',' *> wsP *> pairP))

pairP :: Str s => P s (String, JValue)
pairP = (,) <$> strP <*> (wsP *> char ':' *> wsP *> valueP)

arrayP :: Str s => P s JValue
arrayP =
  JArr . orEmpty
    <$> (char '[' *> wsP *> optional (try elemsP) <* wsP <* char ']')

elemsP :: Str s => P s [JValue]
elemsP = (:) <$> valueP <*> many (try (wsP *> char ',' *> wsP *> valueP))

strP :: Str s => P s String
strP = char '"' *> many (satisfy (/= '"')) <* char '"'

numberJP :: Str s => P s JValue
numberJP = mk <$> optional (char '-') <*> some (satisfy isDigit)
  where
    mk Nothing  ds = JNum (read ds)
    mk (Just _) ds = JNum (negate (read ds))

orEmpty :: Maybe [a] -> [a]
orEmpty Nothing   = []
orEmpty (Just xs) = xs

--------------------------------------------------------------------------------
-- Quoted strings
--------------------------------------------------------------------------------

quotedP :: Str s => P s [String]
quotedP = (:) <$> qP <*> many (try (char ' ' *> qP))

qP :: Str s => P s String
qP = char '"' *> many (satisfy (/= '"')) <* char '"'

--------------------------------------------------------------------------------
-- Runners
--------------------------------------------------------------------------------

run :: Str s => P s a -> (a -> Int) -> String -> s -> Int
run p k what s = case runParser p "<bench>" s of
  Left  e -> error (what ++ ": " ++ errorBundlePretty e)
  Right a -> k a

runArith :: Str s => s -> Int
runArith = run exprP evalExp "runArith"

runCsv :: Str s => s -> Int
runCsv = run csvP (sum . map sum) "runCsv"

runIdents :: Str s => s -> Int
runIdents = run identsP (sum . map length) "runIdents"

runJson :: Str s => s -> Int
runJson = run jsonP sizeJ "runJson"

runQuoted :: Str s => s -> Int
runQuoted = run quotedP (sum . map length) "runQuoted"

sizeJ :: JValue -> Int
sizeJ JNull     = 1
sizeJ (JBool _) = 1
sizeJ (JNum n)  = n
sizeJ (JStr t)  = length t
sizeJ (JArr xs) = 1 + sum (map sizeJ xs)
sizeJ (JObj ps) = 1 + sum [ length k + sizeJ v | (k, v) <- ps ]
