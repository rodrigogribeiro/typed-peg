{-# LANGUAGE FlexibleInstances, DeriveFunctor, TypeFamilies #-}
-- | A simple, continuation-based semantics for PEG expressions.
--
-- 'PExp' in this module is an alternative representation of PEG expressions
-- as explicit functions over an input type @d@, making the semantics of each
-- combinator concrete and inspectable.  Useful for testing and for
-- understanding the library\'s evaluation model.
module PEG.Semantics.Simple where

import Control.Applicative
import Control.Monad (MonadPlus(..), guard)
import Data.Char (isDigit, ord, isSpace)
import Prelude hiding (not)

newtype PExp d a
  = PExp {
      runPExp :: d -> Result d a
    } deriving Functor

data Result d a
  = Pure a             -- didn't consume anything, can backtrack
  | Commit d a         -- consumed input
  | Fail String Bool   -- failed, flagged if consumed
  deriving Functor

instance Applicative (PExp d) where
  pure a = PExp $ \ _ -> Pure a
  PExp mf <*> PExp ma
    = PExp $ \ d ->
      case mf d of
        Pure f      -> fmap f (ma d)
        Fail s c    -> Fail s c
        Commit d' f ->
          case ma d' of
            Pure a       -> Commit d' (f a)
            Fail s _     -> Fail s True
            Commit d'' a -> Commit d'' (f a)

instance Alternative (PExp d) where
  PExp ma <|> PExp mb
    = PExp $ \ d ->
      case ma d of
        Fail _ False -> mb d
        x            -> x
  empty = PExp $ \ _ -> Fail "empty" False


instance Monad (PExp d) where
  PExp m >>= k = PExp $ \d ->
    case m d of
      Pure a -> runPExp (k a) d
      Commit d' a ->
        case runPExp (k a) d' of
          Pure b -> Commit d' b
          Fail s _ -> Fail s True
          commit -> commit
      Fail s c -> Fail s c

instance MonadPlus (PExp d) where
  mplus = (<|>)
  mzero = empty

try :: PExp d a -> PExp d a
try (PExp m)
  = PExp $ \d ->
      case m d of
        Fail s _ -> Fail s False
        x        -> x

infixl 3 </>

(</>) :: PExp d a -> PExp d a -> PExp d a
p </> q = try p <|> q


-- | Unrelated to "PEG.Stream": this is the reference semantics' own
-- token-polymorphic input class, used only inside this module.
class SimpleStream d where
  type Elem d
  anyChar :: PExp d (Elem d)

instance SimpleStream [a] where
  type Elem [a] = a 
  anyChar = PExp $ \s -> case s of
    (x:xs) -> Commit xs x
    [] -> Fail "EOF" False

satisfy :: SimpleStream d => (Elem d -> Bool) -> PExp d (Elem d)
satisfy p = try $ do
  x <- anyChar
  x <$ guard (p x)

whiteSpace :: PExp String ()
whiteSpace = () <$ many (satisfy isSpace)

phrase :: PExp String a -> PExp String a
phrase m = whiteSpace *> m <* eof

not :: PExp d a -> PExp d ()
not (PExp m)
  = PExp $ \d ->
      case m d of
        Fail{} -> Pure ()
        _      -> Fail "unexpected" False

eof :: SimpleStream d => PExp d ()
eof = not anyChar

char :: Eq (Elem d) => SimpleStream d => Elem d -> PExp d (Elem d)
char c = satisfy (c ==)

lexeme :: PExp String a -> PExp String a
lexeme m = m <* whiteSpace

symbol :: Char -> PExp String Char
symbol c = lexeme (char c)

digit :: PExp String Int
digit
  = f <$> satisfy isDigit
    where
      f c = ord c - ord '0'
