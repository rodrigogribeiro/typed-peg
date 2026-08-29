{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeFamilies        #-}
{-# LANGUAGE TypeOperators       #-}

-- | Running a 'Grammar' against a 'String'.
--
-- The top-level entry points are 'parse' (uses 'defaultOpts') and 'parseWith'
-- (accepts custom 'Opts' for indentation-sensitive parsing).  Both return a
-- 'Result' that records the matched value, the consumed prefix, and the
-- remaining suffix.
module PEG.Parse
  ( Result (..)
  , parse
  , parseWith
  , eval
  , Opts (..)
  , defaultOpts
  , Input
  , PState (..)
  , columns
  ) where

import PEG.Grammar
import PEG.Indent
import PEG.Member
import PEG.Syntax
import PEG.Type
import PEG.TyLevel (Lookup)

-- | The result of running a grammar.
--
-- @'OK' a consumed rest@ means the grammar matched, producing value @a@.
-- @consumed@ is the prefix of the input that was consumed; @rest@ is the
-- remaining input.
data Result a
  = OK a String String
  | Fail
  deriving (Show, Eq)

-- | A string annotated with column positions, as produced by 'columns'.
type Input = [(Char, Int)]

-- | Internal parser state.
data PState = PState
  { stInput :: Input     -- ^ Remaining input with column positions.
  , stCands :: !Interval -- ^ Current candidate column interval.
  , stAlign :: !Bool     -- ^ Whether the next token must be aligned.
  }

-- | Annotate every character in a string with its column position.
-- Tab stops are expanded according to @tabWidth@.
columns :: Int -> String -> Input
columns tabWidth = go 0
  where
    go _ []     = []
    go c (x:xs) = (x, c) : go (next c x) xs

    next _ '\n' = 0
    next c '\t'
      | tabWidth > 1 = ((c `div` tabWidth) + 1) * tabWidth
      | otherwise    = c + 1
    next c _    = c + 1

-- | Parser configuration.
data Opts = Opts
  { optTokenMode :: RelD     -- ^ Default column relation between tokens.
  , optCands     :: Interval -- ^ Initial candidate column interval.
  , optTabWidth  :: Int      -- ^ Number of columns per tab stop.
  }

-- | Default options: accept tokens at any column, tab width of 8.
defaultOpts :: Opts
defaultOpts = Opts
  { optTokenMode = relD anyR
  , optCands     = fullI
  , optTabWidth  = 8
  }

-- | Run a grammar with 'defaultOpts'.
parse :: Grammar env ty a -> String -> Result a
parse = parseWith defaultOpts

-- | Run a grammar with custom 'Opts'.
parseWith :: Opts -> Grammar env ty a -> String -> Result a
parseWith opts (Grammar rules start) input =
  case eval rules start (optTokenMode opts) st0 of
    Nothing      -> Fail
    Just (a, st) ->
      let n = length input - length (stInput st)
      in OK a (take n input) (drop n input)
  where
    st0 = PState
      { stInput = columns (optTabWidth opts) input
      , stCands = optCands opts
      , stAlign = False
      }

-- | Low-level evaluator: run a 'PExp' against a 'PState' under a given column
-- relation.  Exposed for advanced use; most callers should use 'parse' or
-- 'parseWith'.
eval :: forall env ty a
      . Rules env env
     -> PExp env ty a
     -> RelD
     -> PState
     -> Maybe (a, PState)
eval rules = go
  where
    go :: forall t b. PExp env t b -> RelD -> PState -> Maybe (b, PState)
    go (Pure x) _ st = Just (x, st)

    go (Term c) tau st = do
      (x, st') <- terminal tau st
      if x == c then Just (c, st') else Nothing

    go AnyChar tau st = terminal tau st

    go (NT (_ :: Name s)) tau st =
      go (ruleFor (member :: Member s env (TyOf (Lookup s env))
                                          (ResOf (Lookup s env)))
                  rules)
         tau st

    go (Seq ef ex) tau st = do
      (f, st')  <- go ef tau st
      (x, st'') <- go ex tau st'
      pure (f x, st'')

    go (Choice e1 e2) tau st = case go e1 tau st of
      Just r  -> Just r
      Nothing -> go e2 tau st

    go (Star e) tau st = Just (starLoop (go e tau) st)

    go (Not e) tau st = case go e tau st of
      Just _  -> Nothing
      Nothing -> Just ((), st)

    go (Map f e) tau st = do
      (x, st') <- go e tau st
      pure (f x, st')

    go (Indent rho e) tau st = do
      (x, st') <- go e tau st { stCands = preimage rd (stCands st) }
      pure ( x
           , st' { stCands = interI (stCands st) (image rd (stCands st')) } )
      where
        rd = relD rho

    go (Position sigma e) _ st = go e (relD sigma) st

    go (Align e) tau st = do
      (x, st') <- go e tau st { stAlign = True }
      pure (x, st' { stAlign = stAlign st && stAlign st' })

terminal :: RelD -> PState -> Maybe (Char, PState)
terminal tau (PState input cands aligned) = case input of
  []            -> Nothing
  ((x, i) : xs)
    | aligned   ->
        if memberI i cands
          then Just (x, PState xs (singletonI i) False)
          else Nothing
    | otherwise ->
        if memberI i (preimage tau cands)
          then Just (x, PState xs (interI cands (image tau (singletonI i))) False)
          else Nothing

starLoop :: (PState -> Maybe (a, PState)) -> PState -> ([a], PState)
starLoop step = loop
  where
    loop st = case step st of
      Nothing       -> ([], st)
      Just (x, st') -> let (xs, rest) = loop st' in (x : xs, rest)

ruleFor :: Member s defs ty a -> Rules env defs -> PExp env ty a
ruleFor Here      (RCons _ body _)    = body
ruleFor (There m) (RCons _ _    rest) = ruleFor m rest
