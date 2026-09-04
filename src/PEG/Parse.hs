{-# LANGUAGE BangPatterns        #-}
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE KindSignatures      #-}
{-# LANGUAGE MagicHash           #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeFamilies        #-}
{-# LANGUAGE TypeOperators       #-}
{-# LANGUAGE UnboxedSums         #-}
{-# LANGUAGE UnboxedTuples       #-}

-- | Running a 'Grammar' against an input stream.
--
-- The top-level entry points are 'parse' (uses 'defaultOpts') and 'parseWith'
-- (accepts custom 'Opts' for indentation-sensitive parsing).  Both return a
-- 'Result' that records the matched value, the consumed prefix, and the
-- remaining suffix.
--
-- The input can be any "PEG.Stream" instance: 'String', strict or lazy
-- 'Data.Text.Text', strict or lazy 'Data.ByteString.ByteString'.
--
-- == Compiling once, parsing many times
--
-- 'parseWith' is written so that @'parseWith' opts g@ is a /closure/ that has
-- already traversed the grammar: every non-terminal reference has been
-- resolved to a function, and no 'PExp' constructor is examined again while
-- input is being consumed.  Bind it once and reuse it:
--
-- @
-- myParser :: String -> Result String Exp
-- myParser = parse myGrammar     -- compiled once, at first use
-- @
--
-- Writing @'parse' myGrammar input@ inline inside a loop instead re-does the
-- traversal on every call.  Give the binding a /monomorphic/ signature: a
-- grammar left polymorphic in its stream is a function of a 'Stream'
-- dictionary rather than a constant, so nothing is shared between calls.
--
-- == Why the result of a step is an unboxed sum
--
-- A compiled step returns @(# (# #) | (# a, 'PState' s #) #)@ rather than
-- @'Maybe' (a, 'PState' s)@.  The two are isomorphic, but the unboxed sum
-- lives in registers: a step that succeeds no longer allocates a @Just@ /and/
-- a pair on top of the new state, and a step that fails allocates nothing at
-- all.  Because the intermediate results of 'Seq' and 'Map' never escape,
-- this makes those two constructors — the ones the quasi-quoter emits for
-- every single grammar item — allocation-free.
module PEG.Parse
  ( Result (..)
  , parse
  , parseWith
  , compileGrammar
  , Step
  , Res
  , Opts (..)
  , defaultOpts
  , PState (..)
  , nextCol
  ) where

import Data.Kind (Type)
import qualified Data.ByteString as B
import qualified Data.Text       as T

import PEG.CharSet (CharSet, memberCS)
import PEG.Grammar
import PEG.Indent
import PEG.Member
import PEG.Stream
import PEG.Syntax
import PEG.Type
import PEG.TyLevel (Lookup)

-- | The result of running a grammar.
--
-- @'OK' a consumed rest@ means the grammar matched, producing value @a@.
-- @consumed@ is the prefix of the input that was consumed; @rest@ is the
-- remaining input.
data Result s a
  = OK a s s
  | Fail
  deriving (Show, Eq)

-- | Internal parser state.
--
-- The column of the character at the head of 'stInput' is carried alongside
-- the input rather than being precomputed for the whole stream, so nothing
-- proportional to the input is ever allocated up front.
data PState s = PState
  { stInput :: !s        -- ^ Remaining input.
  , stCol   :: !Int      -- ^ Column of the head of 'stInput'.
  , stOff   :: !Int      -- ^ Characters consumed so far.
  , stCands :: !Interval -- ^ Current candidate column interval.
  , stAlign :: !Bool     -- ^ Whether the next token must be aligned.
  }

-- | What a compiled step returns: either failure (the left injection, which
-- carries nothing) or a value together with the state after it.
--
-- This is @'Maybe' (a, 'PState' s)@ with the two boxes removed.
type Res s a = (# (# #) | (# a, PState s #) #)

-- | A compiled parser: it still takes the ambient column relation, because a
-- rule body inherits the relation in force at its call site.
type Step s a = RelD -> PState s -> Res s a

-- | Column of the character following @c@, given a column of @c@ and a tab
-- width.
nextCol :: Int -> Int -> Char -> Int
nextCol _  _ '\n' = 0
nextCol tw c '\t'
  | tw > 1        = ((c `div` tw) + 1) * tw
  | otherwise     = c + 1
nextCol _  c _    = c + 1
{-# INLINE nextCol #-}

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
parse :: Stream s => Grammar s env ty a -> s -> Result s a
parse = parseWith defaultOpts
{-# INLINABLE parse #-}
{-# SPECIALIZE parse :: Grammar String env ty a -> String -> Result String a #-}
{-# SPECIALIZE parse :: Grammar T.Text env ty a -> T.Text -> Result T.Text a #-}
{-# SPECIALIZE parse
      :: Grammar B.ByteString env ty a -> B.ByteString -> Result B.ByteString a #-}

-- | Run a grammar with custom 'Opts'.
--
-- Partially applying this to the options and the grammar yields a compiled
-- parser; see the note at the top of this module.
parseWith :: forall s env ty a.
             Stream s => Opts -> Grammar s env ty a -> s -> Result s a
parseWith opts g = run
  where
    step = compileGrammar (optTabWidth opts) g
    tau0 = optTokenMode opts

    run input = case step tau0 (PState input 0 0 (optCands opts) False) of
      (# (# #) | #)       -> Fail
      (# | (# a, st #) #) -> OK a (takeS (stOff st) input) (stInput st)
{-# INLINABLE parseWith #-}
{-# SPECIALIZE parseWith
      :: Opts -> Grammar String env ty a -> String -> Result String a #-}
{-# SPECIALIZE parseWith
      :: Opts -> Grammar T.Text env ty a -> T.Text -> Result T.Text a #-}
{-# SPECIALIZE parseWith
      :: Opts -> Grammar B.ByteString env ty a
      -> B.ByteString -> Result B.ByteString a #-}

--------------------------------------------------------------------------------
-- Compilation
--------------------------------------------------------------------------------

-- | A rule table in which every body has already been compiled to a 'Step'.
-- Built with a knot so that mutually recursive rules resolve to each other's
-- closures.
data CRules (s :: Type) (env :: Env) (defs :: Env) where
  CNil  :: CRules s env '[]
  CCons :: Step s a
        -> CRules s env rest
        -> CRules s env ('(n, 'EnvEntry ty a) ': rest)

clookup :: Member n defs ty a -> CRules s env defs -> Step s a
clookup Here      (CCons f _)    = f
clookup (There m) (CCons _ rest) = clookup m rest

-- | Traverse the grammar once and return a closure that consumes input.
--
-- The traversal resolves every non-terminal reference to the corresponding
-- compiled rule, so at parse time a non-terminal costs one indirect call
-- instead of a walk down the rule list.
compileGrammar :: forall s env ty a.
                  Stream s => Int -> Grammar s env ty a -> Step s a
compileGrammar tw (Grammar rules start) = compileE tw table start
  where
    table :: CRules s env env
    table = build rules

    build :: forall defs. Rules s env defs -> CRules s env defs
    build RNil                = CNil
    build (RCons _ body rest) = CCons (compileE tw table body) (build rest)
{-# INLINABLE compileGrammar #-}
{-# INLINABLE compileE #-}
-- Without these the whole parse runs through a 'Stream' dictionary, and the
-- per-character path stops being allocation-free.  Callers using another
-- stream should mark their own monomorphic parser bindings INLINABLE.
{-# SPECIALIZE compileGrammar
      :: Int -> Grammar String env ty a -> Step String a #-}
{-# SPECIALIZE compileGrammar
      :: Int -> Grammar T.Text env ty a -> Step T.Text a #-}
{-# SPECIALIZE compileGrammar
      :: Int -> Grammar B.ByteString env ty a -> Step B.ByteString a #-}

-- | Does this class avoid the two characters whose column advance is not
-- simply @+1@?  When it does, the column after a matched run is the column
-- before it plus the run's length, and no fold is needed.
simpleCS :: CharSet -> Bool
simpleCS cs = not (memberCS '\n' cs) && not (memberCS '\t' cs)

compileE :: forall s env ty a.
            Stream s => Int -> CRules s env env -> PExp s env ty a -> Step s a
compileE tw table = comp
  where
    -- Select the stream operations once per compiled grammar.  Leaving them
    -- as class-method applications would repeat the dictionary lookup on
    -- every character.
    !uncons  = unconsS       :: s -> (# (# #) | (# Char, s #) #)
    !spanS'  = spanS         :: (Char -> Bool) -> s -> (s, s)
    !lenS'   = lengthS       :: s -> Int
    !foldS'  = foldlS'       :: (Int -> Char -> Int) -> Int -> s -> Int
    !toStr   = chunkToString :: s -> String
    !packS   = packString    :: String -> s
    !emptyS  = packS []

    comp :: forall t b. PExp s env t b -> Step s b

    comp (Pure x) = \_ st -> (# | (# x, st #) #)

    comp (Term c) = satStep (c ==)

    comp (Sat cs) = satStep (\c -> memberCS c cs)

    comp AnyChar  = satStep (const True)

    comp (Str lit) = litStep lit

    -- A run of a character class, returned as a chunk of the stream.  On
    -- 'Data.Text.Text' this is a slice: no copy, no cons cells.
    comp (Span  cs) = spanChunk (\c -> memberCS c cs) (simpleCS cs) False
    comp (Span1 cs) = spanChunk (\c -> memberCS c cs) (simpleCS cs) True

    comp (NT (_ :: Name n)) =
      clookup (member :: Member n env (TyOf (Lookup n env))
                                      (ResOf (Lookup n env)))
              table

    -- Neither this nor 'Map' below allocates: the intermediate results travel
    -- in registers, so a quasi-quoted rule of @n@ items costs @n@ calls and
    -- nothing else.
    comp (Seq ef ex) =
      let pf = comp ef
          px = comp ex
      in \tau st -> case pf tau st of
           (# (# #) | #)       -> (# (# #) | #)
           (# | (# f, s1 #) #) -> case px tau s1 of
             (# (# #) | #)       -> (# (# #) | #)
             (# | (# x, s2 #) #) -> (# | (# f x, s2 #) #)

    comp (Choice e1 e2) =
      let p = comp e1
          q = comp e2
      in \tau st -> case p tau st of
           (# (# #) | #) -> q tau st
           r             -> r

    -- A hand-written @'Star' ('Sat' cs)@ still produces a @['Char']@ rather
    -- than a chunk, so it needs its own scanner.  The quasi-quoter emits
    -- 'Span' instead, but 'PExp' values built by hand can be either.
    comp (Star (Sat cs)) = spanList (\c -> memberCS c cs) (simpleCS cs)
    comp (Star (Term c)) = spanList (c ==) (c /= '\n' && c /= '\t')
    comp (Star AnyChar)  = spanList (const True) False

    comp (Star e) =
      let p = comp e
          go acc tau st = case p tau st of
            (# (# #) | #)        -> (# | (# reverse acc, st #) #)
            (# | (# x, st' #) #) -> go (x : acc) tau st'
      in go []

    -- A negative lookahead at a single character only needs to peek.
    comp (Not (Sat cs))   = notCharStep (\c -> memberCS c cs)
    comp (Not (Term c))   = notCharStep (c ==)
    comp (Not AnyChar)    = notCharStep (const True)
    -- @!e+@ succeeds exactly when the next character is not in the class, so
    -- it is the same peek.  Without this case the generic 'Not' below would
    -- run the whole scan to answer a one-character question.
    comp (Not (Span1 cs)) = notCharStep (\c -> memberCS c cs)
    -- @!e*@ can never succeed: the star always matches, if only the empty
    -- run.  Say so directly rather than scanning the input to find out.
    comp (Not (Span _))   = \_ _ -> (# (# #) | #)

    comp (Not e) =
      let p = comp e
      in \tau st -> case p tau st of
           (# (# #) | #) -> (# | (# (), st #) #)
           _             -> (# (# #) | #)

    comp (Map f e) =
      let p = comp e
      in \tau st -> case p tau st of
           (# (# #) | #)       -> (# (# #) | #)
           (# | (# x, s1 #) #) -> (# | (# f x, s1 #) #)

    comp (Indent rho e) =
      let p  = comp e
          !rd = relD rho
      in \tau st ->
           case p tau st { stCands = preimage rd (stCands st) } of
             (# (# #) | #)       -> (# (# #) | #)
             (# | (# x, s1 #) #) ->
               (# | (# x
                     , s1 { stCands = interI (stCands st)
                                             (image rd (stCands s1)) } #) #)

    comp (Position sigma e) =
      let p  = comp e
          !rd = relD sigma
      in \_ st -> p rd st

    comp (Align e) =
      let p = comp e
      in \tau st -> case p tau st { stAlign = True } of
           (# (# #) | #)       -> (# (# #) | #)
           (# | (# x, s1 #) #) ->
             (# | (# x, s1 { stAlign = stAlign st && stAlign s1 } #) #)

    ------------------------------------------------------------------------
    -- Terminals.  These live here rather than at the top level so that they
    -- close over the hoisted stream operations above.
    ------------------------------------------------------------------------

    -- | Match one character satisfying a predicate.  The predicate is tested
    -- /before/ any column bookkeeping, so a failing alternative costs one
    -- comparison and nothing else.
    satStep :: (Char -> Bool) -> Step s Char
    satStep p = \tau st -> case uncons (stInput st) of
      (# | (# x, xs #) #) | p x -> advance tw tau st x xs
      _                         -> (# (# #) | #)

    -- | Match a literal string.  On the fast path the whole literal is
    -- matched with a single loop and a single new 'PState'; otherwise it goes
    -- character by character so that column bookkeeping stays exactly as it
    -- would be for the equivalent chain of 'Term's.
    --
    -- The result is the literal itself, so no chunk is built.
    litStep :: String -> Step s String
    litStep lit = \tau st ->
      if plainly tau st
        then fast (stInput st) lit (stCol st) (stOff st) (stCands st)
        else slow lit tau st
      where
        fast rest [] !col !off cands =
          (# | (# lit, PState rest col off cands False #) #)
        fast rest (c : cs) !col !off cands = case uncons rest of
          (# | (# x, xs #) #)
            | x == c -> fast xs cs (nextCol tw col x) (off + 1) cands
          _          -> (# (# #) | #)

        slow []       _   st = (# | (# lit, st #) #)
        slow (c : cs) tau st = case uncons (stInput st) of
          (# | (# x, xs #) #)
            | x == c -> case advance tw tau st x xs of
                          (# (# #) | #)        -> (# (# #) | #)
                          (# | (# _, st' #) #) -> slow cs tau st'
          _          -> (# (# #) | #)

    -- | A run of a character class, returned as a chunk.
    --
    -- On the fast path this is one native @span@ — a slice for 'Text' and
    -- 'ByteString' — plus, when the class can contain a newline or a tab, one
    -- fold to find the resulting column.
    spanChunk :: (Char -> Bool) -> Bool -> Bool -> Step s s
    spanChunk p simple atLeastOne = go
      where
        go tau st
          | plainly tau st = case uncons (stInput st) of
              -- Peek before spanning.  A class that cannot match the very
              -- next character is the common case in an ordered choice, and
              -- calling 'spanS' just to be handed an empty prefix would
              -- allocate a pair on every failed alternative.
              (# | (# c, _ #) #) | p c -> chunk tau st
              _ | atLeastOne -> (# (# #) | #)
                | otherwise  -> (# | (# emptyS, st #) #)
          | otherwise = loop [] tau st

        chunk _ st = case spanS' p (stInput st) of
          (pre, rest) ->
            let !n    = lenS' pre
                !col' = if simple then stCol st + n
                                  else foldS' (nextCol tw) (stCol st) pre
            in (# | (# pre
                     , PState rest col' (stOff st + n)
                              (stCands st) False #) #)

        -- The layout-sensitive path: every character has to go through the
        -- interval arithmetic, so the chunk is rebuilt from the characters.
        loop acc tau st = case satStep p tau st of
          (# | (# x, st' #) #) -> loop (x : acc) tau st'
          (# (# #) | #)
            | atLeastOne && null acc -> (# (# #) | #)
            | otherwise -> (# | (# packS (reverse acc), st #) #)

    -- | A run of a character class, returned as a @['Char']@.  Only reachable
    -- from a hand-written @'Star' ('Sat' _)@; the quasi-quoter emits 'Span'.
    spanList :: (Char -> Bool) -> Bool -> Step s String
    spanList p simple = go
      where
        go tau st
          | plainly tau st = case uncons (stInput st) of
              (# | (# c, _ #) #) | p c -> case spanS' p (stInput st) of
                (pre, rest) ->
                  let !n    = lenS' pre
                      !col' = if simple then stCol st + n
                                        else foldS' (nextCol tw) (stCol st) pre
                  in (# | (# toStr pre
                           , PState rest col' (stOff st + n)
                                    (stCands st) False #) #)
              _ -> (# | (# [], st #) #)
          | otherwise = loop [] tau st

        loop acc tau st = case satStep p tau st of
          (# | (# x, st' #) #) -> loop (x : acc) tau st'
          (# (# #) | #)        -> (# | (# reverse acc, st #) #)

    -- | Negative lookahead at a single character: a peek, with no state built.
    notCharStep :: (Char -> Bool) -> Step s ()
    notCharStep p = go
      where
        go tau st
          | plainly tau st = case uncons (stInput st) of
              (# | (# x, _ #) #) | p x -> (# (# #) | #)
              _                        -> (# | (# (), st #) #)
          | otherwise = case satStep p tau st of
              (# (# #) | #) -> (# | (# (), st #) #)
              _             -> (# (# #) | #)

--------------------------------------------------------------------------------
-- Column bookkeeping
--------------------------------------------------------------------------------

-- | Consume the head character, updating column, offset and the candidate
-- interval.
--
-- When the ambient relation is total ('rdTotal', i.e. 'anyR') and no
-- alignment is pending, the candidate interval is provably unchanged, so the
-- whole interval computation is skipped.  Grammars that do not use layout
-- take this branch for every single character.
advance :: Int -> RelD -> PState s -> Char -> s -> Res s Char
advance tw tau (PState _ col off cands aligned) x xs
  | aligned =
      if memberI col cands
        then (# | (# x, PState xs col' off' (singletonI col) False #) #)
        else (# (# #) | #)
  | rdTotal tau =
      if nullI cands
        then (# (# #) | #)
        else (# | (# x, PState xs col' off' cands False #) #)
  | memberI col (preimage tau cands) =
      (# | (# x, PState xs col' off'
                        (interI cands (image tau (singletonI col))) False #) #)
  | otherwise = (# (# #) | #)
  where
    !col' = nextCol tw col x
    !off' = off + 1
{-# INLINE advance #-}

-- | Does the cheap path apply?  It does when the ambient relation constrains
-- nothing, no alignment is pending, and the candidate interval is inhabited:
-- under those conditions 'advance' provably leaves the interval alone, so a
-- run of characters can be consumed without touching it once.
plainly :: RelD -> PState s -> Bool
plainly tau st = rdTotal tau && not (stAlign st) && not (nullI (stCands st))
{-# INLINE plainly #-}
