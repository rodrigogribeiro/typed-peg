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
-- remaining suffix — or, when the grammar does not match, a 'ParseError'
-- saying where in the input the parse got furthest before it failed.
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
-- A compiled step returns @(# Int | (# a, 'PState' s, Int #) #)@ rather than
-- @'Either' 'Int' (a, 'PState' s, 'Int')@.  The two are isomorphic, but the
-- unboxed sum lives in registers: a step that succeeds no longer allocates a
-- constructor /and/ a tuple on top of the new state, and a step that fails
-- allocates nothing at all.  Because the intermediate results of 'Seq' and
-- 'Map' never escape, this makes those two constructors — the ones the
-- quasi-quoter emits for every single grammar item — allocation-free.
--
-- == Where a failed parse is reported
--
-- At the /furthest/ offset at which any step failed, over the whole parse.
-- The offset at which the start expression finally failed would be of little
-- use: an ordered choice backtracks to where its alternative began before
-- trying the next one, so that offset is nearly always the start of some
-- rule, well before whatever was actually wrong.
--
-- The furthest offset has to survive successes as well as failures — in
-- @(a \/ b) c@, @a@ may fail at offset 10, @b@ succeed up to offset 2 and @c@
-- fail at offset 3, and the answer is 10 — so every step takes the furthest
-- offset so far as an argument and returns it, updated, on both branches.
--
-- It is a boxed 'Int', and that is deliberate.  A compiled step is called as
-- an unknown function, and GHC's generic application code has a fast path
-- only for argument lists that are all pointers: a step taking an 'Int#'
-- between two pointers was applied piecemeal, building a partial
-- application on every call, which more than doubled the allocation of
-- some grammars.  A boxed 'Int' is a pointer like the other arguments, and
-- is passed along unchanged — no new box — unless the furthest failure
-- moves forward; see 'noteAt'.
--
-- What counts as a failure:
--
-- * A character test that does not match — 'Term', 'Sat', 'AnyChar', the
--   first character of 'Span1' — fails at the offset of that character.  So
--   does a character the indentation constraints reject.
-- * A string literal fails at the offset where it /starts/, wherever in it the
--   mismatch is: it is one token, and \"expected @while@\" is about the
--   token.
-- * A repetition ends at a failure, and that failure counts: in
--   @(a b)*@ an iteration that matched @a@ and then failed in @b@ is the
--   furthest point reached, even though the repetition itself succeeds.  A
--   'Span' or 'Span1' is a repetition of a character test, and counts the
--   character it stops at in the same way.
-- * Nothing inside a lookahead counts.  @!e@ succeeding means @e@ failed,
--   which is not an error; when @!e@ itself fails, it fails at the offset
--   where it was tried.  That is what makes a @!.@ at the end of a start
--   expression report the start of the trailing input.
--
-- Only the offset is tracked while parsing.  'parseWith' turns it into a line
-- and a column once, after the parse has failed, with one pass over the
-- consumed prefix of the input ("PEG.Location"); a parse that succeeds never
-- pays for it.
module PEG.Parse
  ( Result (..)
  , ParseError (..)
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
import GHC.Exts  (Int (I#), isTrue#, (>#))

import PEG.CharSet (CharSet, memberCS)
import PEG.Grammar
import PEG.Indent
import PEG.Key
import PEG.Location (offsetToLineCol)
import PEG.Member
import PEG.Stream
import PEG.Syntax
import PEG.Type (Env, EnvEntry (..))

-- | The result of running a grammar.
--
-- @'OK' a consumed rest@ means the grammar matched, producing value @a@.
-- @consumed@ is the prefix of the input that was consumed; @rest@ is the
-- remaining input.  @'Fail' e@ means it did not, and @e@ says where.
--
-- A grammar that matches a prefix of the input succeeds: end the start
-- expression with @!.@ to demand all of it, and trailing input that does not
-- parse is then reported as a 'Fail' at the furthest point reached.
data Result s a
  = OK a s s
  | Fail !ParseError
  deriving (Show, Eq)

-- | Where a parse failed: the furthest point in the input at which any part
-- of the grammar failed to match.  See the note at the top of this module for
-- exactly what that is.
--
-- The line and column are those of "PEG.Location", both counted from 1, with
-- a tab advancing the column by one.  On a 'Data.ByteString.ByteString' the
-- offset and the column count bytes.
data ParseError = ParseError
  { errLine   :: !Int  -- ^ Line, from 1.
  , errColumn :: !Int  -- ^ Column, from 1.
  , errOffset :: !Int  -- ^ Characters of the input before the failure.
  } deriving (Show, Eq)

-- | The 'ParseError' at an offset of an input.
parseErrorAt :: Stream s => s -> Int -> ParseError
parseErrorAt input off = ParseError ln col off
  where (ln, col) = offsetToLineCol input off

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

-- | What a compiled step returns: either failure, with the furthest offset
-- at which anything has failed so far, or a value together with the state
-- after it and that same furthest offset.
--
-- This is @'Either' 'Int' (a, 'PState' s, 'Int')@ with the boxes removed.
type Res s a = (# Int | (# a, PState s, Int #) #)

-- | A compiled parser.  It takes the ambient column relation, because a rule
-- body inherits the relation in force at its call site, and the furthest
-- failure offset so far, which it returns updated.
type Step s a = RelD -> Int -> PState s -> Res s a

-- | Record a failure at an offset: the furthest of it and the furthest so far.
--
-- When the offset is no further, the box passed in is returned as it is, so
-- a new 'Int' is allocated only when the furthest failure moves forward —
-- at most once per character of input, and in practice far less often.
noteAt :: Int -> Int -> Int
noteAt far@(I# f) (I# o)
  | isTrue# (o ># f) = I# o
  | otherwise        = far
{-# INLINE noteAt #-}

-- | Fail at an offset.
--
-- The furthest offset is forced before it goes into the result.  A field of
-- an unboxed sum is lazy, and left alone this would build a thunk on every
-- failure — the one thing a failing step must not do.
failOff :: Int -> Int -> Res s a
failOff far off = case noteAt far off of !f -> (# f | #)
{-# INLINE failOff #-}

-- | Fail at the current position.
failAt :: Int -> PState s -> Res s a
failAt far st = failOff far (stOff st)
{-# INLINE failAt #-}

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
parse :: Stream s => Grammar s nt a -> s -> Result s a
parse = parseWith defaultOpts
{-# INLINABLE parse #-}
{-# SPECIALIZE parse :: Grammar String nt a -> String -> Result String a #-}
{-# SPECIALIZE parse :: Grammar T.Text nt a -> T.Text -> Result T.Text a #-}
{-# SPECIALIZE parse
      :: Grammar B.ByteString nt a -> B.ByteString -> Result B.ByteString a #-}

-- | Run a grammar with custom 'Opts'.
--
-- Partially applying this to the options and the grammar yields a compiled
-- parser; see the note at the top of this module.
parseWith :: forall s nt a.
             Stream s => Opts -> Grammar s nt a -> s -> Result s a
parseWith opts g = run
  where
    step = compileGrammar (optTabWidth opts) g
    tau0 = optTokenMode opts

    run input = case step tau0 0 (PState input 0 0 (optCands opts) False) of
      (# far | #)            -> Fail (parseErrorAt input far)
      (# | (# a, st, _ #) #) -> OK a (takeS (stOff st) input) (stInput st)
{-# INLINABLE parseWith #-}
{-# SPECIALIZE parseWith
      :: Opts -> Grammar String nt a -> String -> Result String a #-}
{-# SPECIALIZE parseWith
      :: Opts -> Grammar T.Text nt a -> T.Text -> Result T.Text a #-}
{-# SPECIALIZE parseWith
      :: Opts -> Grammar B.ByteString nt a
      -> B.ByteString -> Result B.ByteString a #-}

--------------------------------------------------------------------------------
-- Compilation
--------------------------------------------------------------------------------

-- | A rule table in which every body has already been compiled to a 'Step'.
-- Built with a knot so that mutually recursive rules resolve to each other's
-- closures.
data CRules (s :: Type) (defs :: Env) where
  CNil  :: CRules s '[]
  CCons :: Step s a
        -> CRules s rest
        -> CRules s ('(n, 'EnvEntry a) ': rest)

clookup :: Member n defs a -> CRules s defs -> Step s a
clookup Here      (CCons f _)    = f
clookup (There m) (CCons _ rest) = clookup m rest

-- | A compiled rule, wrapped so that 'Step' can be the image of a 'Table'.
newtype CStep s a = CStep { unCStep :: Step s a }

-- | Traverse the grammar once and return a closure that consumes input.
--
-- The traversal resolves every non-terminal reference to the corresponding
-- compiled rule, so at parse time a non-terminal costs one indirect call
-- instead of a walk down the rule list.
compileGrammar :: forall s nt a.
                  Stream s => Int -> Grammar s nt a -> Step s a
compileGrammar tw (Grammar rules start) = compileListed tw rules start
compileGrammar tw (Keyed rules start)   = compileKeyed tw tabulate rules start

-- | A grammar over a type-level environment: the rules are compiled into a
-- list, and a reference is resolved by following its membership proof down
-- that list, once, while the grammar is being compiled.
compileListed :: forall s env a. Stream s
              => Int -> Rules s env env -> PExp s (InEnv env) a -> Step s a
compileListed tw rules start = compileE tw resolve start
  where
    table :: CRules s env
    table = build rules

    resolve :: forall b. InEnv env b -> Step s b
    resolve (InEnv w) = clookup w table

    build :: forall defs. Rules s env defs -> CRules s defs
    build RNil                = CNil
    build (RCons _ body rest) = CCons (compileE tw resolve body) (build rest)
{-# INLINABLE compileListed #-}

-- | A grammar over declared keys: the compiled rules are tabulated once, and
-- a reference is resolved by looking its key up in the table.
--
-- The knot is safe for the same reason as the list's: looking a key up yields
-- the (lazy) compiled rule without running it, so compiling a rule body never
-- forces the rules it refers to.
--
-- 'tabulate' is an argument rather than a 'Tabulate' constraint, and that is
-- a matter of performance, not of style.  GHC specialises a function only on
-- dictionaries it knows, and at the call in 'compileGrammar' the key type is
-- still a variable: with the constraint, the @SPECIALIZE@ pragmas below never
-- reached this function, and a grammar over keys ran the whole parse through
-- the 'Stream' dictionary — on MiniPython, 37% slower and 48% more allocation
-- per character than the same grammar over an environment.  With only
-- 'Stream' left to specialise on, the two compile to the same code.
compileKeyed :: forall s nt a. Stream s
             => Int
             -> (forall f. (forall b. nt b -> f b) -> Table nt f)
             -> (forall b. nt b -> PExp s nt b)
             -> PExp s nt a
             -> Step s a
compileKeyed tw tab rules start = compileE tw resolve start
  where
    table :: Table nt (CStep s)
    table = tab (\k -> CStep (compileE tw resolve (rules k)))

    resolve :: forall b. nt b -> Step s b
    resolve k = unCStep (lookupTable table k)
{-# INLINABLE compileKeyed #-}

{-# INLINABLE compileGrammar #-}
{-# INLINABLE compileE #-}
-- Without these the whole parse runs through a 'Stream' dictionary, and the
-- per-character path stops being allocation-free.  Callers using another
-- stream should mark their own monomorphic parser bindings INLINABLE.
{-# SPECIALIZE compileGrammar
      :: Int -> Grammar String nt a -> Step String a #-}
{-# SPECIALIZE compileGrammar
      :: Int -> Grammar T.Text nt a -> Step T.Text a #-}
{-# SPECIALIZE compileGrammar
      :: Int -> Grammar B.ByteString nt a -> Step B.ByteString a #-}

-- | Does this class avoid the two characters whose column advance is not
-- simply @+1@?  When it does, the column after a matched run is the column
-- before it plus the run's length, and no fold is needed.
simpleCS :: CharSet -> Bool
simpleCS cs = not (memberCS '\n' cs) && not (memberCS '\t' cs)

compileE :: forall s nt a. Stream s
         => Int -> (forall b. nt b -> Step s b) -> PExp s nt a -> Step s a
compileE tw resolve = comp
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

    comp :: forall b. PExp s nt b -> Step s b

    comp (Pure x) = \_ far st -> (# | (# x, st, far #) #)

    comp (Term c) = satStep (c ==)

    comp (Sat cs) = satStep (\c -> memberCS c cs)

    comp AnyChar  = satStep (const True)

    comp (Str lit) = litStep lit

    -- Consumes nothing: the offset is already in the state.
    comp GetOffset = \_ far st -> (# | (# stOff st, st, far #) #)

    -- A run of a character class, returned as a chunk of the stream.  On
    -- 'Data.Text.Text' this is a slice: no copy, no cons cells.
    comp (Span  cs) = spanChunk (\c -> memberCS c cs) (simpleCS cs) False
    comp (Span1 cs) = spanChunk (\c -> memberCS c cs) (simpleCS cs) True

    -- The key has already been resolved to its compiled rule by whoever
    -- built @resolve@; this is one lookup per occurrence, at compile time.
    comp (NT k) = resolve k

    -- Neither this nor 'Map' below allocates: the intermediate results travel
    -- in registers, so a quasi-quoted rule of @n@ items costs @n@ calls and
    -- nothing else.
    comp (Seq ef ex) =
      let pf = comp ef
          px = comp ex
      in \tau far st -> case pf tau far st of
           (# f | #)               -> (# f | #)
           (# | (# g, s1, f1 #) #) -> case px tau f1 s1 of
             (# f | #)               -> (# f | #)
             (# | (# x, s2, f2 #) #) -> (# | (# g x, s2, f2 #) #)

    -- The second alternative starts from where the first one got furthest.
    comp (Choice e1 e2) =
      let p = comp e1
          q = comp e2
      in \tau far st -> case p tau far st of
           (# f | #) -> q tau f st
           r         -> r

    -- A hand-written @'Star' ('Sat' cs)@ still produces a @['Char']@ rather
    -- than a chunk, so it needs its own scanner.  The quasi-quoter emits
    -- 'Span' instead, but 'PExp' values built by hand can be either.
    comp (Star (Sat cs)) = spanList (\c -> memberCS c cs) (simpleCS cs)
    comp (Star (Term c)) = spanList (c ==) (c /= '\n' && c /= '\t')
    comp (Star AnyChar)  = spanList (const True) False

    -- The failure that ends the repetition is kept: an iteration that got
    -- some way before failing may be the furthest the parse ever gets.
    comp (Star e) =
      let p = comp e
          go acc tau far st = case p tau far st of
            (# f | #)                -> (# | (# reverse acc, st, f #) #)
            (# | (# x, st', f #) #)  -> go (x : acc) tau f st'
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
    comp (Not (Span _))   = \_ far st -> failAt far st

    -- What fails inside a lookahead is not an error, so the furthest offset
    -- it reached is dropped either way.
    comp (Not e) =
      let p = comp e
      in \tau far st -> case p tau far st of
           (# _ | #) -> (# | (# (), st, far #) #)
           _         -> failAt far st

    comp (Map f e) =
      let p = comp e
      in \tau far st -> case p tau far st of
           (# r | #)               -> (# r | #)
           (# | (# x, s1, f1 #) #) -> (# | (# f x, s1, f1 #) #)

    comp (Indent rho e) =
      let p  = comp e
          !rd = relD rho
      in \tau far st ->
           case p tau far st { stCands = preimage rd (stCands st) } of
             (# f | #)               -> (# f | #)
             (# | (# x, s1, f1 #) #) ->
               (# | (# x
                     , s1 { stCands = interI (stCands st)
                                             (image rd (stCands s1)) }
                     , f1 #) #)

    comp (Position sigma e) =
      let p  = comp e
          !rd = relD sigma
      in \_ far st -> p rd far st

    comp (Align e) =
      let p = comp e
      in \tau far st -> case p tau far st { stAlign = True } of
           (# f | #)               -> (# f | #)
           (# | (# x, s1, f1 #) #) ->
             (# | (# x, s1 { stAlign = stAlign st && stAlign s1 }, f1 #) #)

    ------------------------------------------------------------------------
    -- Terminals.  These live here rather than at the top level so that they
    -- close over the hoisted stream operations above.
    ------------------------------------------------------------------------

    -- | Match one character satisfying a predicate.  The predicate is tested
    -- /before/ any column bookkeeping, so a failing alternative costs one
    -- comparison and nothing else.
    satStep :: (Char -> Bool) -> Step s Char
    satStep p = \tau far st -> case uncons (stInput st) of
      (# | (# x, xs #) #) | p x -> advance tw tau far st x xs
      _                         -> failAt far st
    -- Inlined so that each use sees its predicate.  Shared, it is a worker
    -- that calls the predicate as an unknown function, and allocates on every
    -- character for the privilege.
    {-# INLINE satStep #-}

    -- | Match a literal string.  On the fast path the whole literal is
    -- matched with a single loop and a single new 'PState'; otherwise it goes
    -- character by character so that column bookkeeping stays exactly as it
    -- would be for the equivalent chain of 'Term's.
    --
    -- The result is the literal itself, so no chunk is built.  A literal
    -- fails where it starts, wherever the mismatch is: it is one token.
    litStep :: String -> Step s String
    litStep lit = \tau far st0 ->
      let fast rest [] !col !off cands =
            (# | (# lit, PState rest col off cands False, far #) #)
          fast rest (c : cs) !col !off cands = case uncons rest of
            (# | (# x, xs #) #)
              | x == c -> fast xs cs (nextCol tw col x) (off + 1) cands
            _          -> failAt far st0

          slow []       st = (# | (# lit, st, far #) #)
          slow (c : cs) st = case uncons (stInput st) of
            (# | (# x, xs #) #)
              | x == c -> case advance tw tau far st x xs of
                            (# _ | #)               -> failAt far st0
                            (# | (# _, st', _ #) #) -> slow cs st'
            _          -> failAt far st0
      in if plainly tau st0
           then fast (stInput st0) lit (stCol st0) (stOff st0) (stCands st0)
           else slow lit st0

    -- | A run of a character class, returned as a chunk.
    --
    -- On the fast path this is one native @span@ — a slice for 'Text' and
    -- 'ByteString' — plus, when the class can contain a newline or a tab, one
    -- fold to find the resulting column.  The character the run stops at
    -- counts as a failure there, as it would for the equivalent 'Star'.
    spanChunk :: (Char -> Bool) -> Bool -> Bool -> Step s s
    spanChunk p simple atLeastOne = go
      where
        go tau far st
          | plainly tau st = case uncons (stInput st) of
              -- Peek before spanning.  A class that cannot match the very
              -- next character is the common case in an ordered choice, and
              -- calling 'spanS' just to be handed an empty prefix would
              -- allocate a pair on every failed alternative.
              (# | (# c, _ #) #) | p c -> chunk far st
              _ | atLeastOne -> failAt far st
                | otherwise  -> case noteAt far (stOff st) of
                    !f -> (# | (# emptyS, st, f #) #)
          | otherwise = loop [] tau far st

        chunk far st = case spanS' p (stInput st) of
          (pre, rest) ->
            let !n    = lenS' pre
                !col' = if simple then stCol st + n
                                  else foldS' (nextCol tw) (stCol st) pre
                !off' = stOff st + n
                !f    = noteAt far off'
            in (# | (# pre, PState rest col' off' (stCands st) False, f #) #)

        -- The layout-sensitive path: every character has to go through the
        -- interval arithmetic, so the chunk is rebuilt from the characters.
        loop acc tau far st = case satStep p tau far st of
          (# | (# x, st', f #) #) -> loop (x : acc) tau f st'
          (# f | #)
            | atLeastOne && null acc -> (# f | #)
            | otherwise -> (# | (# packS (reverse acc), st, f #) #)

    -- | A run of a character class, returned as a @['Char']@.  Only reachable
    -- from a hand-written @'Star' ('Sat' _)@; the quasi-quoter emits 'Span'.
    spanList :: (Char -> Bool) -> Bool -> Step s String
    spanList p simple = go
      where
        go tau far st
          | plainly tau st = case uncons (stInput st) of
              (# | (# c, _ #) #) | p c -> case spanS' p (stInput st) of
                (pre, rest) ->
                  let !n    = lenS' pre
                      !col' = if simple then stCol st + n
                                        else foldS' (nextCol tw) (stCol st) pre
                      !off' = stOff st + n
                      !f    = noteAt far off'
                  in (# | (# toStr pre
                           , PState rest col' off' (stCands st) False
                           , f #) #)
              _ -> case noteAt far (stOff st) of
                     !f -> (# | (# [], st, f #) #)
          | otherwise = loop [] tau far st

        loop acc tau far st = case satStep p tau far st of
          (# | (# x, st', f #) #) -> loop (x : acc) tau f st'
          (# f | #)               -> (# | (# reverse acc, st, f #) #)

    -- | Negative lookahead at a single character: a peek, with no state built.
    notCharStep :: (Char -> Bool) -> Step s ()
    notCharStep p = go
      where
        go tau far st
          | plainly tau st = case uncons (stInput st) of
              (# | (# x, _ #) #) | p x -> failAt far st
              _                        -> (# | (# (), st, far #) #)
          | otherwise = case satStep p tau far st of
              (# _ | #) -> (# | (# (), st, far #) #)
              _         -> failAt far st

--------------------------------------------------------------------------------
-- Column bookkeeping
--------------------------------------------------------------------------------

-- | Consume the head character, updating column, offset and the candidate
-- interval.  A character the indentation constraints reject fails at its own
-- offset, like one that does not match.
--
-- When the ambient relation is total ('rdTotal', i.e. 'anyR') and no
-- alignment is pending, the candidate interval is provably unchanged, so the
-- whole interval computation is skipped.  Grammars that do not use layout
-- take this branch for every single character.
advance :: Int -> RelD -> Int -> PState s -> Char -> s -> Res s Char
-- The state is taken apart rather than bound whole: failing needs only its
-- offset, and holding on to the whole state made GHC rebuild it, inside the
-- worker it unpacks it into, on every call.
advance tw tau far (PState _ col off cands aligned) x xs
  | aligned =
      if memberI col cands
        then (# | (# x, PState xs col' off' (singletonI col) False, far #) #)
        else failOff far off
  | rdTotal tau =
      if nullI cands
        then failOff far off
        else (# | (# x, PState xs col' off' cands False, far #) #)
  | memberI col (preimage tau cands) =
      (# | (# x, PState xs col' off'
                        (interI cands (image tau (singletonI col))) False
           , far #) #)
  | otherwise = failOff far off
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
