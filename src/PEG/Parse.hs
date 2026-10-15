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
-- saying where in the input the parse got furthest before it failed, what it
-- found there, and what it expected instead.
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
-- A compiled step returns @(# t | (# a, 'PState' s, t #) #)@ rather than
-- @'Either' t (a, 'PState' s, t)@, where @t@ is what tracks failures — an
-- 'Int' while parsing; see below.  The two are isomorphic, but the
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
--
-- == What was expected: a second pass, on failure only
--
-- A 'ParseError' also lists what the grammar was looking for at the error's
-- offset, @F@.  Collecting that while parsing would cost a list cell on every
-- failed alternative, on every parse.  Instead the grammar is compiled a
-- second time, with a different 'Tracker', and that copy is run only after a
-- parse has failed, from the start, to collect what fails exactly at @F@.  A
-- PEG is deterministic, so the second run retraces the first.  The second
-- copy is compiled the first time it is needed, and 'errExpected' is lazy:
-- a caller that never looks at it never runs it.
--
-- The two passes are the same compiler, 'compileE', over two trackers, so
-- they cannot disagree about the grammar; while parsing, the tracker is the
-- 'Int' above, and everything describing what was expected is dropped
-- unevaluated.
--
-- What is collected at @F@ ('Expected'):
--
-- * A character, a class, any character, or a string literal that fails
--   there, as itself.  A literal fails where it starts, so it is listed when
--   it starts at @F@.
-- * A class repeated by 'Span' or 'Span1' that stops at @F@: one more of it
--   would have been accepted.
-- * @!.@ failing there, as 'ExpEnd'.  No other lookahead contributes, and
--   nothing inside a lookahead does.
-- * A 'Label'led expression that /starts/ at @F@ and collects anything there
--   contributes its name instead.  One that starts before @F@ contributes
--   what it collected, which is more precise.  An expression labelled with
--   the empty name contributes nothing, wherever it starts — that is how
--   whitespace is kept out of the list.
module PEG.Parse
  ( Result (..)
  , ParseError (..)
  , Found (..)
  , Expected (..)
  , renderParseError
  , showFound
  , showExpected
  , parse
  , parseWith
  , compileGrammar
  , Tracker
  , Step
  , Res
  , Opts (..)
  , defaultOpts
  , PState (..)
  , nextCol
  ) where

import Data.Char (isAlphaNum)
import Data.Kind (Type)
import Data.List (intercalate)
import qualified Data.ByteString as B
import qualified Data.Set        as Set
import qualified Data.Text       as T
import GHC.Exts  (Int (I#), isTrue#, (>#))

import PEG.CharSet (CharSet, csRanges, describeCS, memberCS)
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
-- remaining input.  @'Fail' e@ means it did not, and @e@ says where and why.
--
-- A grammar that matches a prefix of the input succeeds: end the start
-- expression with @!.@ to demand all of it, and trailing input that does not
-- parse is then reported as a 'Fail' at the furthest point reached.
data Result s a
  = OK a s s
  | Fail !ParseError
  deriving (Show, Eq)

-- | Where a parse failed, what was there, and what the grammar expected
-- instead.  The position is the furthest point in the input at which any
-- part of the grammar failed to match; see the note at the top of this module
-- for exactly what that is, and for what is listed as expected.
--
-- The line and column are those of "PEG.Location", both counted from 1, with
-- a tab advancing the column by one.  On a 'Data.ByteString.ByteString' the
-- offset and the column count bytes.
--
-- 'errFound' and 'errExpected' are lazy: the second pass that computes
-- 'errExpected' runs only if it is looked at.
data ParseError = ParseError
  { errLine     :: !Int         -- ^ Line, from 1.
  , errColumn   :: !Int         -- ^ Column, from 1.
  , errOffset   :: !Int         -- ^ Characters of the input before the failure.
  , errFound    :: Found        -- ^ What the input has there.
  , errExpected :: [Expected]   -- ^ What would have been accepted there, in
                                --   the order the grammar tried it.
  } deriving (Show, Eq)

-- | What the input has at the position of an error.
data Found
  = FoundToken String  -- ^ A word — a run of letters, digits and @_@ — or
                       --   else a single character.
  | FoundEnd           -- ^ The end of the input.
  deriving (Show, Eq, Ord)

-- | Something the grammar would have accepted at the position of an error.
data Expected
  = ExpChar Char       -- ^ A character: @\'x\'@.
  | ExpString String   -- ^ A string literal: @\"while\"@.
  | ExpClass String    -- ^ A character class, written as in the grammar.
  | ExpAny             -- ^ Any character: @.@.
  | ExpEnd             -- ^ The end of the input: a @!.@ failed there.
  | ExpLabel String    -- ^ The name a 'Label' gave an expression.
  deriving (Show, Eq, Ord)

-- | How a 'Found' reads in a message.
showFound :: Found -> String
showFound FoundEnd         = "end of input"
showFound (FoundToken [c]) = show c
showFound (FoundToken w)   = show w

-- | How an 'Expected' reads in a message.
showExpected :: Expected -> String
showExpected e = case e of
  ExpChar c   -> show c
  ExpString w -> show w
  ExpClass d  -> d
  ExpAny      -> "any character"
  ExpEnd      -> "end of input"
  ExpLabel l  -> l

-- | A one-line message, in English:
--
-- @
-- 1:12: unexpected \';\', expecting \'*\', \'+\' or \')\'
-- @
--
-- Build your own from the fields for another language or format.
renderParseError :: ParseError -> String
renderParseError e =
  show (errLine e) ++ ":" ++ show (errColumn e) ++ ": unexpected "
    ++ showFound (errFound e)
    ++ case map showExpected (errExpected e) of
         [] -> ""
         xs -> ", expecting " ++ orList xs
  where
    orList [x] = x
    orList xs  = intercalate ", " (init xs) ++ " or " ++ last xs

-- | The 'ParseError' at an offset of an input, given what was expected there.
parseErrorAt :: Stream s => s -> Int -> [Expected] -> ParseError
parseErrorAt input off expected =
  ParseError ln col off (foundAt input off) expected
  where (ln, col) = offsetToLineCol input off

-- | What an input has at an offset.
foundAt :: Stream s => s -> Int -> Found
foundAt s0 off = case unconsS (dropChars off s0) of
  (# | (# c, rest #) #)
    | isWord c  -> FoundToken (c : word rest)
    | otherwise -> FoundToken [c]
  _             -> FoundEnd
  where
    isWord c = isAlphaNum c || c == '_'
    word s = case unconsS s of
      (# | (# c, rest #) #) | isWord c -> c : word rest
      _                                -> []
    dropChars n s
      | n <= 0    = s
      | otherwise = case unconsS s of
          (# | (# _, rest #) #) -> dropChars (n - 1) rest
          _                     -> s

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

-- | What a compiled step returns: either failure, with the failure tracker,
-- or a value together with the state after it and the tracker.
--
-- This is @'Either' t (a, 'PState' s, t)@ with the boxes removed.
type Res s t a = (# t | (# a, PState s, t #) #)

-- | A compiled parser.  It takes the ambient column relation, because a rule
-- body inherits the relation in force at its call site, and the failure
-- tracker, which it returns updated.
type Step s t a = RelD -> t -> PState s -> Res s t a

-- | What a compiled grammar records about its failures.
--
-- While parsing it is an 'Int', the furthest offset at which anything has
-- failed.  After a parse has failed, the grammar is run again over a tracker
-- that knows that offset and collects what was expected there.  The class is
-- exported only so that 'compileGrammar' can be; its two instances are all
-- there is.
class Tracker t where
  -- | Something described by the 'Expected' failed at an offset.
  failedAt  :: t -> Int -> Expected -> t
  -- | Something that is not worth describing failed at an offset.
  failedAt_ :: t -> Int -> t
  -- | Run a step under a 'Label'.
  labelled  :: String -> Step s t a -> Step s t a

-- | The furthest failure offset.
--
-- When the offset is no further, the box passed in is returned as it is, so
-- a new 'Int' is allocated only when the furthest failure moves forward —
-- at most once per character of input, and in practice far less often.
-- What was expected is never looked at, and never built.
instance Tracker Int where
  failedAt far off _ = noteAt far off
  failedAt_          = noteAt
  labelled _ p       = p
  {-# INLINE failedAt #-}
  {-# INLINE failedAt_ #-}
  {-# INLINE labelled #-}

noteAt :: Int -> Int -> Int
noteAt far@(I# f) (I# o)
  | isTrue# (o ># f) = I# o
  | otherwise        = far
{-# INLINE noteAt #-}

-- | The second pass: the offset of the error, found by the first, and what
-- has been expected there so far, most recent first.
data Diag = Diag !Int [Expected]

instance Tracker Diag where
  failedAt d@(Diag f es) off e
    | off == f  = Diag f (e : es)
    | otherwise = d
  failedAt_ d _ = d
  labelled l p = \tau (Diag f outer) st ->
    let finish (Diag _ inner) = Diag f (own inner ++ outer)
        own inner
          | null l                         = []
          | stOff st == f, not (null inner) = [ExpLabel l]
          | otherwise                      = inner
    in case p tau (Diag f []) st of
         (# d | #)               -> (# finish d | #)
         (# | (# x, s1, d #) #) -> (# | (# x, s1, finish d #) #)

-- | What a 'Diag' collected, in the order it was tried, without repeats.
expectedIn :: Diag -> [Expected]
expectedIn (Diag _ es) = go Set.empty (reverse es)
  where
    go _ [] = []
    go seen (e : rest)
      | Set.member e seen = go seen rest
      | otherwise         = e : go (Set.insert e seen) rest

-- | Fail at an offset.
--
-- The tracker is forced before it goes into the result.  A field of an
-- unboxed sum is lazy, and left alone this would build a thunk on every
-- failure — the one thing a failing step must not do.
failOff :: Tracker t => t -> Int -> Expected -> Res s t a
failOff t off e = case failedAt t off e of !t' -> (# t' | #)
{-# INLINE failOff #-}

failOff_ :: Tracker t => t -> Int -> Res s t a
failOff_ t off = case failedAt_ t off of !t' -> (# t' | #)
{-# INLINE failOff_ #-}

-- | How a set reads as an 'Expected'.
expectCS :: CharSet -> Expected
expectCS cs = case csRanges cs of
  (True, [])         -> ExpAny
  (False, [(a, b)])
    | a == b         -> ExpChar a
  _                  -> ExpClass (describeCS cs)

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
    step = compileGrammar (optTabWidth opts) g :: Step s Int a
    -- Compiled the first time a parse fails and something asks what was
    -- expected; shared from then on, like 'step'.
    diag = compileGrammar (optTabWidth opts) g :: Step s Diag a
    tau0 = optTokenMode opts
    from input = PState input 0 0 (optCands opts) False

    run input = case step tau0 0 (from input) of
      (# far | #)            -> Fail (parseErrorAt input far (expected input far))
      (# | (# a, st, _ #) #) -> OK a (takeS (stOff st) input) (stInput st)

    expected input far = case diag tau0 (Diag far []) (from input) of
      (# d | #)              -> expectedIn d
      -- Cannot happen: the grammar failed on this input a moment ago.
      (# | (# _, _, d #) #) -> expectedIn d
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
data CRules (s :: Type) (t :: Type) (defs :: Env) where
  CNil  :: CRules s t '[]
  CCons :: Step s t a
        -> CRules s t rest
        -> CRules s t ('(n, 'EnvEntry a) ': rest)

clookup :: Member n defs a -> CRules s t defs -> Step s t a
clookup Here      (CCons f _)    = f
clookup (There m) (CCons _ rest) = clookup m rest

-- | A compiled rule, wrapped so that 'Step' can be the image of a 'Table'.
newtype CStep s t a = CStep { unCStep :: Step s t a }

-- | Traverse the grammar once and return a closure that consumes input.
--
-- The traversal resolves every non-terminal reference to the corresponding
-- compiled rule, so at parse time a non-terminal costs one indirect call
-- instead of a walk down the rule list.
compileGrammar :: forall s t nt a. (Stream s, Tracker t)
               => Int -> Grammar s nt a -> Step s t a
compileGrammar tw (Grammar rules start) = compileListed tw rules start
compileGrammar tw (Keyed rules start)   = compileKeyed tw tabulate rules start

-- | A grammar over a type-level environment: the rules are compiled into a
-- list, and a reference is resolved by following its membership proof down
-- that list, once, while the grammar is being compiled.
compileListed :: forall s t env a. (Stream s, Tracker t)
              => Int -> Rules s env env -> PExp s (InEnv env) a -> Step s t a
compileListed tw rules start = compileE tw resolve start
  where
    table :: CRules s t env
    table = build rules

    resolve :: forall b. InEnv env b -> Step s t b
    resolve (InEnv w) = clookup w table

    build :: forall defs. Rules s env defs -> CRules s t defs
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
-- 'Stream' and 'Tracker' left to specialise on, the two compile to the same
-- code.
compileKeyed :: forall s t nt a. (Stream s, Tracker t)
             => Int
             -> (forall f. (forall b. nt b -> f b) -> Table nt f)
             -> (forall b. nt b -> PExp s nt b)
             -> PExp s nt a
             -> Step s t a
compileKeyed tw tab rules start = compileE tw resolve start
  where
    table :: Table nt (CStep s t)
    table = tab (\k -> CStep (compileE tw resolve (rules k)))

    resolve :: forall b. nt b -> Step s t b
    resolve k = unCStep (lookupTable table k)
{-# INLINABLE compileKeyed #-}

{-# INLINABLE compileGrammar #-}
{-# INLINABLE compileE #-}
-- Without these the whole parse runs through a 'Stream' dictionary, and the
-- per-character path stops being allocation-free.  Callers using another
-- stream should mark their own monomorphic parser bindings INLINABLE.  Only
-- the parsing tracker is listed: the second pass runs once per failed parse.
{-# SPECIALIZE compileGrammar
      :: Int -> Grammar String nt a -> Step String Int a #-}
{-# SPECIALIZE compileGrammar
      :: Int -> Grammar T.Text nt a -> Step T.Text Int a #-}
{-# SPECIALIZE compileGrammar
      :: Int -> Grammar B.ByteString nt a -> Step B.ByteString Int a #-}

-- | Does this class avoid the two characters whose column advance is not
-- simply @+1@?  When it does, the column after a matched run is the column
-- before it plus the run's length, and no fold is needed.
simpleCS :: CharSet -> Bool
simpleCS cs = not (memberCS '\n' cs) && not (memberCS '\t' cs)

-- | A compiled step, in a box the optimiser cannot see through; see @node@ in
-- 'compileE'.  The field is lazy, so that a reference to a rule is not forced
-- while the rule table that it points into is still being built.
data Box a = Box a

compileE :: forall s t nt a. (Stream s, Tracker t)
         => Int -> (forall b. nt b -> Step s t b) -> PExp s nt a -> Step s t a
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

    -- Each terminal is compiled with its description as an 'Expected'.  It is
    -- a thunk built once per grammar node, and forced only by the second
    -- pass; while parsing, the 'Int' tracker ignores it.
    comp :: forall b. PExp s nt b -> Step s t b
    comp e = case node e of Box p -> p

    -- Every node returns its step in a 'Box'.  A function returning a data
    -- constructor cannot be eta-expanded, and that is the point: without the
    -- box GHC gave the compiler the step's three arguments as well, judged
    -- the partial application @comp e@ cheap, and moved it inside the
    -- step's lambda — so the grammar was walked again on every step taken,
    -- a million times in two hundred parses on the benchmarks.
    node :: forall b. PExp s nt b -> Box (Step s t b)
    -- Inlined into @comp@, the box would be taken apart again by a case of a
    -- known constructor, and the eta-expansion would be back.
    {-# NOINLINE node #-}

    node (Pure x) = Box $ \_ t st -> (# | (# x, st, t #) #)

    node (Term c) = Box $ satStep (c ==) (ExpChar c)

    node (Sat cs) = Box $ satStep (\c -> memberCS c cs) (expectCS cs)

    node AnyChar  = Box $ satStep (const True) ExpAny

    node (Str lit) = Box $ litStep lit

    -- Consumes nothing: the offset is already in the state.
    node GetOffset = Box $ \_ t st -> (# | (# stOff st, st, t #) #)

    -- A run of a character class, returned as a chunk of the stream.  On
    -- 'Data.Text.Text' this is a slice: no copy, no cons cells.
    node (Span  cs) = Box $ spanChunk (\c -> memberCS c cs) (simpleCS cs) False (expectCS cs)
    node (Span1 cs) = Box $ spanChunk (\c -> memberCS c cs) (simpleCS cs) True  (expectCS cs)

    -- The key has already been resolved to its compiled rule by whoever
    -- built @resolve@; this is one lookup per occurrence, at compile time.
    node (NT k) = Box $ resolve k

    -- While parsing, this is @comp e@ itself: the 'Int' tracker's 'labelled'
    -- is the identity, so a label costs nothing until a parse has failed.
    node (Label l e) = Box $ labelled l (comp e)

    -- Neither this nor 'Map' below allocates: the intermediate results travel
    -- in registers, so a quasi-quoted rule of @n@ items costs @n@ calls and
    -- nothing else.
    node (Seq ef ex) = Box $
      let pf = comp ef
          px = comp ex
      in \tau t st -> case pf tau t st of
           (# f | #)               -> (# f | #)
           (# | (# g, s1, t1 #) #) -> case px tau t1 s1 of
             (# f | #)               -> (# f | #)
             (# | (# x, s2, t2 #) #) -> (# | (# g x, s2, t2 #) #)

    -- The second alternative starts from where the first one got furthest.
    node (Choice e1 e2) = Box $
      let p = comp e1
          q = comp e2
      in \tau t st -> case p tau t st of
           (# f | #) -> q tau f st
           r         -> r

    -- A hand-written @'Star' ('Sat' cs)@ still produces a @['Char']@ rather
    -- than a chunk, so it needs its own scanner.  The quasi-quoter emits
    -- 'Span' instead, but 'PExp' values built by hand can be either.
    node (Star (Sat cs)) = Box $ spanList (\c -> memberCS c cs) (simpleCS cs) (expectCS cs)
    node (Star (Term c)) = Box $ spanList (c ==) (c /= '\n' && c /= '\t') (ExpChar c)
    node (Star AnyChar)  = Box $ spanList (const True) False ExpAny

    -- The failure that ends the repetition is kept: an iteration that got
    -- some way before failing may be the furthest the parse ever gets.
    node (Star e) = Box $
      let p = comp e
          go acc tau t st = case p tau t st of
            (# f | #)                -> (# | (# reverse acc, st, f #) #)
            (# | (# x, st', f #) #)  -> go (x : acc) tau f st'
      in go []

    -- A negative lookahead at a single character only needs to peek.  Only
    -- @!.@ says what it wanted: the end of the input.
    node (Not (Sat cs))   = Box $ notCharStep (\c -> memberCS c cs) Nothing
    node (Not (Term c))   = Box $ notCharStep (c ==) Nothing
    node (Not AnyChar)    = Box $ notCharStep (const True) (Just ExpEnd)
    -- @!e+@ succeeds exactly when the next character is not in the class, so
    -- it is the same peek.  Without this case the generic 'Not' below would
    -- run the whole scan to answer a one-character question.
    node (Not (Span1 cs)) = Box $ notCharStep (\c -> memberCS c cs) Nothing
    -- @!e*@ can never succeed: the star always matches, if only the empty
    -- run.  Say so directly rather than scanning the input to find out.
    node (Not (Span _))   = Box $ \_ t st -> failOff_ t (stOff st)

    -- What fails inside a lookahead is not an error, so whatever it recorded
    -- is dropped either way.
    node (Not e) = Box $
      let p = comp e
      in \tau t st -> case p tau t st of
           (# _ | #) -> (# | (# (), st, t #) #)
           _         -> failOff_ t (stOff st)

    node (Map f e) = Box $
      let p = comp e
      in \tau t st -> case p tau t st of
           (# r | #)               -> (# r | #)
           (# | (# x, s1, t1 #) #) -> (# | (# f x, s1, t1 #) #)

    node (Indent rho e) = Box $
      let p  = comp e
          !rd = relD rho
      in \tau t st ->
           case p tau t st { stCands = preimage rd (stCands st) } of
             (# f | #)               -> (# f | #)
             (# | (# x, s1, t1 #) #) ->
               (# | (# x
                     , s1 { stCands = interI (stCands st)
                                             (image rd (stCands s1)) }
                     , t1 #) #)

    node (Position sigma e) = Box $
      let p  = comp e
          !rd = relD sigma
      in \_ t st -> p rd t st

    node (Align e) = Box $
      let p = comp e
      in \tau t st -> case p tau t st { stAlign = True } of
           (# f | #)               -> (# f | #)
           (# | (# x, s1, t1 #) #) ->
             (# | (# x, s1 { stAlign = stAlign st && stAlign s1 }, t1 #) #)

    ------------------------------------------------------------------------
    -- Terminals.  These live here rather than at the top level so that they
    -- close over the hoisted stream operations above.
    ------------------------------------------------------------------------

    -- | Match one character satisfying a predicate.  The predicate is tested
    -- /before/ any column bookkeeping, so a failing alternative costs one
    -- comparison and nothing else.
    satStep :: (Char -> Bool) -> Expected -> Step s t Char
    satStep p e = \tau t st -> case uncons (stInput st) of
      (# | (# x, xs #) #) | p x -> advance tw tau t st x xs e
      _                         -> failOff t (stOff st) e
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
    litStep :: String -> Step s t String
    litStep lit = \tau t st0 ->
      let fast rest [] !col !off cands =
            (# | (# lit, PState rest col off cands False, t #) #)
          fast rest (c : cs) !col !off cands = case uncons rest of
            (# | (# x, xs #) #)
              | x == c -> fast xs cs (nextCol tw col x) (off + 1) cands
            _          -> failOff t (stOff st0) e

          slow []       st = (# | (# lit, st, t #) #)
          slow (c : cs) st = case uncons (stInput st) of
            (# | (# x, xs #) #)
              | x == c -> case advance tw tau t st x xs e of
                            (# _ | #)               -> failOff t (stOff st0) e
                            (# | (# _, st', _ #) #) -> slow cs st'
            _          -> failOff t (stOff st0) e
      in if plainly tau st0
           then fast (stInput st0) lit (stCol st0) (stOff st0) (stCands st0)
           else slow lit st0
      where e = ExpString lit

    -- | A run of a character class, returned as a chunk.
    --
    -- On the fast path this is one native @span@ — a slice for 'Text' and
    -- 'ByteString' — plus, when the class can contain a newline or a tab, one
    -- fold to find the resulting column.  The character the run stops at
    -- counts as a failure there, as it would for the equivalent 'Star'.
    spanChunk :: (Char -> Bool) -> Bool -> Bool -> Expected -> Step s t s
    spanChunk p simple atLeastOne e = go
      where
        go tau t st
          | plainly tau st = case uncons (stInput st) of
              -- Peek before spanning.  A class that cannot match the very
              -- next character is the common case in an ordered choice, and
              -- calling 'spanS' just to be handed an empty prefix would
              -- allocate a pair on every failed alternative.
              (# | (# c, _ #) #) | p c -> chunk t st
              _ | atLeastOne -> failOff t (stOff st) e
                | otherwise  -> case failedAt t (stOff st) e of
                    !f -> (# | (# emptyS, st, f #) #)
          | otherwise = loop [] tau t st

        chunk t st = case spanS' p (stInput st) of
          (pre, rest) ->
            let !n    = lenS' pre
                !col' = if simple then stCol st + n
                                  else foldS' (nextCol tw) (stCol st) pre
                !off' = stOff st + n
                !f    = failedAt t off' e
            in (# | (# pre, PState rest col' off' (stCands st) False, f #) #)

        -- The layout-sensitive path: every character has to go through the
        -- interval arithmetic, so the chunk is rebuilt from the characters.
        loop acc tau t st = case satStep p e tau t st of
          (# | (# x, st', f #) #) -> loop (x : acc) tau f st'
          (# f | #)
            | atLeastOne && null acc -> (# f | #)
            | otherwise -> (# | (# packS (reverse acc), st, f #) #)

    -- | A run of a character class, returned as a @['Char']@.  Only reachable
    -- from a hand-written @'Star' ('Sat' _)@; the quasi-quoter emits 'Span'.
    spanList :: (Char -> Bool) -> Bool -> Expected -> Step s t String
    spanList p simple e = go
      where
        go tau t st
          | plainly tau st = case uncons (stInput st) of
              (# | (# c, _ #) #) | p c -> case spanS' p (stInput st) of
                (pre, rest) ->
                  let !n    = lenS' pre
                      !col' = if simple then stCol st + n
                                        else foldS' (nextCol tw) (stCol st) pre
                      !off' = stOff st + n
                      !f    = failedAt t off' e
                  in (# | (# toStr pre
                           , PState rest col' off' (stCands st) False
                           , f #) #)
              _ -> case failedAt t (stOff st) e of
                     !f -> (# | (# [], st, f #) #)
          | otherwise = loop [] tau t st

        loop acc tau t st = case satStep p e tau t st of
          (# | (# x, st', f #) #) -> loop (x : acc) tau f st'
          (# f | #)               -> (# | (# reverse acc, st, f #) #)

    -- | Negative lookahead at a single character: a peek, with no state built.
    -- It fails, when the character is there, as @wanted@ says.
    notCharStep :: (Char -> Bool) -> Maybe Expected -> Step s t ()
    notCharStep p wanted = go
      where
        failHere t st = case wanted of
          Just e  -> failOff t (stOff st) e
          Nothing -> failOff_ t (stOff st)

        go tau t st
          | plainly tau st = case uncons (stInput st) of
              (# | (# x, _ #) #) | p x -> failHere t st
              _                        -> (# | (# (), st, t #) #)
          | otherwise = case satStep p ExpAny tau t st of
              (# _ | #) -> (# | (# (), st, t #) #)
              _         -> failHere t st

--------------------------------------------------------------------------------
-- Column bookkeeping
--------------------------------------------------------------------------------

-- | Consume the head character, updating column, offset and the candidate
-- interval.  A character the indentation constraints reject fails at its own
-- offset, like one that does not match, and is described the same way.
--
-- When the ambient relation is total ('rdTotal', i.e. 'anyR') and no
-- alignment is pending, the candidate interval is provably unchanged, so the
-- whole interval computation is skipped.  Grammars that do not use layout
-- take this branch for every single character.
advance :: Tracker t
        => Int -> RelD -> t -> PState s -> Char -> s -> Expected -> Res s t Char
-- The state is taken apart rather than bound whole: failing needs only its
-- offset, and holding on to the whole state made GHC rebuild it, inside the
-- worker it unpacks it into, on every call.
advance tw tau t (PState _ col off cands aligned) x xs e
  | aligned =
      if memberI col cands
        then (# | (# x, PState xs col' off' (singletonI col) False, t #) #)
        else failOff t off e
  | rdTotal tau =
      if nullI cands
        then failOff t off e
        else (# | (# x, PState xs col' off' cands False, t #) #)
  | memberI col (preimage tau cands) =
      (# | (# x, PState xs col' off'
                        (interI cands (image tau (singletonI col))) False
           , t #) #)
  | otherwise = failOff t off e
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
