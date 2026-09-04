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

-- | Running a 'Grammar' against a 'String'.
--
-- The top-level entry points are 'parse' (uses 'defaultOpts') and 'parseWith'
-- (accepts custom 'Opts' for indentation-sensitive parsing).  Both return a
-- 'Result' that records the matched value, the consumed prefix, and the
-- remaining suffix.
--
-- == Compiling once, parsing many times
--
-- 'parseWith' is written so that @'parseWith' opts g@ is a /closure/ that has
-- already traversed the grammar: every non-terminal reference has been
-- resolved to a function, and no 'PExp' constructor is examined again while
-- input is being consumed.  Bind it once and reuse it:
--
-- @
-- myParser :: String -> Result Exp
-- myParser = parse myGrammar     -- compiled once, at first use
-- @
--
-- Writing @'parse' myGrammar input@ inline inside a loop instead re-does the
-- traversal on every call.
--
-- == Why the result of a step is an unboxed sum
--
-- A compiled step returns @(# (# #) | (# a, 'PState' #) #)@ rather than
-- @'Maybe' (a, 'PState')@.  The two are isomorphic, but the unboxed sum lives
-- in registers: a step that succeeds no longer allocates a @Just@ /and/ a
-- pair on top of the new state, and a step that fails allocates nothing at
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

import PEG.CharSet (memberCS)
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

-- | Internal parser state.
--
-- The column of the character at the head of 'stInput' is carried alongside
-- the input rather than being precomputed for the whole string, so no
-- @[(Char, Int)]@ list is ever allocated.
data PState = PState
  { stInput :: String    -- ^ Remaining input.
  , stCol   :: !Int      -- ^ Column of the head of 'stInput'.
  , stOff   :: !Int      -- ^ Characters consumed so far.
  , stCands :: !Interval -- ^ Current candidate column interval.
  , stAlign :: !Bool     -- ^ Whether the next token must be aligned.
  }

-- | What a compiled step returns: either failure (the left injection, which
-- carries nothing) or a value together with the state after it.
--
-- This is @'Maybe' (a, 'PState')@ with the two boxes removed.
type Res a = (# (# #) | (# a, PState #) #)

-- | A compiled parser: it still takes the ambient column relation, because a
-- rule body inherits the relation in force at its call site.
type Step a = RelD -> PState -> Res a

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
parse :: Grammar env ty a -> String -> Result a
parse = parseWith defaultOpts

-- | Run a grammar with custom 'Opts'.
--
-- Partially applying this to the options and the grammar yields a compiled
-- parser; see the note at the top of this module.
parseWith :: Opts -> Grammar env ty a -> String -> Result a
parseWith opts g = run
  where
    step = compileGrammar (optTabWidth opts) g
    tau0 = optTokenMode opts
    st0 input = PState input 0 0 (optCands opts) False

    run input = case step tau0 (st0 input) of
      (# (# #) | #)       -> Fail
      (# | (# a, st #) #) -> OK a (take (stOff st) input) (stInput st)

--------------------------------------------------------------------------------
-- Compilation
--------------------------------------------------------------------------------

-- | A rule table in which every body has already been compiled to a 'Step'.
-- Built with a knot so that mutually recursive rules resolve to each other's
-- closures.
data CRules (env :: Env) (defs :: Env) where
  CNil  :: CRules env '[]
  CCons :: Step a
        -> CRules env rest
        -> CRules env ('(s, 'EnvEntry ty a) ': rest)

clookup :: Member s defs ty a -> CRules env defs -> Step a
clookup Here      (CCons f _)    = f
clookup (There m) (CCons _ rest) = clookup m rest

-- | Traverse the grammar once and return a closure that consumes input.
--
-- The traversal resolves every non-terminal reference to the corresponding
-- compiled rule, so at parse time a non-terminal costs one indirect call
-- instead of a walk down the rule list.
compileGrammar :: forall env ty a. Int -> Grammar env ty a -> Step a
compileGrammar tw (Grammar rules start) = compileE tw table start
  where
    table :: CRules env env
    table = build rules

    build :: forall defs. Rules env defs -> CRules env defs
    build RNil                = CNil
    build (RCons _ body rest) = CCons (compileE tw table body) (build rest)

compileE :: forall env ty a. Int -> CRules env env -> PExp env ty a -> Step a
compileE tw table = comp
  where
    comp :: forall t b. PExp env t b -> Step b

    comp (Pure x) = \_ st -> (# | (# x, st #) #)

    comp (Term c) = satStep tw (c ==)

    comp (Sat cs) = satStep tw (\c -> memberCS c cs)

    comp AnyChar  = satStep tw (const True)

    comp (Str s)  = litStep tw s

    comp (NT (_ :: Name s)) =
      clookup (member :: Member s env (TyOf (Lookup s env))
                                      (ResOf (Lookup s env)))
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

    -- A repetition of a single character -- @[0-9]*@, @[ \\t]*@, @.*@ -- is by
    -- far the most common shape of 'Star' in a real grammar, and the generic
    -- loop pays a fresh 'PState' for every character it accepts.  Compile
    -- these to a scan instead.
    comp (Star (Sat cs)) = spanStep tw (\c -> memberCS c cs)
    comp (Star (Term c)) = spanStep tw (c ==)
    comp (Star AnyChar)  = spanStep tw (const True)

    comp (Star e) =
      let p = comp e
          go acc tau st = case p tau st of
            (# (# #) | #)        -> (# | (# reverse acc, st #) #)
            (# | (# x, st' #) #) -> go (x : acc) tau st'
      in go []

    -- Likewise, a negative lookahead at a single character only needs to peek.
    comp (Not (Sat cs)) = notCharStep tw (\c -> memberCS c cs)
    comp (Not (Term c)) = notCharStep tw (c ==)
    comp (Not AnyChar)  = notCharStep tw (const True)

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

--------------------------------------------------------------------------------
-- Terminals
--------------------------------------------------------------------------------

-- | Match one character satisfying a predicate.
--
-- The predicate is tested /before/ any column bookkeeping, so a failing
-- alternative costs one comparison and nothing else.
satStep :: Int -> (Char -> Bool) -> Step Char
satStep tw p = \tau st -> case stInput st of
  (x : xs) | p x -> advance tw tau st x xs
  _              -> (# (# #) | #)
{-# INLINE satStep #-}

-- | Match a literal string.
--
-- On the fast path (see 'plainly') the whole literal is matched with a single
-- loop and a single new 'PState'; otherwise it goes character by character so
-- that column bookkeeping stays exactly as it would be for the equivalent
-- chain of 'Term's.
litStep :: Int -> String -> Step String
litStep tw lit = \tau st ->
  if plainly tau st
    then fast (stInput st) lit (stCol st) (stOff st) (stCands st)
    else slow lit tau st
  where
    fast s []       !col !off cands =
      (# | (# lit, PState s col off cands False #) #)
    fast (x : xs) (c : cs) !col !off cands
      | x == c    = fast xs cs (nextCol tw col x) (off + 1) cands
    fast _ _ _ _ _ = (# (# #) | #)

    slow []       _   s = (# | (# lit, s #) #)
    slow (c : cs) tau s = case stInput s of
      (x : xs) | x == c -> case advance tw tau s x xs of
                             (# (# #) | #)       -> (# (# #) | #)
                             (# | (# _, s' #) #) -> slow cs tau s'
      _                 -> (# (# #) | #)

-- | Consume the head character, updating column, offset and the candidate
-- interval.
--
-- When the ambient relation is total ('rdTotal', i.e. 'anyR') and no
-- alignment is pending, the candidate interval is provably unchanged, so the
-- whole interval computation is skipped.  Grammars that do not use layout
-- take this branch for every single character.
advance :: Int -> RelD -> PState -> Char -> String -> Res Char
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
plainly :: RelD -> PState -> Bool
plainly tau st = rdTotal tau && not (stAlign st) && not (nullI (stCands st))
{-# INLINE plainly #-}

-- | @'Star'@ of a single-character expression, as a scan.
spanStep :: Int -> (Char -> Bool) -> Step String
spanStep tw p = go
  where
    go tau st
      | plainly tau st =
          let s = stInput st
          in case scan 0 (stCol st) s of
               (# n, col' #) ->
                 (# | (# take n s
                       , PState (drop n s) col' (stOff st + n)
                                (stCands st) False #) #)
      | rdTotal tau && not (stAlign st) =
          -- The interval is empty, so no character can be consumed at all.
          (# | (# [], st #) #)
      | otherwise = loop [] tau st

    loop acc tau st = case satStep tw p tau st of
      (# (# #) | #)        -> (# | (# reverse acc, st #) #)
      (# | (# x, st' #) #) -> loop (x : acc) tau st'

    scan :: Int -> Int -> String -> (# Int, Int #)
    scan !k !c (x : xs) | p x = scan (k + 1) (nextCol tw c x) xs
    scan !k !c _              = (# k, c #)

-- | @'Not'@ of a single-character expression: a peek, with no state to build.
notCharStep :: Int -> (Char -> Bool) -> Step ()
notCharStep tw p = go
  where
    go tau st
      | plainly tau st = case stInput st of
          (x : _) | p x -> (# (# #) | #)
          _             -> (# | (# (), st #) #)
      | otherwise = case satStep tw p tau st of
          (# (# #) | #) -> (# | (# (), st #) #)
          _             -> (# (# #) | #)
