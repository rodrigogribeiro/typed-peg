-- | Nullability, FIRST sets and well-formedness, computed in Haskell.
--
-- This module is the value-level twin of "PEG.TyLevel" and "PEG.Grammar":
-- it computes, from the grammar DSL's syntax tree, exactly the environment
-- that GHC would otherwise derive by reducing 'PEG.Syntax.SeqTy',
-- 'PEG.Syntax.ChoiceTy' and 'PEG.TyLevel.Union' while type-checking a
-- 'PEG.Grammar.Rules' value.
--
-- == Why it moved here
--
-- It used to be a type-level computation, and that is what made left
-- recursion a type error.  It was billed to every compilation of every module
-- that mentioned the grammar, and its cost grew sharply with the grammar's
-- size: every entry of the environment carried a FIRST set, so the
-- environment was quadratic in the number of rules, and each of the two
-- reference constraints per rule had to be solved against it.  A 64-rule
-- grammar cost GHC 15 s.  The same fixpoint runs here, at splice time and
-- once, in 6 ms for that grammar and 286 ms for one of 256 rules.  See
-- @bench-compile/@ for the measurements and "PEG.Type" for the trade.
--
-- == This module is now load-bearing
--
-- While the FIRST sets were also in the types, this module could be wrong
-- without being dangerous: GHC recomputed everything and rejected a grammar
-- whose environment did not match.  It no longer does.  A left-recursive
-- grammar that this module accepts is a parser that loops.
--
-- What replaces the type checker is @tests/typed-peg-analysis@, which checks
-- the results here against a straightforward statement of what they mean —
-- nullability as a least fixpoint, and a FIRST set as the transitive closure
-- of the one-step head relation — over the grammars in @examples/@ and over a
-- few hundred generated ones.
--
-- == The fixpoint
--
-- Nullability and FIRST are both computed as the least solution of the
-- equations the type families state.  For a grammar without left recursion
-- that solution is the only one, which is why GHC can find it by unification
-- alone; for a left-recursive grammar the least solution is the one that puts
-- a non-terminal in its own FIRST set, which is precisely what
-- 'PEG.Grammar.Acyclic' rejects.
module PEG.Analysis
  ( Ty (..)
  , RuleEnv
  , Diagnostic (..)
  , World (..)
  , analyse
  , analyseWith
  , exprTy
  , seqTy
  , choiceTy
  , insertSym
  , unionSym
  , renderEnv
  , renderDiagnostic
  , spannable
  ) where

import Data.List (foldl1', nub)
import Data.Maybe (fromMaybe)

import PEG.QQ.Syntax (Def (..), Item (..), PExpr (..))

-- | The value-level image of 'PEG.Type.Ty': a nullability flag and a FIRST
-- set of non-terminal names.
--
-- The FIRST set is kept strictly sorted by 'compare', which agrees with
-- 'GHC.TypeLits.CmpSymbol' on the identifiers the DSL admits.  Sortedness is
-- what makes the set canonical, so that a generated environment is
-- /syntactically/ the type GHC computes rather than merely an equivalent one.
data Ty = Ty
  { tyNullable :: !Bool
  , tyFirst    :: ![String]
  } deriving (Eq, Show)

-- | A grammar environment in definition order: the value-level image of
-- 'PEG.Type.Env', minus the result types, which only the type checker knows.
type RuleEnv = [(String, Ty)]

-- | Something that makes the grammar ill-formed.
--
-- Each of these used to be a type error — or, in the case of 'NullableStar',
-- a type error whose message mentioned neither the rule nor the repetition
-- that caused it.  Reporting them here means naming the rule, and is now the
-- only place any of them is reported.
data Diagnostic
  = -- | A non-terminal is in its own FIRST set, with the chain of head
    -- references that puts it there.
    LeftRecursive String [String]
  | -- | @e*@ or @e+@ where @e@ can match the empty string: the repetition
    -- would not consume input and the parser would not terminate.
    NullableStar String
  | -- | A rule body references a name that no rule defines; the second field
    -- lists the names that are defined.
    UndefinedNT String [String]
  | -- | Two rules with the same name.
    DuplicateRule String
  deriving (Eq, Show)

--------------------------------------------------------------------------------
-- Sorted sets, mirroring PEG.TyLevel
--------------------------------------------------------------------------------

-- | The image of 'PEG.TyLevel.ConsIfAbsent'.
insertSym :: String -> [String] -> [String]
insertSym x [] = [x]
insertSym x (y:ys) = case compare x y of
  LT -> x : y : ys
  EQ -> y : ys
  GT -> y : insertSym x ys

-- | The image of 'PEG.TyLevel.Union': a single merge pass over two sorted
-- sets.
unionSym :: [String] -> [String] -> [String]
unionSym [] ys = ys
unionSym xs [] = xs
unionSym (x:xs) (y:ys) = case compare x y of
  LT -> x : unionSym xs (y:ys)
  EQ -> x : unionSym xs ys
  GT -> y : unionSym (x:xs) ys

-- | The image of 'PEG.Syntax.SeqTy'.
seqTy :: Ty -> Ty -> Ty
seqTy t1 t2 =
  Ty (tyNullable t1 && tyNullable t2)
     (unionSym (tyFirst t1) (if tyNullable t1 then tyFirst t2 else []))

-- | The image of 'PEG.Syntax.ChoiceTy'.
choiceTy :: Ty -> Ty -> Ty
choiceTy t1 t2 =
  Ty (tyNullable t1 || tyNullable t2)
     (unionSym (tyFirst t1) (tyFirst t2))

nullTy, termTy :: Ty
nullTy = Ty True  []
termTy = Ty False []

--------------------------------------------------------------------------------
-- The type of one expression
--------------------------------------------------------------------------------

-- | The 'Ty' of a DSL expression, given the 'Ty' of every non-terminal it may
-- reference.
--
-- This has to follow @PEG.QQ.translateExpr@ case for case, including its
-- optimisations: a repetition of a bare class, character or dot compiles to
-- 'PEG.Syntax.Span' or 'PEG.Syntax.Span1' rather than to
-- 'PEG.Syntax.Star', and those two have different FIRST sets from the generic
-- form.  A case that disagrees with the translation produces an environment
-- GHC will reject.
exprTy :: (String -> Ty) -> PExpr -> Ty
exprTy look = go
  where
    go (EChar _)        = termTy
    go EDot             = termTy
    go (EClass _ _)     = termTy
    go (EString s)
      | null s          = nullTy          -- pureP ""
      | otherwise       = termTy
    -- NTGo: the reference adds its own name to the rule's FIRST set.
    go (ENT n)          = let t = look n
                          in Ty (tyNullable t) (insertSym n (tyFirst t))
    -- Both lookaheads are 'Not' at bottom, which is nullable and keeps the
    -- FIRST set of its operand.  @&e@ is @Not (Not e)@.
    go (EAnd e)         = Ty True (tyFirst (go e))
    go (ENot e)         = Ty True (tyFirst (go e))
    go (EOpt e)         = choiceTy (go e) nullTy
    go (EStar e)
      | spannable e     = nullTy          -- spanOf
      | otherwise       = Ty True (tyFirst (go e))
    go (EPlus e)
      | spannable e     = termTy          -- spanOf1
      | otherwise       = let t = go e in seqTy t (Ty True (tyFirst t))
    go (EIndent _ e)    = go e
    go (EPos _ e)       = go e
    go (EAlign e)       = go e
    go (EChoice es)     = foldl1' choiceTy (map go es)
    go (ESeq [] _)      = nullTy          -- pureP
    go (ESeq items _)   = foldl1' seqTy [ go e | Item _ e <- items ]

-- | Does a repetition of this expression compile to a 'PEG.Syntax.Span'?
spannable :: PExpr -> Bool
spannable (EClass _ _) = True
spannable (EChar _)    = True
spannable EDot         = True
spannable _            = False

--------------------------------------------------------------------------------
-- The grammar
--------------------------------------------------------------------------------

-- | Is this the whole grammar, or part of one?
--
-- 'PEG.Grammar.RCons' is exported, so two quasi-quoted blocks can be spliced
-- into one rule set and a rule in the first may reference a rule in the
-- second.  A block analysed 'Open' therefore treats an unknown name as
-- opaque — non-nullable, with an empty FIRST set — instead of reporting it.
--
-- Under-approximating a FIRST set loses a 'LeftRecursive' or a
-- 'NullableStar'; over-approximating would reject a grammar that is fine.
-- The second is the worse failure, so an unknown name is treated as opaque —
-- but nothing catches what that loses, since the type checker no longer
-- computes FIRST sets of its own.  Left recursion that closes across two
-- blocks spliced together is reported by nobody; a grammar written as a
-- single 'PEG.QQ.pegGrammar' is 'Closed' and has no such gap.  The
-- environment returned for an 'Open' block is, for the same reason, not the
-- grammar's environment: only the diagnostics are meaningful.
data World = Closed | Open
  deriving (Eq, Show)

-- | Compute the environment of a complete set of rules, or report why it has
-- none.
--
-- All diagnostics of a kind are reported together, so a grammar with three
-- undefined non-terminals names all three rather than one per recompilation.
analyse :: [Def] -> Either [Diagnostic] RuleEnv
analyse = analyseWith Closed

-- | 'analyse', over a whole grammar or a fragment of one.
analyseWith :: World -> [Def] -> Either [Diagnostic] RuleEnv
analyseWith world defs
  | not (null dups)      = Left dups
  | not (null undefs)    = Left undefs
  | not (null illFormed) = Left illFormed
  | not (null leftRecs)  = Left leftRecs
  | otherwise            = Right env
  where
    names = [ n | Def n _ _ <- defs ]

    dups = [ DuplicateRule n
           | n <- nub names, length (filter (== n) names) > 1 ]

    undefs = case world of
      Open   -> []
      Closed -> [ UndefinedNT n names
                | n <- nub (concatMap (refs . body) defs), n `notElem` names ]
      where body (Def _ _ e) = e

    -- Kleene iteration from the empty environment.  Every clause of 'exprTy'
    -- is monotone in the environment and the lattice is finite, so this
    -- terminates; it is the least solution of the equations the type families
    -- state.
    env = fix [ (n, Ty False []) | n <- names ]
      where
        fix m = let m' = step m in if m' == m then m else fix m'
        step m = [ (n, exprTy (at m) e) | Def n _ e <- defs ]

    at m n = fromMaybe (Ty False []) (lookup n m)

    -- A repetition must consume input, which 'PEG.Syntax.Star' states as a
    -- non-nullable operand.  Checking it here names the rule it is in.
    illFormed = [ NullableStar n | Def n _ e <- defs, hasNullableRep (at env) e ]

    -- Every rule on a cycle is left-recursive, and reporting each of them
    -- prints the same cycle once per entry point.  Two paths that are
    -- rotations of each other are the same cycle, so only the first is kept.
    leftRecs = dedupe [] [ LeftRecursive n (cycleFrom n)
                         | (n, t) <- env, n `elem` tyFirst t ]
      where
        dedupe _ [] = []
        dedupe seen (d@(LeftRecursive _ path) : rest)
          | key `elem` seen = dedupe seen rest
          | otherwise       = d : dedupe (key : seen) rest
          where key = canonical path
        dedupe seen (d : rest) = d : dedupe seen rest

    -- A cycle is written as @n -> ... -> n@; drop the repeated end and turn
    -- it so that it starts at its least name.
    canonical path = case reverse (drop 1 (reverse path)) of
      []    -> []
      nodes -> minimum [ rotate k nodes | k <- [0 .. length nodes - 1] ]
      where rotate k xs = drop k xs ++ take k xs

    -- The FIRST set is already transitive, so it says /that/ a rule is
    -- left-recursive but not /how/.  The chain is recovered from the graph of
    -- direct head references, which is 'exprTy' again with the environment
    -- cut back to nullability alone.
    heads n = tyFirst (exprTy (\k -> Ty (tyNullable (at env k)) []) (bodyOf n))

    bodyOf n = case [ e | Def m _ e <- defs, m == n ] of
                 (e:_) -> e
                 []    -> ESeq [] Nothing

    cycleFrom n = go [n] n
      where
        go path cur = case [ h | h <- heads cur, h == n ] of
          (_:_) -> reverse (n : path)
          []    -> case [ p | h <- heads cur
                            , h `notElem` path
                            , n `elem` tyFirst (at env h)
                            , p <- [go (h : path) h]
                            , not (null p) ] of
                     (p:_) -> p
                     []    -> []

-- | Every non-terminal a body references, at any position.
refs :: PExpr -> [String]
refs (ENT n)       = [n]
refs (EAnd e)      = refs e
refs (ENot e)      = refs e
refs (EOpt e)      = refs e
refs (EStar e)     = refs e
refs (EPlus e)     = refs e
refs (EIndent _ e) = refs e
refs (EPos _ e)    = refs e
refs (EAlign e)    = refs e
refs (EChoice es)  = concatMap refs es
refs (ESeq its _)  = concat [ refs e | Item _ e <- its ]
refs _             = []

-- | Does the expression contain a repetition whose operand is nullable?
hasNullableRep :: (String -> Ty) -> PExpr -> Bool
hasNullableRep look = go
  where
    go (EStar e)     = (not (spannable e) && tyNullable (exprTy look e)) || go e
    go (EPlus e)     = (not (spannable e) && tyNullable (exprTy look e)) || go e
    go (EAnd e)      = go e
    go (ENot e)      = go e
    go (EOpt e)      = go e
    go (EIndent _ e) = go e
    go (EPos _ e)    = go e
    go (EAlign e)    = go e
    go (EChoice es)  = any go es
    go (ESeq its _)  = or [ go e | Item _ e <- its ]
    go _             = False

--------------------------------------------------------------------------------
-- Rendering
--------------------------------------------------------------------------------

-- | Render an environment as the source of a 'PEG.Type.Env' type, given a
-- result type for each rule.
--
-- Used to tell a user what to write while the environment still has to be
-- written by hand.  An entry no longer carries a FIRST set, so the analysis
-- contributes only the rule names and their order; what used to be the
-- interesting half of this function is now something no one has to write
-- down.
renderEnv :: (String -> String) -> RuleEnv -> String
renderEnv resultOf entries = unlines (zipWith line prefixes entries) ++ "   ]"
  where
    prefixes = "  '[ " : repeat "   , "
    line p (n, _) =
      p ++ "'(" ++ show n ++ ", 'EnvEntry " ++ resultOf n ++ ")"

-- | A one-paragraph explanation of a 'Diagnostic', in the shape the
-- quasi-quoter reports it.
renderDiagnostic :: Diagnostic -> String
renderDiagnostic (LeftRecursive n path) =
  "left-recursive non-terminal: " ++ n
    ++ (if null path then "" else "\n  the cycle is " ++ arrows path)
    ++ "\n  a PEG cannot backtrack into a committed choice, so this rule\n"
    ++ "  would not consume input before calling itself"
  where arrows = foldr1 (\a b -> a ++ " -> " ++ b)
renderDiagnostic (NullableStar n) =
  "in rule " ++ n ++ ": a repetition whose operand can match the empty\n"
    ++ "  string; it would not consume input and the parse would not terminate"
renderDiagnostic (UndefinedNT n defined) =
  "undefined non-terminal: " ++ n
    ++ "\n  the grammar defines " ++ unwords defined
renderDiagnostic (DuplicateRule n) =
  "the rule " ++ n ++ " is defined twice"
