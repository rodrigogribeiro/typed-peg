{-# LANGUAGE DataKinds        #-}
{-# LANGUAGE QuasiQuotes      #-}
{-# LANGUAGE TemplateHaskell  #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators    #-}
-- | Checks "PEG.Analysis" against what its results are supposed to mean.
--
-- == Why this is the whole guarantee now
--
-- It did not use to be.  Environment entries carried their FIRST sets as
-- type-level data and @Acyclic@ checked them, so every grammar that compiled
-- was a grammar GHC had agreed with, and this module only had to cover the
-- cases GHC could not see.  Entries no longer carry them — "PEG.Type" says
-- why — so nothing recomputes what "PEG.Analysis" concludes.  A left-recursive
-- grammar it accepts is a parser that loops.
--
-- So the analysis is checked here against a separate statement of what its
-- two results mean, written to be obvious rather than fast:
--
-- * a rule is nullable iff it is in the least fixpoint of "can match the
--   empty string";
-- * @FIRST(r)@ is the set of non-terminals reachable from @r@ under the
--   one-step head relation — @m@ is a head of @r@ when @m@ can be the first
--   non-terminal a derivation of @r@ reaches without any other non-terminal
--   being entered first.
--
-- The second is the definition left recursion is stated in terms of: @r@ is
-- left-recursive exactly when @r@ is reachable from itself.  "PEG.Analysis"
-- computes it a different way — it propagates whole FIRST sets through
-- 'PEG.Analysis.seqTy' and 'PEG.Analysis.choiceTy' as it iterates, over
-- sorted sets merged pairwise — so the two agreeing is worth something.
--
-- They are compared over every grammar in @examples/@ and over a few hundred
-- generated ones, which is what covers the shapes the examples happen not to
-- have.
--
-- What is also checked here:
--
-- * The diagnostics, which no example can exercise, because an example that
--   triggered one would not compile.
-- * The /shape/ of what 'PEG.QQ.pegGrammar' generates, against a literal
--   written out below, and that the grammar it generates parses.
--
-- Result types are not compared against the analysis — it does not compute
-- them, and cannot: they come from the Haskell semantic actions, which GHC
-- types long after the splice has run.
module Main (main) where

import Control.Monad (forM, unless)
import Data.List     (isPrefixOf, nub, sort, union)
import qualified Data.List as L
import System.Exit   (exitFailure)
import System.Timeout (timeout)
import Control.Exception (evaluate)

import Data.Functor.Const (Const (..))

import PEG
import PEG.QQ        (pegGrammar)
import PEG.Analysis  (Diagnostic (..), Ty (..), analyse, renderDiagnostic)
import PEG.QQ.Syntax (Def (..), Item (..), PExpr (..), parseDirectives,
                      parseGrammar)

exampleFiles :: [FilePath]
exampleFiles =
  [ "examples/Arith.hs"
  , "examples/Layout.hs"
  , "examples/Patterns.hs"
  , "examples/Compat.hs"
  , "examples/MiniPython.hs"
  ]

main :: IO ()
main = do
  results <- concat <$> mapM checkFile exampleFiles
  let failures = [ msg | Left msg <- results ]
      checked  = length [ () | Right () <- results ]
  mapM_ putStrLn failures
  putStrLn ("PEG.Analysis: " ++ show checked ++ " grammars in examples/ agree\
            \ with the specification")
  unless (null failures) exitFailure
  -- The examples are half the point of this test; a refactor that stops
  -- finding them must fail rather than pass vacuously.
  unless (checked + length failures >= 8) $ do
    putStrLn "PEG.Analysis: expected at least 8 grammars in examples/, \
             \found fewer"
    exitFailure
  let generated = [ checkDefs ("generated/" ++ show i) g
                  | (i, g) <- zip [0 :: Int ..] generatedGrammars ]
      genBad    = [ msg | Left msg <- generated ]
  mapM_ putStrLn (take 5 genBad)
  putStrLn ("PEG.Analysis: " ++ show (length generated - length genBad)
              ++ " of " ++ show (length generated)
              ++ " generated grammars agree with the specification"
              ++ " (" ++ show recursive ++ " left-recursive rules, "
              ++ show withHeads ++ " with a non-empty FIRST set)")
  unless (null genBad) exitFailure
  -- Agreement is easy to reach vacuously: a generator that stopped emitting
  -- references would make every FIRST set empty and every grammar pass.  The
  -- corpus has to keep containing both answers.
  unless (recursive >= 20 && withHeads >= 20) $ do
    putStrLn "PEG.Analysis: the generated corpus has gone degenerate"
    exitFailure
  nested <- nestingCheck
  let checks = standaloneChecks ++ [witnessCheck] ++ generatedChecks
               ++ factoringChecks ++ [nested]
  mapM_ report checks
  unless (all (\(_, ok) -> ok) checks) exitFailure
  where
    report (name, ok) =
      putStrLn ((if ok then "ok   " else "FAIL ") ++ name)

    -- Coverage of the generated corpus, measured through the specification
    -- rather than the analysis, so that it says what the corpus contains and
    -- not what the code under test thinks it contains.
    recursive = length [ () | g <- generatedGrammars
                            , (n, Ty _ f) <- specEnv g, n `elem` f ]
    withHeads = length [ () | g <- generatedGrammars
                            , any (\(_, Ty _ f) -> not (null f)) (specEnv g) ]

--------------------------------------------------------------------------------
-- The specification: what nullability and a FIRST set mean
--------------------------------------------------------------------------------

-- | The least fixpoint of "can match the empty string", over the rules.
--
-- Iterated over the whole system from "nothing is nullable" until it stops
-- changing, which is the definition rather than a way of computing it
-- quickly.
specNullable :: [Def] -> [(String, Bool)]
specNullable defs = fix [ (n, False) | Def n _ _ <- defs ]
  where
    fix m = let m' = [ (n, nu m e) | Def n _ e <- defs ]
            in if m' == m then m else fix m'

    nu m = go
      where
        go (EChar _)      = False
        go EDot           = False
        go (EClass _ _)   = False
        go (EString s)    = null s
        go (ENT n)        = maybe False id (lookup n m)
        go (EAnd _)       = True          -- a lookahead consumes nothing
        go (ENot _)       = True
        go (EOpt _)       = True
        go (EStar _)      = True
        go (EPlus e)      = go e
        go (EIndent _ e)  = go e
        go (EPos _ e)     = go e
        go (EAlign e)     = go e
        go (EChoice es)   = any go es
        go (ESeq its _)   = all (\(Item _ e) -> go e) its

-- | The one-step head relation: the non-terminals that a derivation of this
-- expression can reach first, without entering any other non-terminal on the
-- way.
--
-- A sequence contributes the heads of its first item, and those of the second
-- as well when the first can match the empty string, and so on.
specHeads :: [(String, Bool)] -> PExpr -> [String]
specHeads nulls = go
  where
    nullableOf = specNullableOf nulls

    go (EChar _)     = []
    go EDot          = []
    go (EClass _ _)  = []
    go (EString _)   = []
    go (ENT n)       = [n]
    go (EAnd e)      = go e
    go (ENot e)      = go e
    go (EOpt e)      = go e
    go (EStar e)     = go e
    go (EPlus e)     = go e
    go (EIndent _ e) = go e
    go (EPos _ e)    = go e
    go (EAlign e)    = go e
    go (EChoice es)  = L.foldl' union [] (map go es)
    go (ESeq its _)  = seqHeads [ e | Item _ e <- its ]

    seqHeads []     = []
    seqHeads (e:es) | nullableOf e = go e `union` seqHeads es
                    | otherwise    = go e

-- | Whether an expression is nullable, given the rules' nullability.
specNullableOf :: [(String, Bool)] -> PExpr -> Bool
specNullableOf nulls = go
  where
    go (EChar _)     = False
    go EDot          = False
    go (EClass _ _)  = False
    go (EString s)   = null s
    go (ENT n)       = maybe False id (lookup n nulls)
    go (EAnd _)      = True
    go (ENot _)      = True
    go (EOpt _)      = True
    go (EStar _)     = True
    go (EPlus e)     = go e
    go (EIndent _ e) = go e
    go (EPos _ e)    = go e
    go (EAlign e)    = go e
    go (EChoice es)  = any go es
    go (ESeq its _)  = all (\(Item _ e) -> go e) its

-- | The environment the analysis is supposed to produce: nullability as
-- above, and each rule's FIRST set as everything reachable from it under
-- 'specHeads'.
specEnv :: [Def] -> [(String, Ty)]
specEnv defs =
  [ (n, Ty (specNullableOf nulls e) (sort (reach (heads e)))) | Def n _ e <- defs ]
  where
    nulls = specNullable defs
    heads = specHeads nulls

    bodyOf n = case [ e | Def m _ e <- defs, m == n ] of
                 (e:_) -> Just e
                 []    -> Nothing

    -- Transitive closure by worklist.  A name the grammar does not define
    -- contributes itself and nothing further, which is how the analysis
    -- treats it too.
    reach = grow []
      where
        grow seen []     = seen
        grow seen (x:xs)
          | x `elem` seen = grow seen xs
          | otherwise     = grow (x : seen)
                                 (maybe [] heads (bodyOf x) ++ xs)

--------------------------------------------------------------------------------
-- Comparing the analysis against it
--------------------------------------------------------------------------------

-- | Check one grammar, whatever the analysis makes of it.
--
-- The two must agree on left recursion — the analysis reports it exactly when
-- a rule is reachable from itself — and, when there is none, on the whole
-- environment.
checkDefs :: String -> [Def] -> Either String ()
checkDefs what defs
  | not (null dups) = Right ()   -- a duplicate rule makes 'specEnv' meaningless
  | otherwise = case analyse defs of
      Left ds
        | not (null [ () | LeftRecursive _ _ <- ds ]) ->
            if null selfReaching
              then Left (what ++ ": analyse reports left recursion, the \
                                 \specification finds no cycle")
              else Right ()
        | otherwise -> Right ()  -- other diagnostics are checked separately
      Right env
        | not (null selfReaching) ->
            Left (what ++ ": analyse accepted a grammar whose rules "
                    ++ show selfReaching ++ " reach themselves")
        | normalise env == normalise spec -> Right ()
        | otherwise -> Left (unlines
            ([ what ++ ": the analysis and the specification disagree" ]
             ++ [ "  " ++ n ++ ": analysed " ++ show got
                          ++ ", specified " ++ show want
                | (n, got) <- normalise env
                , Just want <- [lookup n (normalise spec)]
                , got /= want ]))
  where
    spec  = specEnv defs
    names = [ n | Def n _ _ <- defs ]
    dups  = [ n | n <- nub names, length (filter (== n) names) > 1 ]
    selfReaching = [ n | (n, Ty _ f) <- spec, n `elem` f ]

    -- Compared as plain pairs: the analysis keeps its sets sorted and the
    -- specification builds them with 'union', so ordering is not the claim.
    normalise :: [(String, Ty)] -> [(String, (Bool, [String]))]
    normalise = sort . map (\(n, Ty nu f) -> (n, (nu, sort (nub f))))

checkFile :: FilePath -> IO [Either String ()]
checkFile path = do
  src <- readFile path
  let blocks = [ (b, False) | b <- extractBlocks "[pegRules|" src ]
                 ++ [ (b, True) | b <- extractBlocks "[pegGrammar|" src ]
  forM (zip [1 :: Int ..] blocks) $ \(i, (block, hasDirectives)) ->
    pure $ do
      body <- if hasDirectives
                then fmap snd (left ("directives: " ++) (parseDirectives block))
                else Right block
      (defs, _) <- left ("parse error: " ++) (parseGrammar body)
      left ((path ++ " (" ++ show i ++ "): ") ++) (checkDefs path defs)
  where
    left f = either (Left . f) Right

--------------------------------------------------------------------------------
-- Generated grammars, to cover the shapes the examples happen not to have
--------------------------------------------------------------------------------

-- | A few hundred small grammars, built deterministically so a failure can be
-- reproduced by index.
--
-- The shapes are chosen to make heads interesting: nullable prefixes, so that
-- a sequence's second item contributes; optionals and stars, which are
-- nullable but keep their operand's heads; and references both forwards and
-- backwards, so that some of these are left-recursive and some are not.
generatedGrammars :: [[Def]]
generatedGrammars = [ grammarFrom seed | seed <- take 400 seeds ]
  where
    seeds = iterate (\x -> (x * 1103515245 + 12345) `mod` 2147483648) 1

grammarFrom :: Int -> [Def]
grammarFrom seed0 = snd (L.foldl' rule (seed0, []) [0 .. n - 1])
  where
    n     = 2 + seed0 `mod` 4
    names = [ "r" ++ show i | i <- [0 .. n - 1] ]

    rule (seed, acc) i =
      let (e, seed') = expr seed 2
      in (seed', acc ++ [Def (names !! i) Nothing e])

    next seed = (seed `div` 65536 `mod` 32768, (seed * 1103515245 + 12345)
                                                 `mod` 2147483648)

    -- A term, at the given remaining depth.  At depth zero only leaves.
    expr seed depth =
      let (k, seed') = next seed
      in case (if depth <= (0 :: Int) then k `mod` 3 else k `mod` 9) of
           0 -> (EChar 'x', seed')
           1 -> (EClass False [('a', 'z')], seed')
           2 -> (ENT (names !! (k `mod` n)), seed')
           3 -> let (e, s') = expr seed' (depth - 1) in (EOpt e, s')
           4 -> let (e, s') = expr seed' (depth - 1) in (EStar e, s')
           5 -> let (e, s') = expr seed' (depth - 1) in (ENot e, s')
           6 -> let (a, s1) = expr seed' (depth - 1)
                    (b, s2) = expr s1 (depth - 1)
                in (EChoice [a, b], s2)
           7 -> let (a, s1) = expr seed' (depth - 1)
                    (b, s2) = expr s1 (depth - 1)
                in (ESeq [Item Nothing a, Item Nothing b] Nothing, s2)
           _ -> let (a, s1) = expr seed' (depth - 1)
                in (ESeq [Item Nothing (EOpt a)
                         , Item Nothing (ENT (names !! (k `mod` n)))]
                         Nothing, s1)

--------------------------------------------------------------------------------
-- Standalone cases: the diagnostics, which no example can exercise because an
-- example that triggered one would not compile.
--------------------------------------------------------------------------------

standaloneChecks :: [(String, Bool)]
standaloneChecks =
  [ ("left recursion is reported with its cycle",
      case run "expr <- e:expr '+' t:term / t:term\nterm <- ds:[0-9]+" of
        Left [LeftRecursive "expr" path] -> path == ["expr", "expr"]
        _                                -> False)
  , ("indirect left recursion reports one cycle, not one per rule",
      case run "a <- x:b\nb <- y:c\nc <- z:a" of
        Left [LeftRecursive n path] -> n `elem` ["a", "b", "c"]
                                         && length path == 4
                                         && take 1 path == take 1 (reverse path)
        _                           -> False)
  , ("a nullable repetition is reported",
      case run "a <- xs:b*\nb <- c:'x'?" of
        Left [NullableStar "a"] -> True
        _                       -> False)
  , ("an undefined non-terminal is reported",
      case run "a <- x:missing" of
        Left [UndefinedNT "missing" ["a"]] -> True
        _                                  -> False)
  , ("a duplicate rule is reported",
      case run "a <- 'x'\na <- 'y'" of
        Left [DuplicateRule "a"] -> True
        _                        -> False)
  , ("a right-recursive grammar is accepted",
      case run "a <- 'x' r:a / 'y'" of
        Right env -> lookup "a" env == Just (Ty False [])
        _         -> False)
  , ("a class repetition is a Span, not a Star",
      case run "a <- xs:[a-z]*" of
        Right env -> lookup "a" env == Just (Ty True [])
        _         -> False)
  , ("a nullable head propagates the next item's FIRST set",
      case run "a <- w:ws n:b\nws <- [ ]*\nb <- 'x'" of
        Right env -> lookup "a" env == Just (Ty False ["b", "ws"])
        _         -> False)
  , ("the reported cycle names every rule on it",
      case run "a <- x:b\nb <- y:c\nc <- z:a" of
        Left [LeftRecursive _ path] -> sort (nub path) == ["a", "b", "c"]
        _                           -> False)
  , ("renderDiagnostic says which rule",
      case run "expr <- e:expr '+' t:term / t:term\nterm <- ds:[0-9]+" of
        Left [d] -> "expr" `isInfix` renderDiagnostic d
        _        -> False)
  ]
  where
    run src = case parseGrammar src of
      Left err        -> Left [UndefinedNT ("parse error: " ++ err) []]
      Right (defs, _) -> analyse defs
    isInfix needle hay = any (needle `isPrefixOf`) (suffixes hay)
    suffixes xs = xs : case xs of { [] -> []; (_:r) -> suffixes r }

--------------------------------------------------------------------------------
-- 'ntw': a reference that carries its own membership proof
--------------------------------------------------------------------------------

-- The environment's order is the rule chain's order, which is what makes
-- @There Here@ name @digits@.  A witness that named the wrong rule would not
-- compile: 'NTW' keeps the @Lookup@ equality that ties the two together.
type NtwEnv =
  '[ '("pair"  , 'EnvEntry (Int, Int))
   , '("digits", 'EnvEntry Int)
   ]

digitsCount :: PExp String (InEnv NtwEnv) Int
digitsCount = fmapP (length . chunkToString) (spanOf1 (fromRanges [('0', '9')]))

ntwGrammar :: Grammar String (InEnv NtwEnv) (Int, Int)
ntwGrammar =
  Grammar
    (RCons (Name @"pair")
           ((,) <$>. ntw @"digits" (There Here)
                <*>. (Term ',' .>>. ntw @"digits" (There Here)))
       (RCons (Name @"digits") digitsCount RNil))
    (ntw @"pair" Here)

--------------------------------------------------------------------------------
-- What pegGrammar generates
--------------------------------------------------------------------------------

[pegGrammar|
  %name  tiny
  %env   TinyEnv
  %start pair

  pair   :: (Int, Int) <- a:digits ',' b:digits
  digits :: Int        <- ds:[0-9]+ { length (chunkToString ds) }
|]

-- The key type a reader would have written for that grammar: one constructor
-- per rule, named after the rule, at the rule's declared type.  GHC checks
-- these signatures against the generated declarations, so what this pins down
-- is that the generated key type is also the /expected/ one — same rules,
-- same spelling, same types — and so are the per-rule bindings.
expectedKeys :: (TinyEnv String (Int, Int), TinyEnv String Int)
expectedKeys = (TinyEnv_pair, TinyEnv_digits)

expectedBindings :: ( PExp String (TinyEnv String) (Int, Int)
                    , PExp String (TinyEnv String) Int )
expectedBindings = (tiny'pair, tiny'digits)

-- A grammar over a fixed stream, with a parameter, whose result types mention
-- the stream as @s@: the one place a result type has to be rewritten, since
-- the stream is no longer a variable.
[pegGrammar|
  %name   scaled
  %stream String
  %param  factor :: Int
  %start  num

  num    :: Int <- ds:digits { factor * length ds }
  digits :: s   <- ds:[0-9]+
|]

generatedChecks :: [(String, Bool)]
generatedChecks =
  [ ("pegGrammar generates the expected keys",
      case expectedKeys of
        (p, d) -> ruleName p == "pair" && ruleName d == "digits")
  , ("pegGrammar generates the expected rule bindings",
      case expectedBindings of (_, _) -> True)
  , ("a generated key table agrees with the function it tabulates",
      [ getConst (lookupTable table TinyEnv_pair)
      , getConst (lookupTable table TinyEnv_digits) ] == ["pair", "digits"])
  , ("a generated grammar parses",
      case parse tiny "12,345" of
        OK r _ rest -> r == (2, 3) && rest == ""
        Fail        -> False)
  , ("%param and %stream: a result type of s becomes the stream",
      case parse (scaled 10) "123" of
        OK r _ rest -> r == 30 && rest == ""
        Fail        -> False)
  ]
  where
    table :: Table (TinyEnv String) (Const String)
    table = tabulate (\k -> Const (ruleName k))

--------------------------------------------------------------------------------
-- Factoring shared prefixes out of an ordered choice
--------------------------------------------------------------------------------

-- The translation turns @A B / A C@ into @A (B / C)@.  What can go wrong is
-- which alternative wins and what its action sees, so this grammar has:
--
-- * a group of alternatives sharing one item, under a different label in
--   each, whose remainders share two more items and are factored again;
-- * an alternative that is all prefix, so that its remainder is empty;
-- * two alternatives with the same prefix that are /not/ consecutive, which
--   must not be grouped, since the one between them has to be tried first;
-- * two identical alternatives, of which the first must win;
-- * unlabelled prefixes and sequences with no action, whose value is their
--   labels.
[pegGrammar|
  %name   shared
  %stream String
  %start  top

  top   :: [String] <- ss:(s:stmt ';')* !.

  stmt  :: String   <-
      'x' "yz"                       { "xyz" }
    / n:ident "+=" v:num             { n ++ " add " ++ v }
    / m:ident "-=" w:num             { m ++ " sub " ++ w }
    / p:ident ':' q:ident '=' r:num  { p ++ ":" ++ q ++ " set " ++ r }
    / p2:ident ':' q2:ident          { p2 ++ ":" ++ q2 }
    / k:ident '=' u:num              { k ++ " set " ++ u }
    / j:ident                        { "bare " ++ j }
    / 'x' 'q'                        { "unreachable" }
    / '#' t:tag                      { t }
    / '@'                            { "first" }
    / '@'                            { "second" }

  tag   :: String   <- '<' a:ident '>' / '<' b:num

  ident :: s        <- cs:[a-z]+
  num   :: s        <- ds:[0-9]+
|]

factoringChecks :: [(String, Bool)]
factoringChecks =
  [ ("factoring keeps which alternative wins and what its action sees",
      parse shared "a+=1;b-=2;c:d=3;e:f;g=4;h;xyz;xq;#<i>;#<5;@;"
        `okWith` [ "a add 1", "b sub 2", "c:d set 3", "e:f", "g set 4"
                 , "bare h", "xyz", "bare xq", "i", "5", "first" ])
  , ("factoring keeps a failure a failure",
      case parse shared "a+=;" of
        Fail -> True
        _    -> False)
  ]
  where
    okWith (OK r _ rest) want = r == want && rest == ""
    okWith Fail          _    = False

-- Every level of this grammar would parse its operand twice without
-- factoring — once by the alternative that fails at '+', once by the one
-- that succeeds — so forty nested parentheses would take 2^40 steps.  With
-- it they take forty.  The time limit turns a regression into a failure
-- instead of a hang.
[pegGrammar|
  %name   nest
  %stream String
  %start  e

  e    :: Int <- a:atom '+' b:e { a + b } / a:atom { a }
  atom :: Int <- '(' x:e ')' { x } / ds:[0-9]+ { length ds }
|]

nestingCheck :: IO (String, Bool)
nestingCheck = do
  let depth = 40 :: Int
      input = replicate depth '(' ++ "1+22" ++ replicate depth ')'
  r <- timeout 5000000 (evaluate (case parse nest input of
                                    OK n _ rest -> n == 3 && rest == ""
                                    Fail        -> False))
  pure ("a shared prefix is parsed once, not once per alternative",
        r == Just True)

witnessCheck :: (String, Bool)
witnessCheck =
  ( "ntw parses through the witness it was given"
  , case parse ntwGrammar "12,345" of
      OK r _ rest -> r == (2, 3) && rest == ""
      Fail        -> False )

--------------------------------------------------------------------------------
-- Extracting the grammars from an example's source
--------------------------------------------------------------------------------

-- | Every @[pegRules| ... |]@ (or @[pegGrammar| ... |]@) block, in order of
-- appearance.
extractBlocks :: String -> String -> [String]
extractBlocks open = go
  where
    go s = case breakOn open s of
      Nothing   -> []
      Just rest -> let (body, after) = breakClose rest in body : go after
    breakClose s = case breakOn "|]" s of
      Nothing   -> (s, "")
      Just rest -> (take (length s - length rest - 2) s, rest)

-- | The input just past the first occurrence of the needle, if any.
breakOn :: String -> String -> Maybe String
breakOn needle = go
  where
    go [] = Nothing
    go s@(_:cs)
      | needle `isPrefixOf` s = Just (drop (length needle) s)
      | otherwise             = go cs
