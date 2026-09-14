-- | Generator for the compile-time benchmark.
--
-- @runghc bench-compile/Gen.hs MODE N@ writes a module to stdout.  The point
-- of the benchmark is that a grammar's cost is paid by GHC, once per
-- compilation of every module that mentions it, so the thing being measured
-- is @ghc -fno-code@ on the generated module.
--
-- The shape is the same in every mode: @N@ rules, rule @i@ referencing rules
-- @i+1@ and @i+2@, so there are @2N@ non-terminal occurrences and the
-- environment has @N@ entries.
--
-- Most of the modes exist to take apart a cost that is now gone: entries of
-- the environment used to carry the rule's FIRST set, which made the
-- environment quadratic in the number of rules and dominated everything.
-- What is left measures that it stayed gone, and what the remaining lever —
-- how a reference is resolved — is worth.
--
-- [@dense@]  The environment is written out by hand.  Rule @i@ begins with a
--            non-terminal, so this is the shape whose FIRST sets used to be
--            every rule after @i@: a precedence ladder, the worst case there
--            was.
--
-- [@sparse@] The same @N@ rules and the same @2N@ occurrences, but every rule
--            starts with a terminal, so nothing can be at the head of
--            anything.  @dense@ against @sparse@ used to be 4.9x; the two now
--            differ only by an extra 'Term' per alternative, and their being
--            equal is the result.
--
-- [@witness@, @witness-sparse@] The same grammars with every reference built
--            from 'PEG.Syntax.ntw' and the proof a splice would have written,
--            instead of 'PEG.Syntax.nt' and a @KnownMember@ search.
--
-- [@qq-grammar@, @qq-grammar-sparse@] The same grammars written the way the
--            library recommends, through 'PEG.QQ.pegGrammar' in declaration
--            position, which declares a key type with one constructor per
--            rule.  A reference is a constructor, so nothing is searched and
--            no proof is built.
--
-- [@qq-grammar-expr@] The same grammar through 'PEG.QQ.pegGrammar' in
--            /expression/ position, which cannot declare a key type and
--            builds the environment and a membership proof per reference
--            instead — which is what declaration position also did before
--            the key types.  Against @qq-grammar@ it measures the keys.
--
-- [@minipython@] Not generated: @examples/MiniPython.hs@, a real grammar of
--            27 rules, copied as it is.  @N@ is ignored.
--
-- [@wild@]   As @dense@, but the environment is left to GHC as a wildcard.
--            This used to exhaust tens of gigabytes at @N = 16@, because the
--            entries GHC inferred were unreduced type-family applications
--            over FIRST sets.  There are no type families left for it to
--            leave unreduced.
--
-- [@lookup-*@] A self-contained module, not importing the library, holding an
--            @N@-entry environment and @2N@ references to it.  The trio
--            @lookup-class@ / @lookup-witness-eq@ / @lookup-witness@ measures
--            what the @KnownMember@ search costs against being handed the
--            witness.  @lookup-big@ gives each entry a payload that nothing
--            ever reads, and is the reason entries have to stay small: it is
--            15x at @N = 64@ and does not fit in 8 GB at @N = 96@.
--            @lookup-key@ is the same @2N@ references to a declared key type
--            instead of an environment: what the library's keys cost with
--            nothing else in the way.
--
module Main (main) where

import Data.List        (intercalate, sort)
import System.Environment (getArgs)

main :: IO ()
main = do
  args <- getArgs
  case args of
    [mode, ns] | [(n, "")] <- reads ns -> putStrLn (gen mode n)
    _ -> putStrLn "usage: runghc bench-compile/Gen.hs MODE N\n\
                  \  MODE = dense | sparse | witness | witness-sparse\n\
                  \         | qq-grammar | qq-grammar-sparse | qq-grammar-expr\n\
                  \         | wild | lookup-key\n\
                  \         | lookup-class | lookup-witness | lookup-witness-eq\n\
                  \         | lookup-nameenv | lookup-big | lookup-big-nameenv"

startName :: Int -> String
startName n = case names n of
  (x:_) -> x
  []    -> error "startName: empty grammar"

names :: Int -> [String]
names n = [ "r" ++ pad i | i <- [1 .. n] ]
  where pad i = let s = show i in replicate (width - length s) '0' ++ s
        width = length (show n)

gen :: String -> Int -> String
gen "dense"          n = grammarModule n True
gen "sparse"         n = grammarModule n False
gen "wild"           n = wildModule n
gen "witness"        n = witnessModule n True
gen "witness-sparse" n = witnessModule n False
gen "qq-grammar"     n = qqGrammarModule n True
gen "qq-grammar-sparse" n = qqGrammarModule n False
gen "qq-grammar-expr" n = qqGrammarExprModule n
gen "lookup-key"     n = keyModule n
gen "lookup-class"   n = lookupModule n Class     Small NoEnv
gen "lookup-witness" n = lookupModule n Witness   Small NoEnv
gen "lookup-witness-eq" n = lookupModule n WitnessEq Small NoEnv
gen "lookup-nameenv" n = lookupModule n WitnessEq Small NameEnv
gen "lookup-big"     n = lookupModule n WitnessEq Big   NoEnv
gen "lookup-big-nameenv" n = lookupModule n WitnessEq Big NameEnv
gen m                _ = error ("unknown mode: " ++ m)

--------------------------------------------------------------------------------
-- Modes that go through the library
--------------------------------------------------------------------------------

-- | @dense@ and @sparse@ differ only in whether a terminal precedes the first
-- non-terminal of each rule, which is what decides whether FIRST sets grow.
rules :: Int -> Bool -> [String]
rules n dense =
  [ "       " ++ nm ++ " <- " ++ b | (nm, b) <- zip (names n) (bodies n dense) ]

-- | Just the right-hand sides, which the @literal-ty@ mode splices one at a
-- time with 'PEG.QQ.pegExpr'.
bodies :: Int -> Bool -> [String]
bodies n dense = map body [0 .. n - 1]
  where
    ns = names n
    lead = if dense then "" else "'x' "
    body i
      | i < n - 2 = lead ++ "a:" ++ ns !! (i+1) ++ " / "
                      ++ (if dense then "" else "'y' ") ++ "b:" ++ ns !! (i+2)
      | i == n - 2 = lead ++ "a:" ++ ns !! (i+1)
      | otherwise  = "ds:[0-9]+ { 1 :: Int }"

-- | The environment.  It no longer depends on the grammar's shape at all: an
-- entry is a name and a result type, so @dense@ and @sparse@ now write the
-- same one.  That it does not grow with the grammar beyond one entry per rule
-- is the whole of the change this directory measures.
envType :: Int -> String
envType n = "type GEnv =\n  '[ " ++ intercalate "\n   , " entries ++ "\n   ]"
  where
    entries = [ "'(" ++ show nm ++ ", 'EnvEntry Int)" | nm <- names n ]

grammarModule :: Int -> Bool -> String
grammarModule n dense = unlines
  [ header
  , envType n
  , ""
  , "g :: Grammar String (InEnv GEnv) Int"
  , "g = Grammar"
  , "  [pegRules|"
  , unlines (rules n dense) ++ "  |]"
  , "  (nt @" ++ show (startName n) ++ ")"
  ]

wildModule :: Int -> String
wildModule n = unlines
  [ header
  , "g :: Grammar String _ Int"
  , "g = Grammar"
  , "  [pegRules|"
  , unlines (rules n True) ++ "  |]"
  , "  (nt @" ++ show (startName n) ++ ")"
  ]

-- | @dense@, but every non-terminal reference is built with 'PEG.Syntax.ntw'
-- and the witness a splice would have written, instead of 'PEG.Syntax.nt'.
-- Everything else — the rules, the environment, the FIRST sets, the indices
-- GHC computes for each body — is the same, so the difference from @dense@ is
-- the @KnownMember@ search and nothing else.
witnessModule :: Int -> Bool -> String
witnessModule n dense = unlines
  [ "{-# LANGUAGE DataKinds, TypeApplications, TypeOperators,"
  , "             ScopedTypeVariables #-}"
  , "module Big where"
  , "import PEG"
  , ""
  , envType n
  , ""
  , "rules :: Rules String GEnv GEnv"
  , "rules =" ++ chain
  , ""
  , "g :: Grammar String (InEnv GEnv) Int"
  , "g = Grammar rules (ntw @" ++ show (startName n) ++ " Here)"
  ]
  where
    ns = names n
    chain = foldr step "\n  RNil" (zip [0 ..] ns)
    step (i, nm) rest =
      "\n  RCons (Name @" ++ show nm ++ ") (" ++ body i ++ ") ("  ++ rest ++ ")"
    -- The bodies the quasi-quoter would emit for 'bodies', written out: a
    -- labelled item becomes 'fmapP' over the item, and '/' becomes '.||.'.
    -- When sparse, each alternative is preceded by the same terminal that
    -- 'bodies' puts there.
    body i
      | i < n - 2  = lead 'x' (alt (i+1)) ++ " .||. " ++ lead 'y' (alt (i+2))
      | i == n - 2 = lead 'x' (alt (i+1))
      | otherwise  = "fmapP (\\_ -> 1 :: Int) (spanOf1 (fromRanges [('0','9')]))"
    lead c e | dense     = e
             | otherwise = "(Term '" ++ [c] ++ "' .>>. " ++ e ++ ")"
    alt k = "fmapP id (ntw @" ++ show (ns !! k) ++ " (" ++ witnessAt k ++ "))"
    witnessAt k = concat (replicate k "There (") ++ "Here" ++ replicate k ')'

-- | The same grammar through 'PEG.QQ.pegGrammar': the environment is
-- generated rather than written out, and every reference carries its own
-- proof.  This is the user-facing counterpart of @witness@ — what a grammar
-- costs once it is written the way the library now recommends.
qqGrammarModule :: Int -> Bool -> String
qqGrammarModule n dense = unlines
  ([ "{-# LANGUAGE DataKinds, GADTs, QuasiQuotes, TemplateHaskell,"
   , "             TypeApplications, TypeOperators #-}"
   , "module Big where"
   , "import PEG"
   , "import PEG.QQ (pegGrammar)"
   , ""
   , "[pegGrammar|"
   , "  %name  g"
   , "  %start " ++ startName n
   , ""
   ] ++ [ "  " ++ nm ++ " :: Int <- " ++ b
        | (nm, b) <- zip (names n) (bodies n dense) ]
     ++ [ "|]" ])

-- | The same grammar through 'PEG.QQ.pegGrammar' in expression position,
-- where there is no key type: the environment is inferred from the rules and
-- every reference carries a membership proof into it.
qqGrammarExprModule :: Int -> String
qqGrammarExprModule n = unlines
  ([ "{-# LANGUAGE DataKinds, QuasiQuotes, TemplateHaskell, TypeApplications,"
   , "             TypeOperators, PartialTypeSignatures #-}"
   , "{-# OPTIONS_GHC -Wno-partial-type-signatures #-}"
   , "module Big where"
   , "import PEG"
   , "import PEG.QQ (pegGrammar)"
   , ""
   , "g :: Grammar String _ Int"
   , "g = [pegGrammar|"
   , "  %start " ++ startName n
   , ""
   ] ++ [ "  " ++ nm ++ " <- " ++ b
        | (nm, b) <- zip (names n) (bodies n True) ]
     ++ [ "  |]" ])

header :: String
header = unlines
  [ "{-# LANGUAGE DataKinds, QuasiQuotes, TypeApplications, TypeOperators,"
  , "             PartialTypeSignatures #-}"
  , "{-# OPTIONS_GHC -Wno-partial-type-signatures #-}"
  , "module Big where"
  , "import PEG"
  , "import PEG.QQ (pegRules)"
  ]
-- The partial signature is only for @wild@, which leaves the environment to
-- be inferred; every other mode writes it out.

--------------------------------------------------------------------------------
-- The lookup micro-benchmark
--------------------------------------------------------------------------------

-- | @2N@ references to a declared key type, with no library: the cost the
-- other @lookup-*@ modes are compared against.  The references have the same
-- shape as @lookup-witness@'s — rule @i@ is used twice — and each is checked
-- against the key's own type, which does not grow with @N@.
keyModule :: Int -> String
keyModule n = unlines $
  [ "{-# LANGUAGE GADTs, KindSignatures #-}"
  , "module Lk where"
  , "import Data.Kind (Type)"
  , ""
  , "data Ref (nt :: Type -> Type) (a :: Type) where"
  , "  Ref :: nt a -> Ref nt a"
  , ""
  , "data GKey (a :: Type) where"
  ] ++ [ "  K_" ++ nm ++ " :: GKey Int" | nm <- ns ] ++
  [ "" ] ++
  [ "u" ++ show i ++ ", v" ++ show i ++ " :: Ref GKey Int\n"
      ++ "u" ++ show i ++ " = Ref K_" ++ nm ++ "\n"
      ++ "v" ++ show i ++ " = Ref K_" ++ nm
  | (i, nm) <- zip [1 :: Int ..] ns ]
  where
    ns = names n

-- | Only the environment search, with the library's definitions inlined so
-- the module stands alone.  'Resolve' selects how a reference is resolved:
-- as 'PEG.Syntax.NT' does today, from a generated witness alone, or from a
-- generated witness while keeping the @Lookup@ equality that says which rule
-- the witness is for.
data Resolve = Class | Witness | WitnessEq

-- | How much each entry of the environment carries.
--
-- @Small@ is a result type and nothing else.  @Big@ adds an @N@-symbol list,
-- which is the shape of a real entry: a 'PEG.Type.Ty' whose FIRST set has
-- grown to most of the grammar.  The list is never read — it is there to make
-- the environment @O(N^2)@ type nodes instead of @O(N)@, so that what the
-- pair measures is the size of what a lookup walks over and nothing else.
data Payload = Small | Big deriving Eq

-- | Whether the family that reports a failed lookup names the environment.
--
-- The library's 'PEG.TyLevel.Lookup' does, so that "undefined non-terminal"
-- can list the ones that are defined.  It only reduces once the search has
-- finished, but until then every one of the @2N@ pending applications holds a
-- copy of the environment.  @NoEnv@ drops that argument and the message with
-- it.
data FoundStyle = NoEnv | NameEnv deriving Eq

lookupModule :: Int -> Resolve -> Payload -> FoundStyle -> String
lookupModule n how payload found = unlines
  [ "{-# LANGUAGE DataKinds, TypeApplications, TypeFamilies, TypeOperators, GADTs,"
  , "             KindSignatures, ScopedTypeVariables, AllowAmbiguousTypes,"
  , "             FlexibleContexts, FlexibleInstances, MultiParamTypeClasses,"
  , "             UndecidableInstances, RankNTypes #-}"
  , "module Lk where"
  , "import Data.Kind (Type)"
  , "import Data.Proxy (Proxy(..))"
  , "import GHC.TypeLits"
  , ""
  , "data EnvEntry = EnvEntry " ++ (if big then "[Symbol] Type" else "Type")
  , "type Env = [(Symbol, EnvEntry)]"
  , ""
  , "type family Names (env :: Env) :: [Symbol] where"
  , "  Names '[] = '[]"
  , "  Names ('(s, _) ': rest) = s ': Names rest"
  , ""
  , "type family Lookup (s :: Symbol) (env :: Env) :: EnvEntry where"
  , "  Lookup s env = Found s " ++ (if nameEnv then "env " else "") ++ "(LookupMb s env)"
  , "type family LookupMb (s :: Symbol) (env :: Env) :: Maybe EnvEntry where"
  , "  LookupMb _ '[] = 'Nothing"
  , "  LookupMb s ('(s, e) ': rest) = 'Just e"
  , "  LookupMb s (_ ': rest) = LookupMb s rest"
  , "type family Found (s :: Symbol) " ++ (if nameEnv then "(env :: Env) " else "")
      ++ "(r :: Maybe EnvEntry) :: EnvEntry where"
  , "  Found _ " ++ (if nameEnv then "_ " else "") ++ "('Just e) = e"
  , "  Found s " ++ (if nameEnv then "env " else "") ++ "'Nothing = TypeError"
  , "    ('Text \"Undefined: \" ':<>: 'ShowType s"
      ++ (if nameEnv then " ':$$: 'ShowType (Names env))" else ")")
  , ""
  , "data Member (s :: Symbol) (env :: Env) (a :: Type) where"
  , "  Here  :: Member s ('(s, " ++ entryPat ++ ") ': rest) a"
  , "  There :: Member s rest a -> Member s (e ': rest) a"
  , ""
  , "class KnownMember (s :: Symbol) (env :: Env) (a :: Type) where"
  , "  member :: Member s env a"
  , "instance KnownMemberStep (CmpSymbol s t) s ('(t, e) ': rest) a"
  , "      => KnownMember s ('(t, e) ': rest) a where"
  , "  member = memberStep (Proxy :: Proxy (CmpSymbol s t))"
  , "class KnownMemberStep (o :: Ordering) (s :: Symbol) (env :: Env) (a :: Type) where"
  , "  memberStep :: Proxy o -> Member s env a"
  , "instance (s ~ t) => KnownMemberStep 'EQ s ('(t, " ++ entryPat
      ++ ") ': rest) a where"
  , "  memberStep _ = Here"
  , "instance KnownMember s rest a => KnownMemberStep 'LT s ('(t, e) ': rest) a where"
  , "  memberStep _ = There member"
  , "instance KnownMember s rest a => KnownMemberStep 'GT s ('(t, e) ': rest) a where"
  , "  memberStep _ = There member"
  , ""
  , "-- how PEG.Syntax.nt resolves a non-terminal today"
  , "use :: forall n env " ++ payloadV ++ "a. (KnownSymbol n, Lookup n env ~ "
      ++ entryPat ++ ", KnownMember n env a)"
  , "    => Member n env a"
  , "use = member @n @env"
  , ""
  , "-- how a generated reference would resolve it"
  , "useW :: forall env n a. Member n env a -> Member n env a"
  , "useW m = m"
  , ""
  , "-- a witness, but the equality that names the entry is kept: this is what"
  , "-- a constructor can demand and still be sound about which rule it means"
  , "useE :: forall n env " ++ payloadV ++ "a. (KnownSymbol n, Lookup n env ~ "
      ++ entryPat ++ ")"
  , "     => Member n env a -> Member n env a"
  , "useE m = m"
  , ""
  , "type GEnv = '[ " ++ intercalate ", "
      [ "'(" ++ show nm ++ ", 'EnvEntry " ++ entryVal ++ ")" | nm <- ns ] ++ " ]"
  , ""
  , unlines (zipWith use1 [1 :: Int ..] ns)
  , unlines (zipWith use2 [1 :: Int ..] ns)
  ]
  where
    big      = payload == Big
    nameEnv  = found == NameEnv
    ns       = names n
    entryPat = if big then "'EnvEntry hs a" else "'EnvEntry a"
    payloadV = if big then "hs " else ""
    -- The filler: every entry carries the whole set of names, which is the
    -- size a FIRST set reaches on the precedence ladder the other modes use.
    entryVal = (if big
                  then "'[" ++ intercalate ", " (map show ns) ++ "] "
                  else "") ++ "Int"
    use1 i nm = "u" ++ show i ++ " = " ++ reference (i - 1) nm
    use2 i nm = "v" ++ show i ++ " = " ++ reference (i - 1) nm
    reference k nm = case how of
      Class     -> "use @" ++ show nm ++ " @GEnv"
      Witness   -> "useW @GEnv (" ++ witness k ++ ")"
      WitnessEq -> "useE @" ++ show nm ++ " @GEnv (" ++ witness k ++ ")"
    witness k = concat (replicate k "There (") ++ "Here" ++ replicate k ')'
