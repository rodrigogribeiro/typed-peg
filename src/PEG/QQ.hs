{-# LANGUAGE TemplateHaskell #-}

-- | Quasi-quoters for writing PEG grammars in a concrete DSL.
--
-- == Grammar syntax
--
-- @
-- [pegRules|
--   ruleName <- body
--   ...
-- |]
-- @
--
-- Each rule binds named sub-expressions with @name:subexpr@ and applies
-- a Haskell action in braces: @{ haskellExpr }@.
-- Ordered choice is written with @\/@; Kleene star with @*@; plus with @+@;
-- optional with @?@; negation with @!@.
--
-- Character classes use @[...]@ syntax and may contain ranges: @[a-zA-Z0-9_]@.
-- A leading @^@ negates the class, so @[^\"]@ matches any character other than
-- a double quote; write @[\\^]@ for a class containing a caret.  Prefer a
-- negated class over the @(!c .)@ idiom: the class is one bit test, whereas
-- the lookahead scans every character twice.
--
-- The 'pegExpr' quasi-quoter produces a single 'PEG.Syntax.PExp' value,
-- while 'pegRules' produces a complete set of named rules (a
-- 'PEG.Grammar.Rules' value) to be passed to 'PEG.Grammar.Grammar'.
module PEG.QQ
  ( pegExpr
  , pegRules
  , pegGrammar
  ) where

import Control.Monad              (foldM)
import Data.List                  (elemIndex, nub)
import Language.Haskell.TH        (Exp (..), Pat (..), Q)
import qualified Language.Haskell.TH      as TH
import Language.Haskell.TH.Quote  (QuasiQuoter (..))

import PEG
import PEG.Analysis  (Diagnostic (..), World (..), analyse, analyseWith,
                      renderDiagnostic, spannable)
import PEG.QQ.HsExp  (parseHsExp, parseHsType)
import PEG.QQ.Syntax (Def (..), Directive (..), Item (..), PExpr (..),
                      RelS (..), parseDirectives, parseExpr, parseGrammar,
                      spaces)

-- | Translate a DSL expression, given a way to emit a reference to a
-- non-terminal.
--
-- The two quasi-quoters differ in exactly that: 'pegRules' emits
-- @nt \@"name"@, which makes GHC search the environment, while 'pegGrammar'
-- knows every rule's position and emits @ntw \@"name" witness@, which does
-- not.  Everything else about the translation is shared, so the two cannot
-- drift.
translateExprWith :: (String -> Q Exp) -> PExpr -> Q Exp
translateExprWith ntRef = go
  where
    go (EChar c) =
      [| Term c |]
    go EDot =
      [| AnyChar |]
    go (ENT name) = ntRef name
    go (EString str)
      | null str  = [| pureP "" |]
      | otherwise = [| stringNE str |]
    go (EClass neg rs)
      -- A character class becomes a single 'Sat' node holding a compact
      -- 'PEG.CharSet.CharSet'.  Expanding it into a chain of ordered choices, as
      -- an earlier version did, made matching one character of @[a-zA-Z0-9_]@
      -- cost 63 parser steps.
      | neg       = [| notCharClass rs |]
      | otherwise = [| charClass rs |]
    go (EAnd e)  = do
      e' <- go e
      [| Not (Not $(pure e')) |]
    go (ENot e)  = do
      e' <- go e
      [| Not $(pure e') |]
    go (EOpt e)  = do
      e' <- go e
      [| opt $(pure e') |]
    -- A repetition of a single character -- @[a-z]*@, @','+@, @.*@ -- compiles to
    -- one 'PEG.Syntax.Span' node and produces a /chunk of the input stream/: a
    -- 'Data.Text.Text' slice rather than a @['Char']@.  Only a bare class, literal
    -- or dot qualifies; a wrapper such as @[a-z]^>*@ changes the meaning of each
    -- iteration, so those keep the generic 'Star'.
    go (EStar (EClass neg rs))
      | neg       = [| spanOf (notInRanges rs) |]
      | otherwise = [| spanOf (fromRanges rs) |]
    go (EStar (EChar c)) = [| spanOf (singletonCS c) |]
    go (EStar EDot)      = [| spanOf anyCS |]
    go (EPlus (EClass neg rs))
      | neg       = [| spanOf1 (notInRanges rs) |]
      | otherwise = [| spanOf1 (fromRanges rs) |]
    go (EPlus (EChar c)) = [| spanOf1 (singletonCS c) |]
    go (EPlus EDot)      = [| spanOf1 anyCS |]
    go (EStar e) = do
      e' <- go e
      [| Star $(pure e') |]
    go (EPlus e) = do
      e' <- go e
      [| plus $(pure e') |]
    go (EIndent r e) = do
      e' <- go e
      [| Indent $(translateRel r) $(pure e') |]
    go (EPos r e) = do
      e' <- go e
      [| Position $(translateRel r) $(pure e') |]
    go (EAlign e) = do
      e' <- go e
      [| Align $(pure e') |]
    go (EChoice es) = case es of
      []       -> fail "QQ: empty choice (should be impossible)"
      (e:rest) -> do
        e'    <- go e
        rest' <- mapM go rest
        foldM (\acc x -> [| $(pure acc) .||. $(pure x) |]) e' rest'
    go (ESeq items act) = translateSeqWith ntRef items act

-- | Emit @nt \@"name"@: the environment is searched by the type checker.
ntByName :: String -> Q Exp
ntByName name = pure (TH.AppTypeE (TH.VarE 'nt) (TH.LitT (TH.StrTyLit name)))

translateRel :: RelS -> Q Exp
translateRel RGt          = [| gtR |]
translateRel RGe          = [| geR |]
translateRel REq          = [| eqR |]
translateRel RAny         = [| anyR |]
translateRel (ROffset n)  = [| offsetR n |]
translateRel (RNamed nm)  = pure (TH.VarE (TH.mkName nm))

translateSeqWith :: (String -> Q Exp) -> [Item] -> Maybe String -> Q Exp
translateSeqWith ntRef items act = do
  let labels = [ l | Item (Just l) _ <- items ]
  case duplicates labels of
    (l:_) -> fail ("QQ: the label " ++ show l
                     ++ " is used twice in the same sequence")
    []    -> pure ()
  body <- case act of
    Nothing  -> pure (defaultBody labels)
    Just src -> case parseHsExp src of
      Right e  -> pure e
      Left err -> fail ("QQ: in the semantic action {" ++ src ++ "}: " ++ err)
  es <- mapM (\(Item _ e) -> translateExprWith ntRef e) items
  case es of
    []       -> [| pureP $(pure body) |]
    (e:rest) -> do
      let pats = zipWith itemPat [1 :: Int ..] items
      hd <- [| fmapP $(pure (LamE pats body)) $(pure e) |]
      foldM (\acc x -> [| $(pure acc) <*>. $(pure x) |]) hd rest
  where
    itemPat i (Item ml _) =
      VarP (TH.mkName (maybe ('_' : show i) id ml))

    defaultBody []  = TH.ConE '()
    defaultBody [l] = TH.VarE (TH.mkName l)
    defaultBody ls  = TH.TupE (map (Just . TH.VarE . TH.mkName) ls)

    duplicates xs = [ x | x <- nub xs, length (filter (== x) xs) > 1 ]

translateRules :: (String -> Q Exp) -> [Def] -> Q Exp
translateRules _ [] = [| RNil |]
translateRules ntRef (Def name _ expr : rest) = do
  body  <- translateExprWith ntRef expr
  rest' <- translateRules ntRef rest
  let nameProxy = TH.AppTypeE (TH.ConE 'Name) (TH.LitT (TH.StrTyLit name))
  [| RCons $(pure nameProxy) $(pure body) $(pure rest') |]

-- | Quasi-quoter for a single PEG expression.
--
-- @[pegExpr| body |]@ produces a 'PEG.Syntax.PExp' value.
-- Useful for one-off expressions that do not need a named rule set.
pegExpr :: QuasiQuoter
pegExpr = QuasiQuoter
  { quoteExp  = pegExprExp
  , quotePat  = \_ -> fail "pegExpr: cannot be used as a pattern"
  , quoteType = \_ -> fail "pegExpr: cannot be used as a type"
  , quoteDec  = \_ -> fail "pegExpr: cannot be used as a top-level declaration"
  }

pegExprExp :: String -> Q Exp
pegExprExp src = case parseExpr src of
  Left err     -> fail ("pegExpr: parse error: " ++ err)
  Right (e, rest) -> case spaces rest of
    []  -> translateExprWith ntByName e
    leftover -> fail ("pegExpr: unconsumed input: " ++ show (take 30 leftover))

-- | Quasi-quoter for a set of named PEG rules.
--
-- @[pegRules| rule1 <- body1; rule2 <- body2 |]@ produces a
-- 'PEG.Grammar.Rules' value to be passed to 'PEG.Grammar.Grammar'.
--
-- Example:
--
-- @
-- grammar :: Grammar MyEnv _ MyResult
-- grammar = Grammar
--   [pegRules|
--     expr <- t:term ts:(op:[+-] u:term)* { foldl addOp t ts }
--     term <- n:number                     { n }
--     number <- ds:[0-9]+                  { read ds }
--   |]
--   (nt @\"expr\")
-- @
pegRules :: QuasiQuoter
pegRules = QuasiQuoter
  { quoteExp  = pegRulesExp
  , quotePat  = \_ -> fail "pegRules: cannot be used as a pattern"
  , quoteType = \_ -> fail "pegRules: cannot be used as a type"
  , quoteDec  = \_ -> fail "pegRules: cannot be used as a top-level declaration"
  }

pegRulesExp :: String -> Q Exp
pegRulesExp src = case parseGrammar src of
  Left err -> fail ("pegRules: parse error: " ++ err)
  Right (defs, _) ->
    -- Left recursion, a nullable repetition and a duplicate rule, reported
    -- here because nothing else reports them any more: the FIRST sets that
    -- @Acyclic@ used to check are no longer in the types.  The block is
    -- analysed 'Open' because it may be only part of a rule set — see
    -- 'PEG.Analysis.World' — so a cycle that closes across two blocks is
    -- caught by neither this nor GHC.  'pegGrammar' has no such gap.
    case analyseWith Open defs of
      Left ds -> fail ("pegRules:\n" ++ unlines
                         -- six spaces, so the body lines up under the bullet
                         -- GHC puts in front of the first line
                         [ "      " ++ l | d <- ds, l <- lines (renderDiagnostic d) ])
      Right _ -> translateRules ntByName defs

--------------------------------------------------------------------------------
-- pegGrammar: a whole grammar, environment included
--------------------------------------------------------------------------------

-- | Quasi-quoter for a complete grammar.
--
-- Unlike 'pegRules', which is one part of a rule set and can be combined with
-- another, this owns the whole grammar.  Two things follow from that.
--
-- It knows every rule's position in the environment, so it emits
-- 'PEG.Syntax.ntw' and the membership proof rather than @nt@ and a
-- 'PEG.Member.KnownMember' search.  That is worth about 2.6x on the compile
-- time of a 64-rule grammar; see @bench-compile/@.
--
-- And it knows the whole grammar is in front of it, so a reference to a name
-- no rule defines is an error at the splice rather than a type error later.
--
-- == In expression position
--
-- @
-- arith :: Stream s => Grammar s ArithEnv _ Exp
-- arith = [pegGrammar|
--           %start expr
--           expr   \<- t:term ts:(o:[+-] u:term)* { foldl addOp t ts }
--           term   \<- ...
--         |]
-- @
--
-- == In declaration position
--
-- Give each rule its result type and the environment need not be written at
-- all — the quasi-quoter declares it, along with the grammar and its
-- signature:
--
-- @
-- [pegGrammar|
--   %name  arith
--   %start expr
--   expr   :: Exp \<- t:term ts:(o:[+-] u:term)* { foldl addOp t ts }
--   term   :: Exp \<- ...
-- |]
-- @
--
-- declares @type ArithEnv s@, @arith :: Stream s => Grammar s (ArithEnv s) Exp@
-- and @arith@ itself.  An entry of the environment is a rule's name and the
-- type it returns; the type is the one thing the grammar does not determine,
-- which is what the annotations are for.
--
-- == Directives
--
-- [@%start@] Required.  The start expression: a non-terminal's name, or any
--            PEG expression over the grammar's rules.
-- [@%name@]  Required in declaration position: the name to bind the grammar
--            to.
-- [@%env@]   The name of the generated environment synonym.  Defaults to the
--            grammar's name, capitalised, with @Env@ appended.
-- [@%stream@] The stream type.  Defaults to a variable @s@ with a
--            'PEG.Stream.Stream' constraint.
-- [@%result@] The grammar's result type, for the rare start expression whose
--            type cannot be read off the rules — one with a semantic action
--            of its own.
pegGrammar :: QuasiQuoter
pegGrammar = QuasiQuoter
  { quoteExp  = pegGrammarExp
  , quoteDec  = pegGrammarDec
  , quotePat  = \_ -> fail "pegGrammar: cannot be used as a pattern"
  , quoteType = \_ -> fail "pegGrammar: cannot be used as a type"
  }

-- | A grammar that has been parsed and checked: the pieces both forms need.
--
-- The analysis's own result is not among them.  It used to be — the FIRST
-- sets it computes were written into the environment — and now that entries
-- carry only a result type, running it is entirely a matter of the
-- diagnostics it raises.  It is still run, and it is now the only thing that
-- rejects a left-recursive grammar; see "PEG.Grammar".
data GrammarSrc = GrammarSrc
  { gsDirs  :: [Directive]
  , gsDefs  :: [Def]
  , gsStart :: PExpr
  }

gsNames :: GrammarSrc -> [String]
gsNames gs = [ n | Def n _ _ <- gsDefs gs ]

-- | Parse the header, the rules and the start expression, and run the
-- analysis over all of them.
parseGrammarSrc :: String -> Q GrammarSrc
parseGrammarSrc src = do
  (dirs, afterDirs) <- orFail (parseDirectives src)
  -- A mistyped directive is silent otherwise: @%strt expr@ would be reported
  -- as a missing %start, which points at the wrong thing.
  case [ k | Directive k _ <- dirs, k `notElem` knownDirectives ] of
    []    -> pure ()
    (k:_) -> fail ("pegGrammar: unknown directive %" ++ k
                     ++ "\n      known directives are "
                     ++ unwords [ '%' : d | d <- knownDirectives ])
  (defs, leftover)  <- orFail (parseGrammar afterDirs)
  case spaces leftover of
    [] -> pure ()
    r  -> fail ("pegGrammar: unconsumed input: " ++ show (take 30 r))
  startSrc <- case directive "start" dirs of
    Just v  -> pure v
    Nothing -> fail "pegGrammar: no %start directive"
  (start0, startRest) <- orFail (parseExpr startSrc)
  let start = normaliseStart start0
  case spaces startRest of
    [] -> pure ()
    r  -> fail ("pegGrammar: unconsumed input in %start: " ++ show (take 30 r))
  -- The start expression is a rule body in every way that matters here, so it
  -- is checked with the others: a name it references and no rule defines is
  -- reported the same way.
  case analyse (Def "%start" Nothing start : defs) of
    Left ds  -> fail ("pegGrammar:\n" ++ unlines
                        [ "      " ++ l
                        | d <- ds, l <- lines (renderDiagnostic (unstart d)) ])
    Right _  -> pure ()
  pure (GrammarSrc dirs defs start)
  where
    orFail = either (\e -> fail ("pegGrammar: parse error: " ++ e)) pure

    -- The start expression is not a rule, so it should not be named as one.
    unstart (LeftRecursive n p)  = LeftRecursive (rename n) (map rename p)
    unstart (NullableStar n)     = NullableStar (rename n)
    unstart (UndefinedNT n ns)   = UndefinedNT n (filter (/= "%start") ns)
    unstart (DuplicateRule n)    = DuplicateRule (rename n)
    rename n = if n == "%start" then "the start expression" else n

-- | @%start expr@ means the expression @expr@, not a one-item sequence whose
-- value is discarded.
--
-- Inside a rule, @r \<- term@ with neither a label nor an action does return
-- @()@ — that is the DSL's rule and it stays.  But a start expression is not
-- a rule: it is the @(nt \@"expr")@ that used to be written out by hand next
-- to the rule set, and that returned the rule's value.  A start with a label
-- or an action of its own is left alone; only a lone unlabelled item is
-- unwrapped.
normaliseStart :: PExpr -> PExpr
normaliseStart (ESeq [Item Nothing e] Nothing) = e
normaliseStart e                               = e

knownDirectives :: [String]
knownDirectives = ["start", "name", "env", "stream", "result"]

directive :: String -> [Directive] -> Maybe String
directive k ds = case [ v | Directive k' v <- ds, k' == k ] of
  (v:_) -> Just v
  []    -> Nothing

-- | Emit @ntw \@"name" (There (... Here))@: the proof instead of the search.
ntByWitness :: [String] -> String -> Q Exp
ntByWitness names name = case elemIndex name names of
  Nothing -> fail ("pegGrammar: undefined non-terminal: " ++ name)
  Just k  -> pure (TH.AppE (TH.AppTypeE (TH.VarE 'ntw)
                                        (TH.LitT (TH.StrTyLit name)))
                           (witness k))
  where
    witness 0 = TH.ConE 'Here
    witness k = TH.AppE (TH.ConE 'There) (witness (k - 1))

pegGrammarExp :: String -> Q Exp
pegGrammarExp src = do
  gs <- parseGrammarSrc src
  let ntRef = ntByWitness (gsNames gs)
  rules <- translateRules ntRef (gsDefs gs)
  start <- translateExprWith ntRef (gsStart gs)
  [| Grammar $(pure rules) $(pure start) |]

pegGrammarDec :: String -> Q [TH.Dec]
pegGrammarDec src = do
  gs <- parseGrammarSrc src
  gname <- case directive "name" (gsDirs gs) of
    Just v  -> pure (TH.mkName v)
    Nothing -> fail "pegGrammar: no %name directive, which declaring a \
                    \grammar needs"
  let baseName = maybe "" id (directive "name" (gsDirs gs))
      envName  = TH.mkName (maybe (capitalise baseName ++ "Env") id
                                  (directive "env" (gsDirs gs)))
      streamV  = TH.mkName "s"
  streamT <- case directive "stream" (gsDirs gs) of
    Nothing -> pure (TH.VarT streamV)
    Just t  -> either (\e -> fail ("pegGrammar: in %stream: " ++ e)) pure
                      (parseHsType t)
  anns <- mapM (resultAnnotation gname) (gsDefs gs)
  let envRhs = promotedList [ envEntry n ty | (n, ty) <- anns ]
  startRes <- case directive "result" (gsDirs gs) of
    Just t  -> either (\e -> fail ("pegGrammar: in %result: " ++ e)) pure
                      (parseHsType t)
    Nothing -> case resultTypeOf streamT anns (gsStart gs) of
      Just t  -> pure t
      Nothing -> fail "pegGrammar: cannot tell what the start expression \
                      \returns.\n  It has a semantic action of its own; state \
                      \its type with %result."
  let envApplied = TH.AppT (TH.ConT envName) streamT
      grammarTy  = foldl TH.AppT (TH.ConT ''Grammar)
                     [streamT, envApplied, startRes]
      sigTy = case directive "stream" (gsDirs gs) of
        Just _  -> grammarTy
        Nothing -> TH.ForallT [TH.PlainTV streamV TH.SpecifiedSpec]
                              [TH.AppT (TH.ConT ''Stream) (TH.VarT streamV)]
                              grammarTy
  body <- pegGrammarExp src
  pure [ TH.TySynD envName [TH.PlainTV streamV TH.BndrReq] envRhs
       , TH.SigD gname sigTy
       , TH.FunD gname [TH.Clause [] (TH.NormalB body) []]
       ]
  where
    capitalise []     = []
    capitalise (c:cs) = toUpper c : cs
    toUpper c = if c >= 'a' && c <= 'z' then toEnum (fromEnum c - 32) else c

-- | A rule's declared result type, which declaring an environment needs.
resultAnnotation :: TH.Name -> Def -> Q (String, TH.Type)
resultAnnotation gname (Def n ann _) = case ann of
  Nothing  -> fail ("pegGrammar: the rule " ++ n ++ " has no result type.\n\
                    \  Declaring " ++ show gname ++ " means writing the \
                    \environment down, and a rule's\n  result type is the one \
                    \thing the grammar does not say: write\n    " ++ n
                    ++ " :: T <- ...")
  Just src -> case parseHsType src of
    Left e  -> fail ("pegGrammar: in the result type of " ++ n ++ ": " ++ e)
    Right t -> pure (n, t)

-- | What the start expression returns, read off the rules' declared types.
--
-- This follows @translateSeqWith@: a sequence with no semantic action returns
-- its labelled items, one of them bare and several as a tuple.  A sequence
-- /with/ an action returns whatever the action does, which is Haskell and so
-- not knowable here — hence the 'Maybe', and the @%result@ directive.
resultTypeOf :: TH.Type -> [(String, TH.Type)] -> PExpr -> Maybe TH.Type
resultTypeOf streamT anns = go
  where
    go (ENT n)       = lookup n anns
    go (EChar _)     = Just (TH.ConT ''Char)
    go EDot          = Just (TH.ConT ''Char)
    go (EClass _ _)  = Just (TH.ConT ''Char)
    go (EString _)   = Just (TH.ConT ''String)
    go (EAnd _)      = Just (TH.TupleT 0)
    go (ENot _)      = Just (TH.TupleT 0)
    go (EOpt e)      = TH.AppT (TH.ConT ''Maybe) <$> go e
    go (EStar e)     = rep e
    go (EPlus e)     = rep e
    go (EIndent _ e) = go e
    go (EPos _ e)    = go e
    go (EAlign e)    = go e
    go (EChoice es)  = firstJust (map go es)
    go (ESeq _ (Just _)) = Nothing
    go (ESeq items Nothing) = case [ e | Item (Just _) e <- items ] of
      []  -> Just (TH.TupleT 0)
      [e] -> go e
      es  -> foldl TH.AppT (TH.TupleT (length es)) <$> mapM go es

    rep e | spannable e = Just streamT
          | otherwise   = TH.AppT TH.ListT <$> go e

    firstJust xs = case [ x | Just x <- xs ] of
      (x:_) -> Just x
      []    -> Nothing

--------------------------------------------------------------------------------
-- Building the environment's type
--------------------------------------------------------------------------------

promotedList :: [TH.Type] -> TH.Type
promotedList = foldr (\x acc -> TH.AppT (TH.AppT TH.PromotedConsT x) acc)
                     TH.PromotedNilT

envEntry :: String -> TH.Type -> TH.Type
envEntry n res =
  TH.AppT (TH.AppT (TH.PromotedTupleT 2) (TH.LitT (TH.StrTyLit n)))
          (TH.AppT (TH.PromotedT 'EnvEntry) res)
