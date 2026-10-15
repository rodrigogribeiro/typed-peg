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
-- @\@@ consumes nothing and returns the current offset, an 'Int': label it to
-- give a semantic action the position of what follows, as in
-- @p:\@ k:"while" c:expr { While p c }@.  "PEG.Location" turns an offset
-- into a line and a column.
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

import Control.Monad              (foldM, unless)
import Data.Data                  (Data, gmapQ)
import Data.Typeable              (cast)
import Data.List                  (elemIndex, groupBy, nub)
import Language.Haskell.TH        (Exp (..), Pat (..), Q)
import qualified Language.Haskell.TH      as TH
import Language.Haskell.TH.Quote  (QuasiQuoter (..))

import PEG
import PEG.Analysis  (Diagnostic (..), World (..), analyse, analyseWith,
                      renderDiagnostic, spannable)
import PEG.QQ.Compat (requiredKindedTV, requiredTV)
import PEG.QQ.HsExp  (parseHsExp, parseHsType)
import PEG.QQ.Syntax (Def (..), Directive (..), Item (..), PExpr (..),
                      RelS (..), parseDirectives, parseExpr, parseGrammar,
                      parseLabel, spaces)

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
    go EOffset =
      [| GetOffset |]
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
    go (EChoice es) = do
      alts <- mapM toAlt es
      translateAlts ntRef alts
    go (ESeq items act) = do
      body <- seqBody items act
      translateAlt ntRef (Alt items [] body)

    toAlt (ESeq items act) = Alt items [] <$> seqBody items act
    toAlt e                = pure (Opaque e)

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

-- | One alternative of an ordered choice, on its way to being translated.
--
-- An 'Alt' is the part of a sequence still to be parsed, together with the
-- patterns for values an enclosing factoring has already parsed on its
-- behalf, and the semantic action over all of them.  It translates to an
-- expression returning a function of those earlier values: @\rest... ->
-- \outer... -> body@.  An alternative that is not a sequence is 'Opaque' and
-- never shares a prefix with anything.
data Alt
  = Alt [Item] [Pat] Exp
  | Opaque PExpr

-- | Translate an ordered choice, factoring out prefixes that consecutive
-- alternatives share.
--
-- == Why
--
-- A PEG does not memoise, so in
--
-- @
-- expr <- e:or_expr ws "if" c:or_expr ws "else" a:expr { ... }
--       / e:or_expr { e }
-- @
--
-- a plain expression is parsed twice: once by the alternative that fails
-- at @"if"@ and once by the one that succeeds.  Each precedence level written
-- this way doubles the work, and levels nest — through parentheses, call
-- arguments, list elements — so the cost is exponential in how deeply the
-- /input/ nests.  On the MiniPython grammar @print(str(mdc(f(g(x)))))@ took
-- a third of a second, eight times as long per level.
--
-- == What it does
--
-- In a PEG, @A B \/ A C@ and @A (B \/ C)@ accept the same inputs with the
-- same results: @A@ is deterministic, so the second alternative would parse
-- exactly what the first one did before it failed.  Consecutive alternatives
-- whose leading items are the same expression — labels aside — are
-- translated as their longest common prefix followed by a choice of what is
-- left of each, which is factored again.  Only /consecutive/ alternatives
-- are grouped: in @A B \/ X \/ A C@ the @X@ must still be tried between them.
--
-- Each remainder returns a function of the prefix's values, so that its
-- action still sees the prefix under the labels it gave it.
translateAlts :: (String -> Q Exp) -> [Alt] -> Q Exp
translateAlts ntRef alts = do
  es <- mapM (translateGroup ntRef) (groupBy sameHead alts)
  case es of
    []       -> fail "QQ: empty choice (should be impossible)"
    (e:rest) -> foldM (\acc x -> [| $(pure acc) .||. $(pure x) |]) e rest
  where
    sameHead (Alt (Item _ a : _) _ _) (Alt (Item _ b : _) _ _) = a == b
    sameHead _ _                                             = False

translateGroup :: (String -> Q Exp) -> [Alt] -> Q Exp
translateGroup ntRef [alt] = translateAlt ntRef alt
translateGroup ntRef grp = do
  let itemss = [ is | Alt is _ _ <- grp ]
      k      = commonPrefix itemss
      prefix = [ e | Item _ e <- take k (headItems itemss) ]
  xs <- mapM (\i -> TH.newName ("p" ++ show i)) [1 .. k]
  kf <- TH.newName "rest"
  let apply = LamE (map VarP xs ++ [VarP kf])
                   (foldl AppE (VarE kf) (map VarE xs))
      remainders = [ Alt (drop k is) (map itemPat (take k is) ++ outer) body
                   | Alt is outer body <- grp ]
  pes  <- mapM (translateExprWith ntRef) prefix
  rest <- translateAlts ntRef remainders
  case pes of
    []       -> fail "QQ: factoring an empty prefix (should be impossible)"
    (p:ps)   -> do
      hd <- [| fmapP $(pure apply) $(pure p) |]
      foldM (\acc x -> [| $(pure acc) <*>. $(pure x) |]) hd (ps ++ [rest])
  where
    headItems (is:_) = is
    headItems []     = []

    commonPrefix []       = 0
    commonPrefix (i:iss)  = foldr (min . agree i) (length i) iss
    agree as bs = length (takeWhile id (zipWith sameItem as bs))
    sameItem (Item _ a) (Item _ b) = a == b

-- | Translate one alternative that nothing is factored out of.
translateAlt :: (String -> Q Exp) -> Alt -> Q Exp
translateAlt ntRef (Opaque e) = translateExprWith ntRef e
translateAlt ntRef (Alt items outer body) = do
  es <- mapM (\(Item _ e) -> translateExprWith ntRef e) items
  case es of
    []       -> [| pureP $(pure (lambda outer body)) |]
    (e:rest) -> do
      hd <- [| fmapP $(pure (LamE (map itemPat items ++ outer) body)) $(pure e) |]
      foldM (\acc x -> [| $(pure acc) <*>. $(pure x) |]) hd rest
  where
    lambda [] b = b
    lambda ps b = LamE ps b

itemPat :: Item -> Pat
itemPat (Item (Just l) _) = VarP (TH.mkName l)
itemPat (Item Nothing _)  = WildP

-- | The value a sequence returns: its semantic action, or its labelled items
-- when it has none — one of them bare, several as a tuple, none as @()@.
seqBody :: [Item] -> Maybe String -> Q Exp
seqBody items act = do
  let labels = [ l | Item (Just l) _ <- items ]
  case duplicates labels of
    (l:_) -> fail ("QQ: the label " ++ show l
                     ++ " is used twice in the same sequence")
    []    -> pure ()
  case act of
    Nothing  -> pure (defaultBody labels)
    Just src -> case parseHsExp src of
      Right e  -> pure e
      Left err -> fail ("QQ: in the semantic action {" ++ src ++ "}: " ++ err)
  where
    defaultBody []  = TH.ConE '()
    defaultBody [l] = TH.VarE (TH.mkName l)
    defaultBody ls  = TH.TupE (map (Just . TH.VarE . TH.mkName) ls)

    duplicates xs = [ x | x <- nub xs, length (filter (== x) xs) > 1 ]

translateRules :: [(String, String)] -> (String -> Q Exp) -> [Def] -> Q Exp
translateRules _ _ [] = [| RNil |]
translateRules labels ntRef (Def name _ expr : rest) = do
  body  <- withLabel labels name <$> translateExprWith ntRef expr
  rest' <- translateRules labels ntRef rest
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
      Right _ -> translateRules [] ntByName defs

--------------------------------------------------------------------------------
-- pegGrammar: a whole grammar, environment included
--------------------------------------------------------------------------------

-- | Quasi-quoter for a complete grammar.
--
-- Unlike 'pegRules', which is one part of a rule set and can be combined with
-- another, this owns the whole grammar, so a reference to a name no rule
-- defines is an error at the splice rather than a type error later, and left
-- recursion is looked for across every rule.
--
-- == In declaration position
--
-- Give each rule its result type and nothing else need be written — the
-- quasi-quoter declares the grammar's key type, the grammar, and its
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
-- declares
--
-- @
-- data ArithEnv s a where
--   ArithEnv_expr :: ArithEnv s Exp
--   ArithEnv_term :: ArithEnv s Exp
-- instance 'Tabulate' (ArithEnv s)
--
-- arith'expr :: Stream s => PExp s (ArithEnv s) Exp
-- arith'term :: Stream s => PExp s (ArithEnv s) Exp
--
-- arith :: Stream s => Grammar s (ArithEnv s) Exp
-- @
--
-- A reference to @term@ is @'NT' ArithEnv_term@, whose type is checked
-- without looking at the rest of the grammar, so the cost of type-checking a
-- grammar grows with its size and no faster.  Each rule is a binding of its
-- own with the declared type as its signature, so an annotation that
-- disagrees with the rule's body is reported against that rule.  The module
-- needs @GADTs@, since the key type is one.
--
-- == In expression position
--
-- @
-- arith :: Grammar String _ Exp
-- arith = [pegGrammar|
--           %start expr
--           expr   \<- t:term ts:(o:[+-] u:term)* { foldl addOp t ts }
--           term   \<- ...
--         |]
-- @
--
-- An expression cannot declare a type, so there is no key type to generate:
-- the grammar is built over a type-level environment, as 'pegRules' builds
-- it, with each reference carrying its membership proof.  That is fine for a
-- grammar of a few dozen rules and increasingly expensive past that; see
-- "PEG.Key".  Prefer declaration position, with @%param@ for what the
-- expression form would have captured from its surroundings.
--
-- == Directives
--
-- [@%start@] Required.  The start expression: a non-terminal's name, or any
--            PEG expression over the grammar's rules.
-- [@%name@]  Required in declaration position: the name to bind the grammar
--            to.
-- [@%env@]   The name of the generated key type.  Defaults to the grammar's
--            name, capitalised, with @Env@ appended.
-- [@%stream@] The stream type.  Defaults to a variable @s@ with a
--            'PEG.Stream.Stream' constraint.
-- [@%result@] The grammar's result type, for the rare start expression whose
--            type cannot be read off the rules — one with a semantic action
--            of its own.
-- [@%param@] @%param name :: Type@, in declaration position: the grammar and
--            every rule take an argument @name@, in scope in every semantic
--            action.  May be repeated; the arguments are taken in order.
-- [@%label@] @%label rule "name"@: when the parse fails, and @rule@ failed
--            at the error's position without consuming anything, the list of
--            what was expected says @name@ instead of what @rule@ was looking
--            for.  @%label rule ""@ keeps @rule@ out of that list altogether,
--            which is what whitespace wants.  May be repeated, once per rule;
--            see 'PEG.Parse.ParseError' and 'PEG.Syntax.Label'.
pegGrammar :: QuasiQuoter
pegGrammar = QuasiQuoter
  { quoteExp  = pegGrammarExp
  , quoteDec  = pegGrammarDec
  , quotePat  = \_ -> fail "pegGrammar: cannot be used as a pattern"
  , quoteType = \_ -> fail "pegGrammar: cannot be used as a type"
  }

-- | Wrap a rule's body in its @%label@, if it has one.
withLabel :: [(String, String)] -> String -> Exp -> Exp
withLabel labels name body = case lookup name labels of
  Nothing -> body
  Just l  -> TH.AppE (TH.AppE (TH.ConE 'Label) (TH.LitE (TH.StringL l))) body

-- | A grammar that has been parsed and checked: the pieces both forms need.
--
-- The analysis's own result is not among them.  It used to be — the FIRST
-- sets it computes were written into the environment — and now that entries
-- carry only a result type, running it is entirely a matter of the
-- diagnostics it raises.  It is still run, and it is now the only thing that
-- rejects a left-recursive grammar; see "PEG.Grammar".
data GrammarSrc = GrammarSrc
  { gsDirs   :: [Directive]
  , gsDefs   :: [Def]
  , gsStart  :: PExpr
  , gsLabels :: [(String, String)]  -- ^ @%label@: rule, name
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
  labels <- mapM (orFailIn "%label" . parseLabel) (directives "label" dirs)
  let ruleNames = [ n | Def n _ _ <- defs ]
  case [ r | (r, _) <- labels, r `notElem` ruleNames ] of
    []    -> pure ()
    (r:_) -> fail ("pegGrammar: %label names " ++ r ++ ", which is not a rule;\n\
                   \      the grammar defines " ++ unwords ruleNames)
  case dupsOf (map fst labels) of
    []    -> pure ()
    (r:_) -> fail ("pegGrammar: the rule " ++ r ++ " has two %label directives")
  pure (GrammarSrc dirs defs start labels)
  where
    orFailIn d = either (\e -> fail ("pegGrammar: in " ++ d ++ ": " ++ e)) pure
    dupsOf xs = [ x | (i, x) <- zip [0 :: Int ..] xs, x `elem` take i xs ]

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
knownDirectives = ["start", "name", "env", "stream", "result", "param", "label"]

directive :: String -> [Directive] -> Maybe String
directive k ds = case directives k ds of
  (v:_) -> Just v
  []    -> Nothing

directives :: String -> [Directive] -> [String]
directives k ds = [ v | Directive k' v <- ds, k' == k ]

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
  unless (null (directives "param" (gsDirs gs))) $
    fail "pegGrammar: %param is only meaningful in declaration position;\n\
         \      an expression can use the variables in scope around it"
  let ntRef = ntByWitness (gsNames gs)
  rules <- translateRules (gsLabels gs) ntRef (gsDefs gs)
  start <- translateExprWith ntRef (gsStart gs)
  [| Grammar $(pure rules) $(pure start) |]

pegGrammarDec :: String -> Q [TH.Dec]
pegGrammarDec src = do
  gs <- parseGrammarSrc src
  gadts <- TH.isExtEnabled TH.GADTs
  unless gadts $
    fail "pegGrammar: declaring a grammar declares a GADT, its key type;\n\
         \      enable {-# LANGUAGE GADTs #-} in this module"
  baseName <- case directive "name" (gsDirs gs) of
    Just v  -> pure v
    Nothing -> fail "pegGrammar: no %name directive, which declaring a \
                    \grammar needs"
  let gname    = TH.mkName baseName
      envStr   = maybe (capitalise baseName ++ "Env") id
                       (directive "env" (gsDirs gs))
      envName  = TH.mkName envStr
      streamV  = TH.mkName "s"
      polyStream = directive "stream" (gsDirs gs) == Nothing
  streamT <- case directive "stream" (gsDirs gs) of
    Nothing -> pure (TH.VarT streamV)
    Just t  -> either (\e -> fail ("pegGrammar: in %stream: " ++ e)) pure
                      (parseHsType t)
  params <- mapM parseParam (directives "param" (gsDirs gs))
  anns0 <- mapM (resultAnnotation gname) (gsDefs gs)
  -- A result type may mention the stream as @s@.  In the key type @s@ is the
  -- type's own parameter, so it can stay; in a signature of a grammar over a
  -- fixed stream it has to become that stream.
  let atStream = if polyStream then id else substVar streamV streamT
      anns     = [ (n, atStream t) | (n, t) <- anns0 ]
  startRes <- case directive "result" (gsDirs gs) of
    Just t  -> either (\e -> fail ("pegGrammar: in %result: " ++ e))
                      (pure . atStream) (parseHsType t)
    Nothing -> case resultTypeOf streamT anns (gsStart gs) of
      Just t  -> pure t
      Nothing -> fail "pegGrammar: cannot tell what the start expression \
                      \returns.\n  It has a semantic action of its own; state \
                      \its type with %result."
  let keyCon n  = TH.mkName (envStr ++ "_" ++ n)
      ruleVar n = TH.mkName (baseName ++ "'" ++ n)
      ntT       = TH.AppT (TH.ConT envName) streamT
      ntRef n   = pure (TH.AppE (TH.ConE 'NT) (TH.ConE (keyCon n)))
      -- A rule that does not use a parameter binds it to @_@, so that a
      -- grammar with a parameter only some actions need compiles cleanly
      -- under @-Wunused-matches@.
      usedPats body = [ if mentions p body then TH.VarP p else TH.WildP
                      | (p, _) <- params ]
      paramArgs = [ TH.VarE p | (p, _) <- params ]
      -- @forall s. Stream s => P1 -> ... -> t@, or @P1 -> ... -> t@ over a
      -- fixed stream.
      signature t =
        let body = foldr (\(_, pt) r -> TH.AppT (TH.AppT TH.ArrowT pt) r)
                         t params
        in if polyStream
             then TH.ForallT [TH.PlainTV streamV TH.SpecifiedSpec]
                             [TH.AppT (TH.ConT ''Stream) (TH.VarT streamV)]
                             body
             else body
      names = gsNames gs

  -- The key type: one constructor per rule, indexed by the rule's result.
  resV <- TH.newName "a"
  let keyDecl = TH.DataD [] envName
        [ requiredTV streamV
        , requiredKindedTV resV TH.StarT ]
        Nothing
        [ TH.GadtC [keyCon n] []
            (TH.AppT (TH.AppT (TH.ConT envName) (TH.VarT streamV)) ty)
        | (n, ty) <- anns0 ]
        []

  -- Its 'Tabulate' instance.  Every rule's image is bound once, outside the
  -- lookup, which is what makes the table a memo table.
  fV <- TH.newName "f"
  kV <- TH.newName "k"
  xs <- mapM (\n -> TH.newName ("x_" ++ n)) names
  let onKey arms = TH.LamE [TH.VarP kV] (caseOrAbsurd (TH.VarE kV) arms)
      caseOrAbsurd scrut [] =
        -- A grammar with no rules has an uninhabited key type.
        TH.AppE (TH.AppE (TH.VarE 'seq) scrut)
                (TH.AppE (TH.VarE 'error)
                         (TH.LitE (TH.StringL "PEG: no rules")))
      caseOrAbsurd scrut arms = TH.CaseE scrut arms
      arm n e = TH.Match (TH.ConP (keyCon n) [] []) (TH.NormalB e) []
      tabulateD = TH.FunD 'tabulate
        [ TH.Clause [TH.VarP fV]
            (TH.NormalB
               (letOrBody
                  [ TH.ValD (TH.VarP x)
                            (TH.NormalB (TH.AppE (TH.VarE fV)
                                                 (TH.ConE (keyCon n))))
                            []
                  | (n, x) <- zip names xs ]
                  (TH.AppE (TH.ConE 'Table)
                           (onKey [ arm n (TH.VarE x)
                                  | (n, x) <- zip names xs ]))))
            [] ]
      letOrBody [] e = e
      letOrBody ds e = TH.LetE ds e
      ruleNameD = TH.FunD 'ruleName
        [ TH.Clause [TH.VarP kV]
            (TH.NormalB (caseOrAbsurd (TH.VarE kV)
                           [ arm n (TH.LitE (TH.StringL n)) | n <- names ]))
            [] ]
      instDecl = TH.InstanceD Nothing []
        (TH.AppT (TH.ConT ''Tabulate)
                 (TH.AppT (TH.ConT envName) (TH.VarT streamV)))
        [tabulateD, ruleNameD]

  -- One binding per rule, with the declared type as its signature.
  ruleDecls <- fmap concat $ mapM
    (\(Def n _ e, (_, ty)) -> do
        body <- withLabel (gsLabels gs) n <$> translateExprWith ntRef e
        pure [ TH.SigD (ruleVar n)
                 (signature (foldl TH.AppT (TH.ConT ''PExp) [streamT, ntT, ty]))
             , TH.FunD (ruleVar n)
                 [TH.Clause (usedPats body) (TH.NormalB body) []]
             ])
    (zip (gsDefs gs) anns)

  -- The grammar: the rules as a function of their keys, and the start.
  start <- translateExprWith ntRef (gsStart gs)
  let rulesE = onKey [ arm n (foldl TH.AppE (TH.VarE (ruleVar n)) paramArgs)
                     | n <- names ]
      grammarTy = foldl TH.AppT (TH.ConT ''Grammar) [streamT, ntT, startRes]
  pure $ [ keyDecl, instDecl ] ++ ruleDecls ++
    [ TH.SigD gname (signature grammarTy)
    , TH.FunD gname
        [ TH.Clause (usedPats (TH.AppE rulesE start))
            (TH.NormalB (TH.AppE (TH.AppE (TH.ConE 'Keyed) rulesE) start)) [] ]
    ]
  where
    capitalise []     = []
    capitalise (c:cs) = toUpper c : cs
    toUpper c = if c >= 'a' && c <= 'z' then toEnum (fromEnum c - 32) else c

-- | @%param name :: Type@.
parseParam :: String -> Q (TH.Name, TH.Type)
parseParam src = case breakOnSig src of
  Just (nm, ty)
    | validName nm -> either (\e -> fail ("pegGrammar: in %param " ++ nm
                                            ++ ": " ++ e))
                             (\t -> pure (TH.mkName nm, t))
                             (parseHsType ty)
  _ -> fail ("pegGrammar: expected %param name :: Type, found %param " ++ src)
  where
    breakOnSig = go []
      where
        go acc (':':':':rest) = Just (trim (reverse acc), rest)
        go acc (c:cs)         = go (c:acc) cs
        go _   []             = Nothing
    trim = reverse . dropWhile (== ' ') . reverse . dropWhile (== ' ')
    validName (c:cs) = (c == '_' || (c >= 'a' && c <= 'z'))
                       && all (\x -> x == '_' || x == '\'' || (x >= 'a' && x <= 'z')
                                     || (x >= 'A' && x <= 'Z')
                                     || (x >= '0' && x <= '9')) cs
    validName []     = False

-- | Does the name occur anywhere in the expression?  Conservative: a
-- binding of the same name inside counts as an occurrence.
mentions :: Data a => TH.Name -> a -> Bool
mentions n x = case cast x of
  Just n' -> n' == n
  Nothing -> or (gmapQ (mentions n) x)

-- | Replace a type variable.
substVar :: TH.Name -> TH.Type -> TH.Type -> TH.Type
substVar v new = go
  where
    go (TH.VarT n) | n == v    = new
    go (TH.AppT a b)           = TH.AppT (go a) (go b)
    go (TH.AppKindT t k)       = TH.AppKindT (go t) k
    go (TH.SigT t k)           = TH.SigT (go t) k
    go (TH.InfixT a n b)       = TH.InfixT (go a) n (go b)
    go (TH.ParensT t)          = TH.ParensT (go t)
    go t                       = t

-- | A rule's declared result type, which declaring the key type needs.
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
-- This follows @seqBody@: a sequence with no semantic action returns
-- its labelled items, one of them bare and several as a tuple.  A sequence
-- /with/ an action returns whatever the action does, which is Haskell and so
-- not knowable here — hence the 'Maybe', and the @%result@ directive.
resultTypeOf :: TH.Type -> [(String, TH.Type)] -> PExpr -> Maybe TH.Type
resultTypeOf streamT anns = go
  where
    go (ENT n)       = lookup n anns
    go (EChar _)     = Just (TH.ConT ''Char)
    go EDot          = Just (TH.ConT ''Char)
    go EOffset       = Just (TH.ConT ''Int)
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
