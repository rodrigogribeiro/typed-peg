{-# LANGUAGE DataKinds       #-}
{-# LANGUAGE GADTs           #-}
{-# LANGUAGE QuasiQuotes     #-}
{-# LANGUAGE TemplateHaskell #-}
-- | Checks where a failed parse is reported.
--
-- A 'Fail' carries the furthest offset at which any part of the grammar
-- failed, and its line and column.  That offset is threaded through every
-- compiled step, including the fast paths that match a literal or a run of a
-- class in one go and the slow paths taken under indentation constraints, so
-- it is easy to get right in one place and wrong in another.  It is checked
-- two ways:
--
-- * Hand-picked cases, each stating where the error is and why: the rules
--   'PEG.Parse' documents — a literal fails where it starts, a repetition's
--   last failure counts, nothing inside a lookahead counts — and the line and
--   column arithmetic.
-- * A reference interpreter, written to be obvious rather than fast, against
--   which the compiled parser is compared on a few thousand generated
--   grammars and inputs, over every stream and with and without layout.
--
-- What was found and expected at the error is checked the same two ways: by
-- cases for each rule 'PEG.Parse' states, and by the reference interpreter,
-- which computes the expected list straight from its definition.
module Main (main) where

import Control.Exception (SomeException, evaluate, try)
import Control.Monad (unless)
import Data.Char     (isAlphaNum)
import Data.List     (isPrefixOf, nub)
import System.Exit   (exitFailure)
import Language.Haskell.TH        (runQ)
import Language.Haskell.TH.Quote  (quoteExp)

import qualified Data.ByteString.Char8 as BC
import qualified Data.Text             as T

import PEG
import PEG.QQ (pegGrammar)

--------------------------------------------------------------------------------
-- Hand-picked cases
--------------------------------------------------------------------------------

-- | An expression with no rules, run on a 'String'.
run :: PExp String (InEnv '[]) a -> String -> Result String a
run e = parse (Grammar RNil e)

-- | @e@ then @f@, keeping neither result.
(~>) :: PExp s nt a -> PExp s nt b -> PExp s nt ()
e ~> f = (\_ _ -> ()) <$>. e <*>. f
infixr 4 ~>

ch :: Char -> PExp s nt ()
ch c = () <$ Term c

eof :: PExp s nt ()
eof = Not AnyChar

-- | Where the expression is expected to fail: line, column, offset.
data Want = Want Int Int Int

failsAt :: Result s a -> Want -> Bool
failsAt (Fail e) (Want l c o) = (errLine e, errColumn e, errOffset e) == (l, c, o)
failsAt _        _            = False

cases :: [(String, Bool)]
cases =
  [ ("a literal fails where it starts",
      run (ch 'x' ~> Str "while") "xwhale" `failsAt` Want 1 2 1)
  , ("an alternative that got further is remembered past a later success",
      -- (abc / a) z on "abd": the first alternative fails at the d, the
      -- second succeeds, and z fails earlier than the d.
      run (((ch 'a' ~> ch 'b' ~> ch 'c') .||. ch 'a') ~> ch 'z') "abd"
        `failsAt` Want 1 3 2)
  , ("nothing inside a negative lookahead counts",
      run (Not (ch 'a' ~> ch 'b' ~> ch 'c') ~> ch 'q') "abx" `failsAt` Want 1 1 0)
  , ("a failing negative lookahead fails where it was tried",
      run (ch 'a' ~> Not (ch 'b')) "ab" `failsAt` Want 1 2 1)
  , ("nothing inside a positive lookahead counts",
      run (Not (Not (ch 'a' ~> ch 'b')) ~> ch 'q') "ax" `failsAt` Want 1 1 0)
  , ("the iteration that ends a repetition counts",
      run (Star (ch 'a' ~> ch 'b') ~> eof) "abac" `failsAt` Want 1 4 3)
  , ("a trailing !. reports the leftover input",
      run (ch 'a' ~> eof) "ax" `failsAt` Want 1 2 1)
  , ("lines are counted from 1, and a newline starts a line at column 1",
      run (Star (ch 'a' ~> ch '\n') ~> eof) "a\na\nab" `failsAt` Want 3 2 5)
  , ("the end of an input that ends in a newline is on the next line",
      run (ch 'a' ~> ch '\n' ~> ch 'b') "a\n" `failsAt` Want 2 1 2)
  , ("a tab advances the column by one",
      run (ch '\t' ~> ch 'y') "\tx" `failsAt` Want 1 2 1)
  , ("a run of a class reports the character after it",
      run (spanOf1 (fromRanges [('a', 'z')]) ~> ch ';') "abc1" `failsAt` Want 1 4 3)
  , ("an empty input fails at 1:1",
      run (ch 'a') "" `failsAt` Want 1 1 0)
  , ("a character the layout rejects fails at its own offset",
      -- Under =, every token must be in the same column; the 7 is not.
      case parseWith defaultOpts { optTokenMode = relD eqR }
                     (Grammar RNil (ch '-' ~> ch '7')) "-7" of
        r -> r `failsAt` Want 1 2 1
               && okIs (run (ch '-' ~> ch '7') "-7"))
  , ("a literal under layout still fails where it starts",
      parseWith defaultOpts { optTokenMode = relD geR }
                (Grammar RNil (ch 'x' ~> Str "while")) "xwhale"
        `failsAt` Want 1 2 1)
  , ("every stream reports the same place",
      and [ errOf (parse g s) == errOf (parse g (T.pack s))
              && errOf (parse g s) == errOf (parse g (BC.pack s))
          | s <- ["a\na\nab", "abd", "x\twhale", ""] ])
  , ("a quasi-quoted grammar points at the token that is wrong",
      -- The ';' on line 2 is where an operand was expected.
      let src = "x := 1;\ny := 2 + ;\n"
      in parse stmts src `failsAt` Want 2 10 17)
  , ("a quasi-quoted grammar that succeeds is unaffected",
      okIs (parse stmts "x := 1;\ny := 2 + 3;\n"))

    -- What was found, and what was expected.  'calc' labels factor and name,
    -- and hides ws.
  , ("a label replaces what a rule that starts at the error looked for",
      says calc "x := 1;\ny := (2 + ) * x;\nprint y;\n"
        (2, 11) (FoundToken ")") [ExpLabel "an operand"])
  , ("a rule that started before the error lists what it looked for",
      -- factor began at the 2, so its label does not apply; one more digit
      -- would have been accepted, and so would '*', '+' or ')'.
      says calc "x := (1 + 2;\n"
        (1, 12) (FoundToken ";")
        [ExpClass "[0-9]", ExpChar '*', ExpChar '+', ExpChar ')'])
  , ("a hidden rule is never listed, and a word is found whole",
      says calc "x := 1\nprint x;\n"
        (2, 1) (FoundToken "print") [ExpChar '*', ExpChar '+', ExpChar ';'])
  , ("a literal, a label and the end of the input",
      says calc "x := 1;\nprint x; @\n"
        (2, 10) (FoundToken "@") [ExpString "print", ExpLabel "a name", ExpEnd])
  , ("the end of the input is found at the end",
      says calc "x := 1 +\n" (2, 1) FoundEnd [ExpLabel "an operand"])
  , ("a negated class is described as it is written",
      says quoted "\"abc" (1, 5) FoundEnd [ExpClass "[^\"]", ExpChar '"'])
  , ("the message reads well",
      case parse calc "x := (1 + 2;\n" of
        Fail e -> renderParseError e
                    == "1:12: unexpected ';', expecting [0-9], '*', '+' or ')'"
        _      -> False)
  , ("every stream finds and expects the same",
      and [ errOf (parse calc s) == errOf (parse calc (T.pack s))
              && errOf (parse calc s) == errOf (parse calc (BC.pack s))
          | s <- [ "x := 1;\ny := (2 + ) * x;\n", "x := (1 + 2;\n"
                 , "x := 1\nprint x;\n", "x := 1 +\n" ] ])
  ]
  where
    okIs (OK _ _ _) = True
    okIs _          = False

    says :: Grammar String nt a -> String -> (Int, Int) -> Found -> [Expected]
         -> Bool
    says gr src (l, c) found expect = case parse gr src of
      Fail e -> (errLine e, errColumn e) == (l, c)
                  && errFound e == found && errExpected e == expect
      _      -> False

    g :: Stream s => Grammar s (InEnv '[]) ()
    g = Grammar RNil ((Star (ch 'a' ~> ch '\n') ~> ch 'a' ~> ch 'b' ~> ch 'c')
                       .||. (() <$ Str "x\twhile"))

    errOf :: Result s a -> Maybe ParseError
    errOf (Fail e) = Just e
    errOf _        = Nothing

[pegGrammar|
  %name   stmts
  %stream String
  %start  prog

  prog :: Int    <- ws ss:stmt* !.             { length ss }
  stmt :: ()     <- name ":=" ws expr ';' ws     { () }
  expr :: ()     <- atom ('+' ws atom)*         { () }
  atom :: ()     <- [0-9]+ ws { () } / name { () }
  name :: String <- cs:[a-z]+ ws               { cs }
  ws   :: ()     <- [ \t\n]*                   { () }
|]

-- | The grammar of the example in the documentation: factor and name are
-- labelled, and ws is hidden.
[pegGrammar|
  %name   calc
  %start  ss:prog !.
  %label  factor "an operand"
  %label  name   "a name"
  %label  ws     ""

  prog   :: Int    <- ws ss:stmt*                       { length ss }
  stmt   :: ()     <- "print" ![a-z] ws expr ';' ws     { () }
                   /  name ":=" ws expr ';' ws          { () }
  expr   :: ()     <- term ('+' ws term)*               { () }
  term   :: ()     <- factor ('*' ws factor)*           { () }
  factor :: ()     <- [0-9]+ ws { () } / name { () } / '(' ws expr ')' ws { () }
  name   :: ()     <- [a-z]+ ws                         { () }
  ws     :: ()     <- [ \t\n]*                          { () }
|]

[pegGrammar|
  %name   quoted
  %start  q:str !.
  str :: () <- '"' [^"]* '"'  { () }
|]

-- | A @%label@ the splice must refuse.  Run in 'IO', a failing quasi-quoter
-- prints its message and throws one that only says it failed, so what is
-- checked here is the refusal; the messages are on the test's output.
labelErrors :: IO [String]
labelErrors = concat <$> mapM refused
  [ "%start a\n%label b \"x\"\na :: () <- 'a' { () }"               -- not a rule
  , "%start a\n%label a \"x\"\n%label a \"y\"\na :: () <- 'a' { () }" -- twice
  , "%start a\n%label a x\na :: () <- 'a' { () }" ]                  -- not a string
  where
    refused src = do
      r <- try (runQ (quoteExp pegGrammar src)
                  >>= \e -> evaluate (length (show e)))
             :: IO (Either SomeException Int)
      pure $ case r of
        Left _  -> []
        Right _ -> ["%label: accepted " ++ show src]

--------------------------------------------------------------------------------
-- The reference interpreter
--------------------------------------------------------------------------------

-- | A grammar to generate: untyped, so that it can be both interpreted below
-- and translated to a 'PExp'.
data G
  = GChar Char
  | GSat [Char]
  | GAny
  | GStr String
  | GSpan [Char]
  | GSpan1 [Char]
  | GSeq G G
  | GCh G G
  | GStar G          -- ^ Only ever over something that consumes input.
  | GNot G
  | GOff
  | GLabel String G  -- ^ The empty string hides.
  deriving Show

-- | What 'PEG.Parse' documents, stated directly: run @g@ from @off@ with the
-- furthest failure so far @far@, and return either the new furthest failure,
-- or the offset reached and the furthest failure.
ref :: G -> Int -> Int -> String -> Either Int (Int, Int, String)
ref g far off inp = case g of
  GChar c      -> char (== c)
  GSat cs   -> char (`elem` cs)
  GAny      -> char (const True)
  GStr lit
    | lit `isPrefixOf` inp -> Right (far, off + length lit, drop (length lit) inp)
    | otherwise            -> Left (max far off)
  GSpan cs  -> let n = length (takeWhile (`elem` cs) inp)
               in Right (max far (off + n), off + n, drop n inp)
  GSpan1 cs -> let n = length (takeWhile (`elem` cs) inp)
               in if n == 0 then Left (max far off)
                            else Right (max far (off + n), off + n, drop n inp)
  GSeq a b  -> case ref a far off inp of
                 Left f              -> Left f
                 Right (f, off', r)  -> ref b f off' r
  GCh a b   -> case ref a far off inp of
                 Left f -> ref b f off inp
                 r      -> r
  GStar a   -> let go f o r = case ref a f o r of
                                Left f'            -> Right (f', o, r)
                                Right (f', o', r') -> go f' o' r'
               in go far off inp
  GNot a    -> case ref a far off inp of
                 Left _  -> Right (far, off, inp)
                 Right _ -> Left (max far off)
  GOff      -> Right (far, off, inp)
  GLabel _ a -> ref a far off inp
  where
    char p = case inp of
      (c : r) | p c -> Right (far, off + 1, r)
      _             -> Left (max far off)

-- | What 'PEG.Parse' documents as expected at the error's offset @f@, stated
-- directly: run @g@ from @off@, and return whether it matched (and where it
-- got to) together with what it listed, in the order it was tried.
refExp :: Int -> G -> Int -> String -> (Maybe (Int, String), [Expected])
refExp f g off inp = case g of
  GChar c   -> char (== c) (ExpChar c)
  GSat cs   -> char (`elem` cs) (classOf cs)
  GAny      -> char (const True) ExpAny
  GStr lit
    | lit `isPrefixOf` inp -> (Just (off + length lit, drop (length lit) inp), [])
    | otherwise            -> (Nothing, here off (ExpString lit))
  GSpan cs  -> let n = length (takeWhile (`elem` cs) inp)
               in (Just (off + n, drop n inp), here (off + n) (classOf cs))
  GSpan1 cs -> let n = length (takeWhile (`elem` cs) inp)
               in if n == 0 then (Nothing, here off (classOf cs))
                  else (Just (off + n, drop n inp), here (off + n) (classOf cs))
  GSeq a b  -> case refExp f a off inp of
                 (Nothing, ia)       -> (Nothing, ia)
                 (Just (o, r), ia)   -> let (rb, ib) = refExp f b o r
                                        in (rb, ia ++ ib)
  GCh a b   -> case refExp f a off inp of
                 (Nothing, ia) -> let (rb, ib) = refExp f b off inp
                                  in (rb, ia ++ ib)
                 r             -> r
  GStar a   -> let go o r acc = case refExp f a o r of
                                  (Nothing, ia)      -> (Just (o, r), acc ++ ia)
                                  (Just (o', r'), ia) -> go o' r' (acc ++ ia)
               in go off inp []
  -- Nothing inside a lookahead is listed; only !. says what it wanted.
  GNot a    -> case refExp f a off inp of
                 (Nothing, _) -> (Just (off, inp), [])
                 _            -> (Nothing, case a of
                                             GAny -> here off ExpEnd
                                             _    -> [])
  GOff      -> (Just (off, inp), [])
  GLabel l a -> let (ra, ia) = refExp f a off inp
                    own | null l                  = []
                        | off == f && not (null ia) = [ExpLabel l]
                        | otherwise               = ia
                in (ra, own)
  where
    here o e = [ e | o == f ]
    char p e = case inp of
      (c : r) | p c -> (Just (off + 1, r), [])
      _             -> (Nothing, here off e)
    classOf cs = case nub cs of
      [c] -> ExpChar c
      _   -> ExpClass (describeCS (fromList cs))

-- | What the input has at an offset, stated directly.
refFound :: String -> Int -> Found
refFound s off = case drop off s of
  []                      -> FoundEnd
  (c : rest) | isWord c   -> FoundToken (c : takeWhile isWord rest)
             | otherwise  -> FoundToken [c]
  where isWord c = isAlphaNum c || c == '_'

-- | Line and column of an offset, stated directly.
refLineCol :: String -> Int -> (Int, Int)
refLineCol s off = (1 + length nls, off - lineStart + 1)
  where
    nls       = [ i | (i, c) <- zip [0 :: Int ..] (take off s), c == '\n' ]
    lineStart = if null nls then 0 else last nls + 1

-- | The same grammar as a 'PExp'.  Each construct is built the way a user or
-- the quasi-quoter would build it, so the specialised cases of the compiler —
-- @'Star' ('Sat' _)@, @'Not' ('Term' _)@ and the rest — are all reached.
toP :: G -> PExp s nt ()
toP g = case g of
  GChar c      -> () <$ Term c
  GSat cs   -> () <$ Sat (fromList cs)
  GAny      -> () <$ AnyChar
  GStr s    -> () <$ Str s
  GSpan cs  -> () <$ Span (fromList cs)
  GSpan1 cs -> () <$ Span1 (fromList cs)
  GSeq a b  -> toP a ~> toP b
  GCh a b   -> toP a .||. toP b
  GStar a   -> () <$ starOf a
  GNot a    -> notOf a
  GOff      -> () <$ GetOffset
  GLabel l a -> Label l (toP a)
  where
    -- Keep the operand bare where the compiler has a case for it.
    starOf (GChar c)    = () <$ Star (Term c)
    starOf (GSat cs) = () <$ Star (Sat (fromList cs))
    starOf GAny      = () <$ Star AnyChar
    starOf a         = () <$ Star (toP a)
    notOf (GChar c)      = Not (Term c)
    notOf (GSat cs)   = Not (Sat (fromList cs))
    notOf GAny        = Not AnyChar
    notOf (GSpan cs)  = Not (Span (fromList cs))
    notOf (GSpan1 cs) = Not (Span1 (fromList cs))
    notOf a           = Not (toP a)

--------------------------------------------------------------------------------
-- Generation
--------------------------------------------------------------------------------

-- | A linear congruential generator: enough to vary the shapes, and the
-- same shapes on every run.
newtype Gen a = Gen { unGen :: Int -> (a, Int) }

instance Functor Gen where
  fmap f (Gen g) = Gen (\s -> let (a, s') = g s in (f a, s'))
instance Applicative Gen where
  pure a = Gen (\s -> (a, s))
  Gen f <*> Gen g = Gen (\s -> let (h, s1) = f s; (a, s2) = g s1 in (h a, s2))
instance Monad Gen where
  Gen g >>= k = Gen (\s -> let (a, s1) = g s in unGen (k a) s1)

choose :: Int -> Gen Int
choose n = Gen (\s -> let s' = (s * 1103515245 + 12345) `mod` 2147483648
                      in ((s' `div` 65536) `mod` n, s'))

pick :: [a] -> Gen a
pick xs = (xs !!) <$> choose (length xs)

alphabet :: [Char]
alphabet = "ab\n\t"

klass :: Gen [Char]
klass = do
  n <- (+ 1) <$> choose 2
  mapM (const (pick alphabet)) [1 .. n]

-- | A grammar of at most the given depth.  @consuming@ asks for one that
-- cannot match the empty string, which is what a repetition needs.
grammar :: Bool -> Int -> Gen G
grammar consuming d
  | d <= 0    = leaf
  | otherwise = do
      k <- choose 10
      case k of
        0 -> GSeq <$> grammar consuming (d - 1) <*> grammar False (d - 1)
        1 -> GSeq <$> grammar False (d - 1) <*> grammar consuming (d - 1)
        2 -> GCh <$> grammar consuming (d - 1) <*> grammar consuming (d - 1)
        3 | not consuming -> GStar <$> grammar True (d - 1)
        4 | not consuming -> GNot <$> grammar False (d - 1)
        5 | not consuming -> pure GOff
        6 -> GLabel <$> pick ["", "L1", "L2"] <*> grammar consuming (d - 1)
        _ -> leaf
  where
    leaf = do
      k <- choose (if consuming then 5 else 6)
      case k of
        0 -> GChar <$> pick alphabet
        1 -> GSat <$> klass
        2 -> pure GAny
        3 -> do n <- (+ 1) <$> choose 3
                GStr <$> mapM (const (pick alphabet)) [1 .. n]
        4 -> GSpan1 <$> klass
        _ -> GSpan <$> klass

input :: Gen String
input = do
  n <- choose 9
  mapM (const (pick alphabet)) [1 .. n]

-- | What the reference says a parse of the whole grammar returns.
expected :: G -> String -> Result String ()
expected g s = case ref g 0 0 s of
  Left f           -> let (l, c) = refLineCol s f
                      in Fail (ParseError l c f (refFound s f)
                                          (nub (snd (refExp f g 0 s))))
  Right (_, o, r)  -> OK () (take o s) r

-- | One generated grammar and input, over every stream, with and without
-- layout.  Under @>=@ from the full candidate interval every column is
-- acceptable, so the answer is the same, but the slow paths are taken.
agrees :: G -> String -> [String]
agrees g s =
  [ name ++ ": " ++ show g ++ " on " ++ show s ++ ": expected "
      ++ show want ++ ", got " ++ got
  | (name, got) <- runs
  , got /= show want ]
  where
    want   = expected g s
    gr     :: Stream s => Grammar s (InEnv '[]) ()
    gr     = Grammar RNil (toP g)
    layout = defaultOpts { optTokenMode = relD geR }
    shown :: Result String () -> String
    shown = show
    runs =
      [ ("String",          shown (parse gr s))
      , ("String/layout",   shown (parseWith layout gr s))
      , ("Text",            textAsString (parse gr (T.pack s)))
      , ("Text/layout",     textAsString (parseWith layout gr (T.pack s)))
      , ("ByteString",      bsAsString (parse gr (BC.pack s)))
      , ("ByteString/layout", bsAsString (parseWith layout gr (BC.pack s)))
      ]
    textAsString (OK a c r) = shown (OK a (T.unpack c) (T.unpack r))
    textAsString (Fail e)   = shown (Fail e)
    bsAsString (OK a c r)   = shown (OK a (BC.unpack c) (BC.unpack r))
    bsAsString (Fail e)     = shown (Fail e)

main :: IO ()
main = do
  let bad = [ n | (n, ok) <- cases, not ok ]
  mapM_ (putStrLn . ("FAILED: " ++)) bad
  putStrLn ("hand-picked: " ++ show (length cases - length bad) ++ " of "
              ++ show (length cases) ++ " pass")

  let samples = fst (unGen (mapM (const ((,) <$> grammar False 4 <*> input))
                                  [1 .. 3000 :: Int]) 42)
      problems = concatMap (uncurry agrees) samples
      fails    = length [ () | (g, s) <- samples
                             , Fail _ <- [expected g s] ]
  mapM_ putStrLn (take 5 problems)
  labelBad <- labelErrors
  mapM_ putStrLn labelBad
  putStrLn ("%label errors at the splice: " ++ show (3 - length labelBad)
              ++ " of 3 reported")
  putStrLn ("generated: " ++ show (length samples) ++ " grammars ("
              ++ show fails ++ " failing parses), "
              ++ show (length problems) ++ " disagreements with the reference")

  unless (null bad && null problems && null labelBad) exitFailure
