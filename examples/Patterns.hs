{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE QuasiQuotes           #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE TypeOperators         #-}

-- | Worked examples for @peg-patterns.md@.
--
-- Every snippet quoted in that document appears here, so the document cannot
-- drift away from code that compiles.  'patternsMain' exercises each one.
module Patterns
  ( Expr (..)
  , Asgn (..)
  , evalE
  , ws, lexeme, keyword, eof, fully
  , calc
  , addOp
  , kwG
  , prog
  , Loc (..), Stmt (..), LExpr (..)
  , located
  , undefinedVars
  , patternsMain
  ) where

import PEG
import PEG.QQ (pegExpr, pegGrammar, pegRules)

--------------------------------------------------------------------------------
-- Pattern 2a/2bi: whitespace and token combinators, at the PExp level
--------------------------------------------------------------------------------

-- | Zero or more layout characters.  A character class, so this compiles to a
-- single 'Span' node and returns a chunk of the input.
ws :: PExp s env s
ws = spanOf (fromRanges [(' ', ' '), ('\t', '\t'), ('\r', '\r'), ('\n', '\n')])

-- | Run @p@, then consume /trailing/ whitespace only.
--
-- A combinator over expressions is an ordinary polymorphic function.  It did
-- not use to be: when a 'PExp' carried its nullability and FIRST set in a
-- fourth index, this had to be written
--
-- @
-- lexeme :: PExp s env ty a -> PExp s env (SeqTy ty ('MkTy 'True '[])) a
-- @
--
-- and every combinator built on it had to restate the nesting exactly.  See
-- "PEG.Type" for where those indices went.
lexeme :: PExp s env a -> PExp s env a
lexeme p = (\x _ -> x) <$>. p <*>. ws

-- | End of input: nothing can follow.
eof :: PExp s env ()
eof = Not AnyChar

-- | Leading whitespace, then @p@, then end of input.
fully :: PExp s env a -> PExp s env a
fully p = (\_ x _ -> x) <$>. ws <*>. p <*>. eof

--------------------------------------------------------------------------------
-- Pattern 2bii: keyword combinator
--------------------------------------------------------------------------------

identCont :: CharSet
identCont = fromRanges [('a', 'z'), ('A', 'Z'), ('0', '9'), ('_', '_')]

-- | Match a keyword that is not a prefix of a longer identifier.
--
-- The negative lookahead is the whole pattern: @keyword "negate"@ fails on
-- @negatex@ because an identifier character follows.  In a backtracking
-- combinator library this needs @try@; in a PEG it is just @!@.
keyword :: String -> PExp s env ()
keyword k = (\_ _ -> ()) <$>. stringNE k <*>. Not (sat identCont)

--------------------------------------------------------------------------------
-- The AST, one layer per precedence level (Pattern 1b)
--------------------------------------------------------------------------------

data Expr
  = Add Expr Expr
  | Sub Expr Expr
  | Mul Expr Expr
  | Div Expr Expr
  | Neg Expr
  | Num Int
  | Var String
  deriving (Eq, Show)

data Asgn = Asgn String Expr
  deriving (Eq, Show)

evalE :: [(String, Int)] -> Expr -> Int
evalE g (Add a b) = evalE g a + evalE g b
evalE g (Sub a b) = evalE g a - evalE g b
evalE g (Mul a b) = evalE g a * evalE g b
evalE g (Div a b) = let d = evalE g b in if d == 0 then 0 else evalE g a `div` d
evalE g (Neg a)   = negate (evalE g a)
evalE _ (Num n)   = n
evalE g (Var v)   = maybe 0 id (lookup v g)

--------------------------------------------------------------------------------
-- Pattern 3a: lifted constructors
--
-- The semantic actions stay one application wide; the dispatch on which
-- constructor an operator denotes lives in ordinary Haskell.
--------------------------------------------------------------------------------

-- | Fold a left-associative chain: an operand followed by @(op, operand)@
-- pairs.  This is what @chainl1@ buys in a combinator library, written out.
chainl :: Expr -> [(Char, Expr)] -> Expr
chainl = foldl step
  where
    step l ('+', r) = Add l r
    step l ('-', r) = Sub l r
    step l ('*', r) = Mul l r
    step l ('/', r) = Div l r
    step _ (c  , _) = error ("chainl: unexpected operator " ++ show c)

mkNum :: Stream s => s -> Expr
mkNum = Num . read . chunkToString

mkVar :: Stream s => s -> Expr
mkVar = Var . chunkToString

mkAsgn :: Stream s => s -> Expr -> Asgn
mkAsgn v e = Asgn (chunkToString v) e

--------------------------------------------------------------------------------
-- Pattern 1a/1c: a precedence ladder, one rule per level
--------------------------------------------------------------------------------

type CalcEnv s =
  '[ '("expr" , 'EnvEntry Expr)
   , '("term" , 'EnvEntry Expr)
   , '("unary", 'EnvEntry Expr)
   , '("atom" , 'EnvEntry Expr)
   ]

-- | The classic expression language.
--
-- Note what is /not/ here: no @try@, no left recursion, and no rule that can
-- loop.  @expr <- expr '+' term@ would be rejected by 'PEG.Analysis' when the
-- @pegRules@ block below is spliced, naming @expr@ and the cycle.
calc :: Stream s => Grammar s (InEnv (CalcEnv s)) Expr
calc =
  Grammar
    [pegRules|
       expr  <- t:term  ts:(o:[+-] u:term)*  { chainl t ts }
       term  <- f:unary fs:(o:[*/] g:unary)* { chainl f fs }
       unary <- '-' e:unary                  { Neg e }
              / a:atom
       atom  <- '(' e:expr ')'
              / ds:[0-9]+                    { mkNum ds }
              / &[a-zA-Z_] cs:[a-zA-Z0-9_]+  { mkVar cs }
    |]
    (nt @"expr")

-- | The same pattern inside a quasi-quoted grammar: a string literal followed
-- by a negative lookahead on the identifier-continuation class.
type KwEnv = '[ '("kw", 'EnvEntry String) ]

kwG :: Stream s => Grammar s (InEnv KwEnv) String
kwG = Grammar [pegRules| kw <- k:"negate" ![a-zA-Z0-9_]  { k } |] (nt @"kw")

--------------------------------------------------------------------------------
-- Pattern 3b: deferred constructors
--
-- A rule may return a *function*, so the choice of constructor is made where
-- the operator is read and applied where the operands are known.  This is the
-- defunctionalised chain the paper describes, and it removes the partial
-- 'error' case from 'chainl' above.
--------------------------------------------------------------------------------

type OpEnv =
  '[ '("op", 'EnvEntry (Expr -> Expr -> Expr)) ]

addOp :: Stream s => Grammar s (InEnv OpEnv) (Expr -> Expr -> Expr)
addOp = Grammar [pegRules| op <- '+' { Add } / '-' { Sub } |] (nt @"op")

--------------------------------------------------------------------------------
-- Pattern 3b, continued: source positions
--
-- @\@@ consumes nothing and returns the offset of the current position.  A
-- label on it hands that offset to the action, and the 'LineIndex' passed in
-- as a parameter turns it into a line and a column.
--------------------------------------------------------------------------------

-- | A line and a column, both from 1.
data Loc = Loc Int Int
  deriving Eq

instance Show Loc where
  show (Loc l c) = show l ++ ":" ++ show c

data Stmt
  = Assign Loc Loc String LExpr   -- ^ where the statement starts and ends
  | Print  Loc LExpr
  deriving (Eq, Show)

data LExpr
  = LNum Loc Int
  | LVar Loc String
  | LAdd LExpr LExpr
  deriving (Eq, Show)

-- | The lifted constructor of §3.1, for positions: an offset becomes a 'Loc'
-- here, not in the action.
at :: LineIndex -> Int -> Loc
at idx = uncurry Loc . lineCol idx

-- | Each @p:\@@ sits /before/ the token it locates and after the whitespace
-- the previous token consumed (§2.1), so it is the token's first character.
-- An @\@@ after the last token of a statement gives where it ends.
[pegGrammar|
  %name   located
  %stream String
  %param  idx :: LineIndex
  %start  prog
  %label  atom "an operand"
  %label  name "a name"
  %label  ws   ""

  prog :: [Stmt] <- ws ss:stmt* !.                         { ss }
  stmt :: Stmt   <- p:@ "print" ![a-z] ws e:expr ';' ws    { Print (at idx p) e }
                 /  p:@ v:name ":=" ws e:expr ';' r:@ ws
                                       { Assign (at idx p) (at idx r) v e }
  expr :: LExpr  <- t:atom ts:('+' ws u:atom)*             { foldl LAdd t ts }
  atom :: LExpr  <- p:@ ds:[0-9]+ ws                       { LNum (at idx p) (read ds) }
                 /  p:@ v:name                             { LVar (at idx p) v }
  name :: String <- cs:[a-z]+ ws                           { cs }
  ws   :: ()     <- [ \t\n]*                               { () }
|]

-- | Every use of a variable before it is assigned, reported where it occurs.
undefinedVars :: [Stmt] -> [String]
undefinedVars = go []
  where
    go _ [] = []
    go env (Assign _ _ v e : ss) = uses env e ++ go (v : env) ss
    go env (Print _ e      : ss) = uses env e ++ go env ss

    uses env (LVar l v) | v `notElem` env = [show l ++ ": " ++ v ++ " is not defined"]
    uses env (LAdd a b) = uses env a ++ uses env b
    uses _   _          = []

--------------------------------------------------------------------------------
-- §4: errors.  A failed parse is reported at the furthest point it reached;
-- an error production turns a failure into a node, so that the parse goes on
-- and every error is reported, each with a message of its own.
--------------------------------------------------------------------------------

-- | 'located', with an alternative that catches a statement it cannot parse.
-- The catch-all comes last and consumes up to the next @;@, which is where
-- parsing resumes.
[pegGrammar|
  %name   recovering
  %stream String
  %param  idx :: LineIndex
  %start  prog

  prog :: [Either String Stmt] <- ws ss:stmt* !.          { ss }
  stmt :: Either String Stmt
       <- p:@ v:name ":=" ws res:(e:expr ';' r:@ ws { Right (e, r) }
                                 / q:@ skip         { Left q })
            { either (\q -> Left (show (at idx q) ++ ": expected an expression"))
                     (\(e, r) -> Right (Assign (at idx p) (at idx r) v e)) res }
        / q:@ skip                     { Left (show (at idx q) ++ ": expected a statement") }
  skip :: ()     <- [^;]* ';' ws                           { () }
  expr :: LExpr  <- t:atom ts:('+' ws u:atom)*             { foldl LAdd t ts }
  atom :: LExpr  <- p:@ ds:[0-9]+ ws                       { LNum (at idx p) (read ds) }
                 /  p:@ v:name                             { LVar (at idx p) v }
  name :: String <- cs:[a-z]+ ws                           { cs }
  ws   :: ()     <- [ \t\n]*                               { () }
|]

--------------------------------------------------------------------------------
-- Statements, to show ordered choice and the lexeme discipline
--------------------------------------------------------------------------------

type ProgEnv s =
  '[ '("prog" , 'EnvEntry [Asgn])
   , '("asgn" , 'EnvEntry Asgn)
   , '("expr" , 'EnvEntry Expr)
   , '("term" , 'EnvEntry Expr)
   , '("unary", 'EnvEntry Expr)
   , '("atom" , 'EnvEntry Expr)
   ]

-- | @a := 1; b := a * 2@
--
-- @':='@ comes before @':'@ nowhere in this grammar, but the ordering rule it
-- illustrates is the one PEG newcomers get wrong: in an ordered choice the
-- longer alternative must come first, because the first success wins and
-- there is no backtracking into a committed branch.
prog :: Stream s => Grammar s (InEnv (ProgEnv s)) [Asgn]
prog =
  Grammar
    [pegRules|
       prog  <- a:asgn as:(';' b:asgn)*      { a : as }
       asgn  <- &[a-zA-Z_] v:[a-zA-Z0-9_]+ ":=" e:expr  { mkAsgn v e }

       expr  <- t:term  ts:(o:[+-] u:term)*  { chainl t ts }
       term  <- f:unary fs:(o:[*/] g:unary)* { chainl f fs }
       unary <- '-' e:unary                  { Neg e }
              / a:atom
       atom  <- '(' e:expr ')'
              / ds:[0-9]+                    { mkNum ds }
              / &[a-zA-Z_] cs:[a-zA-Z0-9_]+  { mkVar cs }
    |]
    (nt @"prog")

--------------------------------------------------------------------------------
-- Demonstration
--------------------------------------------------------------------------------

showR :: Show a => Result String a -> String
showR (OK a _ r) = "OK " ++ show a ++ (if null r then "" else " rest=" ++ show r)
showR (Fail e)   = "Fail " ++ showErr e

-- | Where a parse failed, as @line:column@.
showErr :: ParseError -> String
showErr e = show (errLine e) ++ ":" ++ show (errColumn e)

patternsMain :: IO ()
patternsMain = do
  putStrLn "### precedence ladder"
  mapM_ (\s -> putStrLn (show s ++ " => " ++ show (fmap' (evalE []) (parse calc s))))
    [ "1+2*3", "(1+2)*3", "2*3+4", "-3+4", "10/2/5", "1-2-3", "x" ]

  putStrLn "### ordered choice / statements"
  mapM_ (\s -> putStrLn (show s ++ " => " ++ showR (parse prog s)))
    [ "a:=1", "a:=1;b:=a*2", "a:=", "a:=1;" ]

  putStrLn "### keyword vs bare literal"
  -- No 'fully' here: the point is what each one leaves behind.
  let kw   = parse (Grammar RNil (keyword "negate"))
               :: String -> Result String ()
      bare = parse (Grammar RNil (const () <$>. stringNE "negate"))
               :: String -> Result String ()
  mapM_ (\s -> putStrLn (show s ++ " keyword => " ++ showR (kw s)
                           ++ " | bare => " ++ showR (bare s)))
    [ "negate", "negatex", "negate2", "negate x" ]

  putStrLn "### keyword, in quasi-quoter syntax"
  mapM_ (\s -> putStrLn (show s ++ " => " ++ showR (parse kwG s)))
    [ "negate", "negatex", "negate x" ]

  putStrLn "### deferred constructor: a rule returning a function"
  mapM_ (\s -> putStrLn (show s ++ " => " ++
          case parse addOp s of
            OK f _ _ -> show (f (Num 1) (Num 2))
            Fail e   -> "Fail " ++ showErr e))
    [ "+", "-", "*" ]

  putStrLn "### source positions"
  let src = "x := 1;\nprint x + y;\n  y := x+\n    2;\nprint z;\n"
  case parse (located (lineIndex src)) src of
    OK ss _ _ -> do mapM_ print ss
                    mapM_ putStrLn (undefinedVars ss)
    Fail e    -> putStrLn ("Fail " ++ showErr e)

  putStrLn "### syntax errors"
  let bad = "x := 1;\ny := 2 + ;\n42;\nz := y;\n"
  putStrLn (showR (parse (located (lineIndex bad)) bad))
  case parse (located (lineIndex bad)) bad of
    Fail e -> putStrLn (renderParseError e)
    OK{}   -> pure ()
  case parse (recovering (lineIndex bad)) bad of
    OK rs _ _ -> mapM_ (putStrLn . either id show) rs
    Fail e    -> putStrLn ("Fail " ++ showErr e)

  putStrLn "### lexeme discipline: fully (lexeme p)"
  let toks = parse (Grammar RNil (fully (lexeme [pegExpr| ds:[0-9]+ |])))
               :: String -> Result String String
  mapM_ (\s -> putStrLn (show s ++ " => " ++ showR (toks s)))
    [ "12", "  12  ", "12 x", "" ]
  where
    fmap' f (OK a _ _) = Just (f a)
    fmap' _ (Fail _)   = Nothing
