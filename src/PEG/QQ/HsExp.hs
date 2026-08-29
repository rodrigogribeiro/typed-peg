{-# LANGUAGE TemplateHaskell #-}

-- | Internal parser for Haskell expressions embedded in quasi-quoter actions.
--
-- 'parseHsExp' parses a subset of Haskell 2010 expressions sufficient to
-- handle the @{ expr }@ action blocks in 'PEG.QQ.pegRules'.
-- It is implemented without any external parsing library and depends only on
-- @base@ and @template-haskell@.
module PEG.QQ.HsExp
  ( parseHsExp
  ) where

import Data.Char           (isAlpha, isAlphaNum, isDigit, isHexDigit,
                            isOctDigit, isSpace, isUpper)
import qualified Language.Haskell.TH as TH
import Language.Haskell.TH (Body (..), Clause (..), Dec (..), Exp (..),
                            Lit (..), Match (..), Pat (..), Range (..),
                            Stmt (..), Type (..), mkName, tupleDataName,
                            tupleTypeName)

data Tok
  = TVar    String
  | TCon    String
  | TVarSym String
  | TConSym String
  | TInt    Integer
  | TRat    Rational
  | TChar   Char
  | TStr    String
  | TPunc   String
  | TRes    String
  deriving (Eq, Show)

showTok :: Tok -> String
showTok t = case t of
  TVar    s -> s
  TCon    s -> s
  TVarSym s -> s
  TConSym s -> s
  TInt    n -> show n
  TRat    r -> show (fromRational r :: Double)
  TChar   c -> show c
  TStr    s -> show s
  TPunc   s -> s
  TRes    s -> s

atTok :: [Tok] -> String
atTok []      = "at the end of the action"
atTok (t : _) = "at " ++ show (showTok t)

symChars :: String
symChars = "!#$%&*+./<=>?@\\^|-~:"

reservedOps :: [String]
reservedOps = ["..", "::", "=", "\\", "|", "<-", "->", "@", "~", "=>"]

reservedIds :: [String]
reservedIds =
  [ "case", "class", "data", "default", "deriving", "do", "else"
  , "foreign", "if", "import", "in", "infix", "infixl", "infixr"
  , "instance", "let", "module", "newtype", "of", "then", "type"
  , "where", "_"
  ]

lexHs :: String -> Either String [Tok]
lexHs = go
  where
    go [] = Right []

    go s@(c : cs)
      | isSpace c = go cs
      | c == '{', ('-' : cs') <- cs = skipBlock (1 :: Int) cs' >>= go
      | c == '\'' = lexChar s
      | c == '"'  = lexString s
      | isDigit c = lexNumber s
      | isAlpha c || c == '_' = lexIdent s
      | c == '`' = lexBacktick cs
      | c `elem` "()[],;{}" = (TPunc [c] :) <$> go cs
      | c `elem` symChars =
          let (sym, rest) = span (`elem` symChars) s
          in if all (== '-') sym && length sym >= 2
               then go (dropWhile (/= '\n') rest)
               else (classifySym sym :) <$> go rest
      | otherwise = Left ("unexpected character " ++ show c ++ " in action")

    skipBlock :: Int -> String -> Either String String
    skipBlock 0 s               = Right s
    skipBlock _ []              = Left "unterminated {- -} comment in action"
    skipBlock n ('-' : '}' : s) = skipBlock (n - 1) s
    skipBlock n ('{' : '-' : s) = skipBlock (n + 1) s
    skipBlock n (_ : s)         = skipBlock n s

    lexChar s = case reads s :: [(Char, String)] of
      [(ch, rest)] -> (TChar ch :) <$> go rest
      _            -> Left ("malformed character literal in action: "
                              ++ show (take 10 s))

    lexString s = case reads s :: [(String, String)] of
      [(str, rest)] -> (TStr str :) <$> go rest
      _             -> Left ("malformed string literal in action: "
                               ++ show (take 10 s))

    lexIdent s =
      let (name, rest) = spanIdent s
      in case rest of
           ('.' : c' : _) | startsUpper name
                          , isAlpha c' || c' == '_' ->
             let (rest', qual) = lexQual name (drop 1 rest)
             in (qual :) <$> go rest'
           ('.' : c' : _) | startsUpper name
                          , c' `elem` symChars ->
             let (sym, rest') = span (`elem` symChars) (drop 1 rest)
             in (classifyQualSym name sym :) <$> go rest'
           _ | name `elem` reservedIds -> (TRes name :) <$> go rest
             | startsUpper name        -> (TCon name :) <$> go rest
             | otherwise               -> (TVar name :) <$> go rest

    lexQual acc s =
      let (name, rest) = spanIdent s
          acc'         = acc ++ "." ++ name
      in case rest of
           ('.' : c' : _) | startsUpper name
                          , isAlpha c' || c' == '_' -> lexQual acc' (drop 1 rest)
           _ | startsUpper name -> (rest, TCon acc')
             | otherwise           -> (rest, TVar acc')

    lexBacktick s =
      let (name, rest) = spanIdent s
      in case rest of
           ('`' : rest')
             | null name -> Left "empty backticked operator in action"
             | startsUpper name -> (TConSym name :) <$> go rest'
             | otherwise           -> (TVarSym name :) <$> go rest'
           _ -> Left "unterminated backticked operator in action"

    classifySym sym
      | sym `elem` reservedOps = TRes sym
      | take 1 sym == ":"      = TConSym sym
      | otherwise              = TVarSym sym

    classifyQualSym m sym
      | take 1 sym == ":" = TConSym (m ++ "." ++ sym)
      | otherwise         = TVarSym (m ++ "." ++ sym)

    lexNumber s =
      case s of
        ('0' : x : rest) | x `elem` "xX", (ds, r) <- span isHexDigit rest, not (null ds) ->
          (TInt (readBase 16 ds) :) <$> go r
        ('0' : o : rest) | o `elem` "oO", (ds, r) <- span isOctDigit rest, not (null ds) ->
          (TInt (readBase 8 ds) :) <$> go r
        ('0' : b : rest) | b `elem` "bB", (ds, r) <- span (`elem` "01") rest, not (null ds) ->
          (TInt (readBase 2 ds) :) <$> go r
        _ ->
          let (whole, r1) = span isDigit s
          in case r1 of
               ('.' : d : _) | isDigit d ->
                 let (frac, r2) = span isDigit (drop 1 r1)
                     (expo, r3) = lexExponent r2
                 in (TRat (mkRat whole frac (maybe 0 id expo)) :) <$> go r3
               _ | (Just expo, r2) <- lexExponent r1 ->
                     (TRat (mkRat whole "" expo) :) <$> go r2
                 | otherwise -> (TInt (read whole) :) <$> go r1

    mkRat whole frac expo =
      let mantissa = read (whole ++ frac) :: Integer
          scale    = expo - toInteger (length frac)
      in if scale >= 0
           then toRational (mantissa * 10 ^ scale)
           else toRational mantissa / toRational (10 ^ negate scale :: Integer)

    lexExponent s@(e : rest)
      | e `elem` "eE" =
          case rest of
            ('+' : ds) | (n@(_ : _), r) <- span isDigit ds -> (Just (read n), r)
            ('-' : ds) | (n@(_ : _), r) <- span isDigit ds -> (Just (negate (read n)), r)
            _ | (n@(_ : _), r) <- span isDigit rest -> (Just (read n), r)
            _ -> (Nothing, s)
    lexExponent s = (Nothing, s)

    readBase :: Integer -> String -> Integer
    readBase b = foldl (\acc d -> acc * b + toInteger (digitVal d)) 0

    digitVal d
      | isDigit d = fromEnum d - fromEnum '0'
      | otherwise = 10 + fromEnum (toLowerAscii d) - fromEnum 'a'

    toLowerAscii ch
      | ch >= 'A' && ch <= 'Z' = toEnum (fromEnum ch + 32)
      | otherwise              = ch

startsUpper :: String -> Bool
startsUpper (c : _) = isUpper c
startsUpper []      = False

spanIdent :: String -> (String, String)
spanIdent s =
  let (c, cs) = splitAt 1 s
      (n, r)  = span (\x -> isAlphaNum x || x == '_' || x == '\'') cs
  in (c ++ n, r)

type P a = [Tok] -> Either String (a, [Tok])

parseHsExp :: String -> Either String Exp
parseHsExp src = do
  toks <- lexHs src
  case toks of
    [] -> Left "empty semantic action"
    _  -> do
      (e, rest) <- pExp toks
      case rest of
        [] -> Right e
        _  -> Left ("unconsumed input in action " ++ atTok rest)

pExp :: P Exp
pExp toks = do
  (e, mop, rest) <- pOpChain toks
  case mop of
    Just op -> Left ("dangling operator " ++ show (pprExp op) ++ " in action")
    Nothing -> case rest of
      (TRes "::" : rest') -> do
        (ty, rest'') <- pType rest'
        Right (SigE e ty, rest'')
      _ -> Right (e, rest)

pOpChain :: [Tok] -> Either String (Exp, Maybe Exp, [Tok])
pOpChain toks = do
  (e, rest) <- pOperand toks
  go [e] [] rest
  where
    go operands ops rest = case rest of
      (t : rest') | Just op <- opExpOf t ->
        if startsOperand rest'
          then do
            (e', rest'') <- pOperand rest'
            go (e' : operands) (op : ops) rest''
          else Right (build (reverse operands) (reverse ops), Just op, rest')
      _ -> Right (build (reverse operands) (reverse ops), Nothing, rest)

    build [e]           _          = e
    build (e : es)      (op : ops) = UInfixE e op (build es ops)
    build _             _          = error "PEG.QQ.HsExp: impossible operator chain"

opExpOf :: Tok -> Maybe Exp
opExpOf (TVarSym s) = Just (VarE (mkName s))
opExpOf (TConSym s) = Just (ConE (mkName s))
opExpOf _           = Nothing

pOperand :: P Exp
pOperand (TVarSym "-" : rest) = do
  (e, rest') <- pOperand rest
  Right (AppE (VarE 'negate) e, rest')
pOperand toks@(TRes "\\" : _)   = pLambda toks
pOperand toks@(TRes "let" : _)  = pLet toks
pOperand toks@(TRes "if" : _)   = pIf toks
pOperand toks@(TRes "case" : _) = pCase toks
pOperand (TRes "do" : _) =
  Left "'do' notation is not supported in a semantic action"
pOperand (TRes "where" : _) =
  Left "'where' is not supported in a semantic action; use 'let ... in' instead"
pOperand toks = pApp toks

startsOperand :: [Tok] -> Bool
startsOperand []      = False
startsOperand (t : _) = case t of
  TVarSym "-" -> True
  TRes r      -> r `elem` ["\\", "let", "if", "case"]
  _           -> startsAExp t

startsAExp :: Tok -> Bool
startsAExp t = case t of
  TVar  _   -> True
  TCon  _   -> True
  TInt  _   -> True
  TRat  _   -> True
  TChar _   -> True
  TStr  _   -> True
  TPunc "(" -> True
  TPunc "[" -> True
  _         -> False

pApp :: P Exp
pApp toks = do
  (f, rest) <- pAExp toks
  go f rest
  where
    go acc rest@(t : _) | startsAExp t = do
      (x, rest') <- pAExp rest
      go (AppE acc x) rest'
    go acc rest = Right (acc, rest)

pAExp :: P Exp
pAExp (TVar  s : rest) = Right (VarE (mkName s), rest)
pAExp (TCon  s : rest) = Right (ConE (mkName s), rest)
pAExp (TInt  n : rest) = Right (LitE (IntegerL n), rest)
pAExp (TRat  r : rest) = Right (LitE (RationalL r), rest)
pAExp (TChar c : rest) = Right (LitE (CharL c), rest)
pAExp (TStr  s : rest) = Right (LitE (StringL s), rest)
pAExp (TPunc "(" : rest) = pParen rest
pAExp (TPunc "[" : rest) = pBracket rest
pAExp toks = Left ("expected an expression " ++ atTok toks)

pParen :: P Exp
pParen (TPunc ")" : rest) = Right (ConE '(), rest)
pParen toks@(TPunc "," : _) =
  let (commas, rest) = span (== TPunc ",") toks
  in case rest of
       (TPunc ")" : rest') -> Right (ConE (tupleDataName (length commas + 1)), rest')
       _ -> Left ("expected ')' after a tuple constructor " ++ atTok rest)
pParen (t : rest)
  | Just op <- opExpOf t
  , t /= TVarSym "-" =
      case rest of
        (TPunc ")" : rest') -> Right (op, rest')
        _ -> do
          (e, rest') <- pExp rest
          rest'' <- expect (TPunc ")") rest'
          Right (InfixE Nothing op (Just e), rest'')
pParen toks = do
  (e, mop, rest) <- pOpChain toks
  case mop of
    Just op -> do
      rest' <- expect (TPunc ")") rest
      Right (InfixE (Just e) op Nothing, rest')
    Nothing -> case rest of
      (TRes "::" : rest') -> do
        (ty, rest'') <- pType rest'
        rest''' <- expect (TPunc ")") rest''
        Right (ParensE (SigE e ty), rest''')
      (TPunc ")" : rest') -> Right (ParensE e, rest')
      (TPunc "," : _)     -> do
        (es, rest') <- pCommaList pExp rest
        rest'' <- expect (TPunc ")") rest'
        Right (TupE (map Just (e : es)), rest'')
      _ -> Left ("expected ')' or ',' " ++ atTok rest)

pBracket :: P Exp
pBracket (TPunc "]" : rest) = Right (ListE [], rest)
pBracket toks = do
  (e, rest) <- pExp toks
  case rest of
    (TPunc "]" : rest') -> Right (ListE [e], rest')
    (TRes ".." : rest') -> case rest' of
      (TPunc "]" : rest'') -> Right (ArithSeqE (FromR e), rest'')
      _ -> do
        (hi, rest'') <- pExp rest'
        rest''' <- expect (TPunc "]") rest''
        Right (ArithSeqE (FromToR e hi), rest''')
    (TRes "|" : rest') -> do
      (quals, rest'') <- pCommaList1 pQual rest'
      rest''' <- expect (TPunc "]") rest''
      Right (CompE (quals ++ [NoBindS e]), rest''')
    (TPunc "," : rest') -> do
      (e2, rest'') <- pExp rest'
      case rest'' of
        (TRes ".." : rest''') -> case rest''' of
          (TPunc "]" : r) -> Right (ArithSeqE (FromThenR e e2), r)
          _ -> do
            (hi, r) <- pExp rest'''
            r' <- expect (TPunc "]") r
            Right (ArithSeqE (FromThenToR e e2 hi), r')
        (TPunc "]" : r) -> Right (ListE [e, e2], r)
        (TPunc "," : r) -> do
          (es, r') <- pCommaList pExp r
          r'' <- expect (TPunc "]") r'
          Right (ListE (e : e2 : es), r'')
        _ -> Left ("expected ']' or ',' in a list " ++ atTok rest'')
    _ -> Left ("expected ']' " ++ atTok rest)

pQual :: P Stmt
pQual (TRes "let" : rest) = do
  (ds, rest') <- pDecls rest
  Right (LetS ds, rest')
pQual toks =
  case pPat toks of
    Right (p, TRes "<-" : rest) -> do
      (e, rest') <- pExp rest
      Right (BindS p e, rest')
    _ -> do
      (e, rest) <- pExp toks
      Right (NoBindS e, rest)

pLambda :: P Exp
pLambda (TRes "\\" : rest) = do
  (ps, rest') <- pApats rest
  case ps of
    [] -> Left "a lambda needs at least one argument"
    _  -> do
      rest'' <- expect (TRes "->") rest'
      (e, rest''') <- pExp rest''
      Right (LamE ps e, rest''')
pLambda toks = Left ("expected a lambda " ++ atTok toks)

pIf :: P Exp
pIf (TRes "if" : rest) = do
  (c, rest1) <- pExp rest
  rest2      <- expect (TRes "then") rest1
  (t, rest3) <- pExp rest2
  rest4      <- expect (TRes "else") rest3
  (e, rest5) <- pExp rest4
  Right (CondE c t e, rest5)
pIf toks = Left ("expected 'if' " ++ atTok toks)

pLet :: P Exp
pLet (TRes "let" : rest) = do
  (ds, rest') <- pDecls rest
  rest''      <- expect (TRes "in") rest'
  (e, rest''') <- pExp rest''
  Right (LetE ds e, rest''')
pLet toks = Left ("expected 'let' " ++ atTok toks)

pCase :: P Exp
pCase (TRes "case" : rest) = do
  (scrut, rest1) <- pExp rest
  rest2 <- expect (TRes "of") rest1
  case rest2 of
    (TPunc "{" : rest3) -> do
      (alts, rest4) <- pSemiList pAlt rest3
      rest5 <- expect (TPunc "}") rest4
      Right (CaseE scrut alts, rest5)
    _ -> Left "'case' inside a semantic action needs explicit braces"
pCase toks = Left ("expected 'case' " ++ atTok toks)

pAlt :: P Match
pAlt toks = do
  (p, rest)   <- pPat toks
  rest'       <- expect (TRes "->") rest
  (e, rest'') <- pExp rest'
  Right (Match p (NormalB e) [], rest'')

pDecls :: P [Dec]
pDecls (TPunc "{" : rest) = do
  (ds, rest') <- pSemiList pDecl rest
  rest'' <- expect (TPunc "}") rest'
  Right (ds, rest'')
pDecls toks = pSemiList pDecl toks

pDecl :: P Dec
pDecl (TVar f : rest) = do
  (ps, rest') <- pApats rest
  case rest' of
    (TRes "=" : rest'') -> do
      (e, rest''') <- pExp rest''
      Right ( if null ps
                then ValD (VarP (mkName f)) (NormalB e) []
                else FunD (mkName f) [Clause ps (NormalB e) []]
            , rest''' )
    _ -> Left ("expected '=' in a let binding " ++ atTok rest')
pDecl toks = do
  (p, rest) <- pPat toks
  rest'     <- expect (TRes "=") rest
  (e, rest'') <- pExp rest'
  Right (ValD p (NormalB e) [], rest'')

pPat :: P Pat
pPat toks = do
  (p, rest) <- pPat10
  go p rest
  where
    pPat10 = case toks of
      (TCon c : rest) -> do
        (ps, rest') <- pApats rest
        Right (if null ps then ConP (mkName c) [] [] else ConP (mkName c) [] ps, rest')
      _ -> pApat toks

    go p (TConSym op : rest) = do
      (q, rest') <- pPat rest
      Right (UInfixP p (mkName op) q, rest')
    go p rest = Right (p, rest)

pApats :: P [Pat]
pApats toks = go [] toks
  where
    go acc rest
      | startsApat rest = do
          (p, rest') <- pApat rest
          go (p : acc) rest'
      | otherwise = Right (reverse acc, rest)

    startsApat (t : _) = case t of
      TVar  _   -> True
      TCon  _   -> True
      TInt  _   -> True
      TChar _   -> True
      TStr  _   -> True
      TRes  "_" -> True
      TRes  "~" -> True
      TPunc "(" -> True
      TPunc "[" -> True
      _         -> False
    startsApat [] = False

pApat :: P Pat
pApat (TRes "_" : rest)  = Right (WildP, rest)
pApat (TRes "~" : rest)  = do
  (p, rest') <- pApat rest
  Right (TildeP p, rest')
pApat (TVar v : TRes "@" : rest) = do
  (p, rest') <- pApat rest
  Right (AsP (mkName v) p, rest')
pApat (TVar  v : rest) = Right (VarP (mkName v), rest)
pApat (TCon  c : rest) = Right (ConP (mkName c) [] [], rest)
pApat (TInt  n : rest) = Right (LitP (IntegerL n), rest)
pApat (TChar c : rest) = Right (LitP (CharL c), rest)
pApat (TStr  s : rest) = Right (LitP (StringL s), rest)
pApat (TPunc "(" : TPunc ")" : rest) = Right (ConP '() [] [], rest)
pApat (TPunc "(" : rest) = do
  (p, rest') <- pPat rest
  case rest' of
    (TPunc ")" : rest'') -> Right (p, rest'')
    (TPunc "," : _)      -> do
      (ps, rest'') <- pCommaList pPat rest'
      rest''' <- expect (TPunc ")") rest''
      Right (TupP (p : ps), rest''')
    _ -> Left ("expected ')' in a pattern " ++ atTok rest')
pApat (TPunc "[" : TPunc "]" : rest) = Right (ListP [], rest)
pApat (TPunc "[" : rest) = do
  (p, rest')  <- pPat rest
  (ps, rest'') <- pCommaList pPat rest'
  rest''' <- expect (TPunc "]") rest''
  Right (ListP (p : ps), rest''')
pApat toks = Left ("expected a pattern " ++ atTok toks)

pType :: P Type
pType toks = do
  (t, rest) <- pBType toks
  case rest of
    (TRes "->" : rest') -> do
      (u, rest'') <- pType rest'
      Right (AppT (AppT ArrowT t) u, rest'')
    _ -> Right (t, rest)

pBType :: P Type
pBType toks = do
  (t, rest) <- pAType toks
  go t rest
  where
    go acc rest@(u : _) | startsAType u = do
      (x, rest') <- pAType rest
      go (AppT acc x) rest'
    go acc rest = Right (acc, rest)

    startsAType t = case t of
      TCon  _   -> True
      TVar  _   -> True
      TPunc "(" -> True
      TPunc "[" -> True
      _         -> False

pAType :: P Type
pAType (TCon c : rest) = Right (ConT (mkName c), rest)
pAType (TVar v : rest) = Right (VarT (mkName v), rest)
pAType (TPunc "(" : TPunc ")" : rest) = Right (ConT ''(), rest)
pAType (TPunc "(" : rest) = do
  (t, rest') <- pType rest
  case rest' of
    (TPunc ")" : rest'') -> Right (t, rest'')
    (TPunc "," : _)      -> do
      (ts, rest'') <- pCommaList pType rest'
      rest''' <- expect (TPunc ")") rest''
      let n = length ts + 1
      Right (foldl AppT (ConT (tupleTypeName n)) (t : ts), rest''')
    _ -> Left ("expected ')' in a type " ++ atTok rest')
pAType (TPunc "[" : TPunc "]" : rest) = Right (ListT, rest)
pAType (TPunc "[" : rest) = do
  (t, rest') <- pType rest
  rest'' <- expect (TPunc "]") rest'
  Right (AppT ListT t, rest'')
pAType toks = Left ("expected a type " ++ atTok toks)

expect :: Tok -> [Tok] -> Either String [Tok]
expect t (t' : rest) | t == t' = Right rest
expect t toks = Left ("expected " ++ show (showTok t) ++ " " ++ atTok toks)

pCommaList1 :: P a -> P [a]
pCommaList1 p toks = do
  (x, rest)   <- p toks
  (xs, rest') <- pCommaList p rest
  Right (x : xs, rest')

pCommaList :: P a -> P [a]
pCommaList p = go []
  where
    go acc (TPunc "," : rest) = do
      (x, rest') <- p rest
      go (x : acc) rest'
    go acc rest = Right (reverse acc, rest)

pSemiList :: P a -> P [a]
pSemiList p toks = do
  (x, rest) <- p toks
  go [x] rest
  where
    go acc (TPunc ";" : rest) = do
      (y, rest') <- p rest
      go (y : acc) rest'
    go acc rest = Right (reverse acc, rest)

pprExp :: Exp -> String
pprExp (VarE n) = TH.nameBase n
pprExp (ConE n) = TH.nameBase n
pprExp e        = show e
