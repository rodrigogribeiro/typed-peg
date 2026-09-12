-- | The concrete syntax of the grammar DSL: its abstract syntax tree and the
-- recursive-descent parser that produces it.
--
-- This is split out of "PEG.QQ" so that the tree has two consumers rather
-- than one.  "PEG.QQ" translates it to Template Haskell; "PEG.Analysis"
-- computes nullability, FIRST sets and the well-formedness diagnostics from
-- it, at splice time, without the type checker being involved.
module PEG.QQ.Syntax
  ( Def (..)
  , Item (..)
  , PExpr (..)
  , RelS (..)
  , Directive (..)
  , P
  , parseGrammar
  , parseDirectives
  , parseExpr
  , spaces
  ) where

-- | One rule: its name, the source of its @:: T@ result-type annotation if it
-- has one, and its body.
--
-- The annotation is what lets 'PEG.QQ.pegGrammar' write the environment down:
-- the nullability and FIRST set of a rule can be computed from the grammar,
-- but its result type cannot — that comes from the Haskell in its semantic
-- action, which GHC types long after the splice has run.
data Def = Def String (Maybe String) PExpr
  deriving Show

-- | A @%key value@ line in the header of a grammar: @%start@, @%name@,
-- @%env@, @%stream@, @%result@.  The value is the rest of the line.
data Directive = Directive String String
  deriving Show

data Item = Item (Maybe String) PExpr
  deriving Show

data PExpr
  = EChoice  [PExpr]
  | ESeq     [Item] (Maybe String)
  | EAnd     PExpr
  | ENot     PExpr
  | EOpt     PExpr
  | EStar    PExpr
  | EPlus    PExpr
  | EChar    Char
  | EString  String
  | EClass   Bool [(Char,Char)]   -- ^ 'True' when the class is negated.
  | EDot
  | ENT      String
  | EIndent  RelS PExpr
  | EPos     RelS PExpr
  | EAlign   PExpr
  deriving Show

data RelS
  = RGt
  | RGe
  | REq
  | RAny
  | ROffset Int
  | RNamed  String
  deriving Show

type P a = String -> Either String (a, String)

errorAt :: String -> String -> Either String a
errorAt msg s = Left $ msg ++ " at: " ++ show (take 30 s)

spaces :: String -> String
spaces []         = []
spaces ('#':xs)   = spaces (drop 1 (dropWhile (/= '\n') xs))
spaces (c:xs)
  | c == ' ' || c == '\t' || c == '\n' || c == '\r' = spaces xs
  | otherwise = c:xs

tok :: String -> P ()
tok t s = case stripPrefix t (spaces s) of
  Just r  -> Right ((), r)
  Nothing -> errorAt ("expected " ++ show t) s
  where
    stripPrefix [] xs                 = Just xs
    stripPrefix (p:ps) (x:xs) | p==x  = stripPrefix ps xs
    stripPrefix _ _                   = Nothing

ident :: P String
ident s0 = case spaces s0 of
  (c:xs) | isIdStart c ->
    let (rest, leftover) = span isIdCont xs
    in Right (c:rest, leftover)
  s -> errorAt "expected identifier" s
  where
    isIdStart c = c == '_' || (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z')
    isIdCont c  = isIdStart c || (c >= '0' && c <= '9')

charLit :: P Char
charLit s0 = case spaces s0 of
  ('\'':xs) -> do (c, r1) <- escChar '\'' xs
                  case r1 of
                    ('\'':r2) -> Right (c, r2)
                    _         -> errorAt "expected closing '" r1
  s         -> errorAt "expected character literal" s

strLit :: P String
strLit s0 = case spaces s0 of
  ('"':xs) -> loop xs
  s        -> errorAt "expected string literal" s
  where
    loop ('"':r) = Right ("", r)
    loop r0      = do (c, r1) <- escChar '"' r0
                      (cs, r2) <- loop r1
                      pure (c:cs, r2)

escChar :: Char -> P Char
escChar _ ('\\':e:xs) = case e of
  'n'  -> Right ('\n', xs)
  't'  -> Right ('\t', xs)
  'r'  -> Right ('\r', xs)
  '\\' -> Right ('\\', xs)
  '\'' -> Right ('\'', xs)
  '"'  -> Right ('"',  xs)
  '['  -> Right ('[',  xs)
  ']'  -> Right (']',  xs)
  '0'  -> Right ('\0', xs)
  '^'  -> Right ('^',  xs)
  _    -> errorAt ("unknown escape \\" ++ [e]) xs
escChar stopC (c:xs)
  | c == stopC = errorAt "unexpected close quote" (c:xs)
  | otherwise  = Right (c, xs)
escChar _ [] = Left "unexpected end of input in literal"

-- | A character class.  A leading @^@ negates it, as in POSIX; write
-- @[\\^]@ for a class containing the caret itself.
classLit :: P (Bool, [(Char, Char)])
classLit s0 = case spaces s0 of
  ('[':'^':xs) -> do
    (rs, r) <- loop xs
    if null rs
      then errorAt "empty negated character class" s0
      else Right ((True, rs), r)
  ('[':xs)     -> do
    (rs, r) <- loop xs
    Right ((False, rs), r)
  s            -> errorAt "expected character class" s
  where
    loop (']':r) = Right ([], r)
    loop []      = Left "unterminated character class"
    loop r0      = do
      (c1, r1) <- escChar ']' r0
      case r1 of
        ('-':']':r2) -> pure ([(c1, c1), ('-', '-')], r2)
        ('-':r2) ->
          do (c2, r3) <- escChar ']' r2
             (rs, r4) <- loop r3
             pure ((c1, c2) : rs, r4)
        _ ->
          do (rs, r2) <- loop r1
             pure ((c1, c1) : rs, r2)

actionLit :: P String
actionLit s0 = case spaces s0 of
  ('{':xs) -> go (1 :: Int) ' ' [] xs
  s        -> errorAt "expected a semantic action" s
  where
    go _ _ _ [] = Left "unterminated semantic action: missing '}'"
    go n prev acc s = case s of
      ('{':'-':r) -> do
        (com, r') <- blockComment (1 :: Int) r
        go n '}' (revApp ("{-" ++ com) acc) r'
      ('"':r) -> do
        (str, r') <- literalBody '"' r
        go n '"' (revApp ('"' : str) acc) r'
      ('\'':r) | not (isIdChar prev) -> do
        (ch, r') <- literalBody '\'' r
        go n '\'' (revApp ('\'' : ch) acc) r'
      ('{':r) -> go (n + 1) '{' ('{' : acc) r
      ('}':r) | n == 1    -> Right (reverse acc, r)
              | otherwise -> go (n - 1) '}' ('}' : acc) r
      (c:_) | c `elem` symChars ->
        let (sym, r) = span (`elem` symChars) s
        in if all (== '-') sym && length sym >= 2
             then let (line, r') = span (/= '\n') r
                  in go n '\n' (revApp (sym ++ line) acc) r'
             else go n (last sym) (revApp sym acc) r
      (c:r) -> go n c (c : acc) r

    isIdChar c = c == '_' || c == '\''
              || (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z')
              || (c >= '0' && c <= '9')

    literalBody _ [] = Left "unterminated literal in a semantic action"
    literalBody q ('\\':c:r)     = do (b, r') <- literalBody q r
                                      Right ('\\' : c : b, r')
    literalBody q (c:r) | c == q = Right ([c], r)
    literalBody q (c:r)          = do (b, r') <- literalBody q r
                                      Right (c : b, r')

    blockComment _ []              = Left "unterminated {- -} comment in a semantic action"
    blockComment k ('-':'}':r)
      | k == 1                     = Right ("-}", r)
      | otherwise                  = do (c, r') <- blockComment (k - 1) r
                                        Right ("-}" ++ c, r')
    blockComment k ('{':'-':r)     = do (c, r') <- blockComment (k + 1) r
                                        Right ("{-" ++ c, r')
    blockComment k (c:r)           = do (c', r') <- blockComment k r
                                        Right (c : c', r')

    revApp xs acc = reverse xs ++ acc

    symChars = "!#$%&*+./<=>?@\\^|-~:"

parseExpr :: P PExpr
parseExpr s0 = do
  (e1, s1) <- parseSeq s0
  loop [e1] s1
  where
    loop acc s = case tok "/" s of
      Right (_, s') -> do (e, s'') <- parseSeq s'
                          loop (e:acc) s''
      Left _        -> case reverse acc of
        [x] -> Right (x, s)
        xs  -> Right (EChoice xs, s)

parseSeq :: P PExpr
parseSeq s0 = loop [] s0
  where
    loop acc s = case parseLabelled s of
      Right (it, s') -> loop (it:acc) s'
      Left _         -> case actionLit s of
        Right (act, s') -> Right (ESeq (reverse acc) (Just act), s')
        Left _          -> Right (ESeq (reverse acc) Nothing,    s)

parseLabelled :: P Item
parseLabelled s = case label s of
  Just (l, s1) -> do (e, s2) <- parsePrefix s1
                     pure (Item (Just l) e, s2)
  Nothing      -> do (e, s1) <- parsePrefix s
                     pure (Item Nothing e, s1)
  where
    label s' = case ident s' of
      Right (name, s1) -> case tok ":" s1 of
        Right (_, s2) -> Just (name, s2)
        Left _        -> Nothing
      Left _ -> Nothing

parsePrefix :: P PExpr
parsePrefix s = case tok "&" s of
  Right (_, s') -> do (e, s'') <- parseSuffix s'; pure (EAnd e, s'')
  Left _        -> case tok "!" s of
    Right (_, s') -> do (e, s'') <- parseSuffix s'; pure (ENot e, s'')
    Left _        -> parseSuffix s

parseSuffix :: P PExpr
parseSuffix s = do
  (p, s1) <- parsePrimary s
  loop p s1
  where
    loop p s1 = case tok "?" s1 of
      Right (_, s2) -> loop (EOpt p) s2
      Left _ -> case tok "*" s1 of
        Right (_, s2) -> loop (EStar p) s2
        Left _ -> case tok "+" s1 of
          Right (_, s2) -> loop (EPlus p) s2
          Left _ -> case indented EIndent "^" p s1 of
            Right (p', s2) -> loop p' s2
            Left _ -> case indented EPos "_" p s1 of
              Right (p', s2) -> loop p' s2
              Left _         -> Right (p, s1)

    indented con marker p s1 = do
      (_, s2) <- tok marker s1
      (r, s3) <- parseRel s2
      pure (con r p, s3)

parseRel :: P RelS
parseRel s = case tok ">=" s of
  Right (_, s1) -> Right (RGe, s1)
  Left _ -> case tok ">" s of
    Right (_, s1) -> Right (RGt, s1)
    Left _ -> case tok "=" s of
      Right (_, s1) -> Right (REq, s1)
      Left _ -> case tok "~" s of
        Right (_, s1) -> Right (RAny, s1)
        Left _ -> case tok "@" s of
          Right (_, s1) -> do (name, s2) <- ident s1
                              pure (RNamed name, s2)
          Left _ -> case tok "+" s of
            Right (_, s1) -> case span isDigit (spaces s1) of
              ([], _)     -> errorAt "expected a number after '+'" s1
              (ds, s2)    -> Right (ROffset (read ds), s2)
            Left _ -> errorAt "expected an indentation relation" s
  where
    isDigit c = c >= '0' && c <= '9'

parsePrimary :: P PExpr
parsePrimary s =
  case tok "(" s of
    Right (_, s1) -> do (e, s2) <- parseExpr s1
                        (_, s3) <- tok ")" s2
                        pure (e, s3)
    Left _ -> case parseAlign s of
     Right r -> Right r
     Left _ -> case tok "." s of
      Right (_, s1) -> Right (EDot, s1)
      Left _ -> case charLit s of
        Right (c, s1) -> Right (EChar c, s1)
        Left _ -> case strLit s of
          Right (cs, s1) -> Right (EString cs, s1)
          Left _ -> case classLit s of
            Right ((neg, rs), s1) -> Right (EClass neg rs, s1)
            Left _ -> case ident s of
              Right (name, s1) ->
                case tok "<-" s1 of
                  Right _  -> errorAt "definition where expression expected" s
                  Left _   -> Right (ENT name, s1)
              Left _ -> errorAt "expected primary expression" s

parseAlign :: P PExpr
parseAlign s = do
  (_, s1) <- tok "|" s
  (e, s2) <- parseExpr s1
  if isEmptyExpr e
    then errorAt "empty alignment: write |e| with a non-empty e" s
    else do (_, s3) <- tok "|" s2
            pure (EAlign e, s3)
  where
    isEmptyExpr (ESeq [] Nothing) = True
    isEmptyExpr _                 = False

parseGrammar :: P [Def]
parseGrammar s0 = loop [] s0
  where
    loop acc s = case ident s of
      Left _ -> case spaces s of
        [] -> Right (reverse acc, "")
        s' -> errorAt "expected definition or end of input" s'
      Right (name, s1) -> do
        (ty, s2) <- resultType s1
        (_, s3)  <- tok "<-" s2
        (e, s4)  <- parseExpr s3
        loop (Def name ty e : acc) s4

    -- @name :: T <- body@.  The annotation runs to the @<-@, which no type
    -- can contain, so it needs no parsing here: it is handed to
    -- "PEG.QQ.HsExp" as text.
    resultType s = case tok "::" s of
      Left _        -> Right (Nothing, s)
      Right (_, s1) -> case breakOnArrow (spaces s1) of
        Nothing        -> errorAt "expected '<-' after a result type" s1
        Just (ty, s2)
          | all isSpaceC ty -> errorAt "empty result type" s1
          | otherwise       -> Right (Just ty, s2)

    breakOnArrow = go []
      where
        go _   []             = Nothing
        go acc r@('<':'-':_)  = Just (reverse acc, r)
        go acc (c:cs)         = go (c:acc) cs

    isSpaceC c = c == ' ' || c == '\t' || c == '\n' || c == '\r'

-- | Consume the @%key value@ lines a grammar may start with.
--
-- Only the header is scanned, and only before the first rule, so a @%@ inside
-- a semantic action is never mistaken for a directive.
parseDirectives :: P [Directive]
parseDirectives = loop []
  where
    loop acc s = case spaces s of
      ('%':rest) ->
        let (key, r1)  = span isKeyChar rest
            (val, r2)  = span (/= '\n') r1
        in if null key
             then errorAt "expected a directive name after '%'" s
             else loop (Directive key (trim val) : acc) r2
      s' -> Right (reverse acc, s')

    isKeyChar c = (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z')
    trim = dropWhile isSpaceC . reverse . dropWhile isSpaceC . reverse
    isSpaceC c = c == ' ' || c == '\t' || c == '\r'
