{-# LANGUAGE DataKinds        #-}
{-# LANGUAGE GADTs            #-}
{-# LANGUAGE QuasiQuotes      #-}
{-# LANGUAGE TemplateHaskell  #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators    #-}

-- | The grammar of MiniPython, the language of the compilers course at UFOP.
--
-- It is ported from the course's reference implementation (the @mpyc@
-- compiler, @MiniPython.ParserPEG@), with one change to the AST: source
-- positions are dropped, since that grammar filled every one of them with
-- @Pos file 0 0@ anyway.
--
-- Two things the specification has and that grammar lacked are added, as
-- they were to the course's parsers: a method's explicit @self@ parameter,
-- and a field declared in the body of a class with a type and no initialiser
-- (@x: int@), which is 'SFieldDecl'.
--
-- It is here for its size rather than for its language.  With 27 rules, a
-- dozen precedence levels and some very long ordered choices it is the
-- largest grammar in @examples/@, and a realistic check on what a generated
-- grammar costs the type checker.  While environments carried FIRST sets (see
-- "PEG.Type"), this grammar with an inferred environment exhausted a 10 GB
-- heap after four minutes.  Over a generated key type (see "PEG.Key") it
-- type-checks in under half a second and 57 MiB; @bench-compile/@ measures it
-- as the @minipython@ mode.
--
-- Blocks are indentation-sensitive: @block@ requires its statements to be
-- indented further than the line that opened it, and each statement to be
-- aligned with the first one.  Run it with 'mpyOpts'.
module MiniPython
  ( AnnType (..)
  , BinOp (..)
  , UnOp (..)
  , Expr (..)
  , Param (..)
  , Stmt (..)
  , Program (..)
  , MiniPythonEnv
  , miniPython
  , mpyOpts
  , parseMiniPython
  , miniPythonMain
  ) where

import PEG hiding (Not)
import PEG.QQ (pegGrammar)

type Ident = String

data AnnType
  = ATInt
  | ATFloat
  | ATBool
  | ATStr
  | ATNone
  | ATList AnnType
  | ATFunc [AnnType] AnnType
  | ATClass Ident
  deriving (Show, Eq)

data BinOp
  = Add | Sub | Mul | Div | IDiv | Mod | Pow
  | Eq | Ne | Lt | Le | Gt | Ge
  | And | Or
  deriving (Show, Eq)

data UnOp = Neg | Not
  deriving (Show, Eq)

data Expr
  = EInt     Integer
  | EFloat   Double
  | EBool    Bool
  | EStr     String
  | ENone
  | EVar     Ident
  | EBinOp   BinOp Expr Expr
  | EUnOp    UnOp Expr
  | ECall    Expr [Expr]
  | EIndex   Expr Expr
  | EField   Expr Ident
  | EList    [Expr]
  | ELambda  [Ident] Expr
  | EIfExpr  Expr Expr Expr
  deriving (Show, Eq)

data Param = Param Ident (Maybe AnnType)
  deriving (Show, Eq)

data Stmt
  = SAssign    Ident (Maybe AnnType) Expr
  | SAssignIdx Expr Expr Expr
  | SAssignFld Expr Ident Expr
  | SAugAssign Ident BinOp Expr
  | SExpr      Expr
  | SIf        [(Expr, [Stmt])] (Maybe [Stmt])
  | SWhile     Expr [Stmt]
  | SFor       Ident Expr [Stmt]
  | SReturn    (Maybe Expr)
  | SBreak
  | SContinue
  | SPass
  | SDef       Ident [Param] (Maybe AnnType) [Stmt]
  | SClass     Ident (Maybe Ident) [Stmt]
  | SFieldDecl Ident AnnType
  deriving (Show, Eq)

newtype Program = Program [Stmt]
  deriving (Show, Eq)

data Postfix
  = PFCall  [Expr]
  | PFIndex Expr
  | PFField Ident

applyPostfixes :: Expr -> [Postfix] -> Expr
applyPostfixes = foldl step
  where
    step e (PFCall  args) = ECall  e args
    step e (PFIndex idx)  = EIndex e idx
    step e (PFField n)    = EField e n

-- | The left-hand side of an assignment is parsed as an expression and
-- checked afterwards, as Python's own grammar does.
assignTo :: Expr -> Expr -> Stmt
assignTo (EField base n) rhs = SAssignFld base n rhs
assignTo (EIndex base i) rhs = SAssignIdx base i rhs
assignTo (EVar n)        rhs = SAssign n Nothing rhs
assignTo e               rhs = SExpr (EBinOp Eq e rhs)

binLeft :: BinOp -> Expr -> [Expr] -> Expr
binLeft o = foldl (EBinOp o)

binOps :: Expr -> [(BinOp, Expr)] -> Expr
binOps = foldl (\l (o, r) -> EBinOp o l r)

-- | A keyword is a literal not followed by an identifier character; every
-- @![a-zA-Z0-9_]@ below is that lookahead.
[pegGrammar|
  %name   miniPython
  %start  program
  %stream String

  program      :: Program <- ws ss:(ws st:|s:stmtbody|)* ws !. { Program ss }

  ws           :: ()      <- ([ \t\n\r] / '#' [^\n]* ('\n' / !.))*_~

  name         :: String  <-
      !( ( "and" / "break" / "bool" / "class" / "continue"
         / "def" / "elif" / "else" / "False" / "float"
         / "for" / "if" / "int" / "in" / "lambda"
         / "None" / "not" / "or" / "pass" / "return"
         / "self" / "str" / "True" / "while" ) ![a-zA-Z0-9_] )
      c:[a-zA-Z_] cs:[a-zA-Z0-9_]* { c : cs }

  block        :: [Stmt]  <- ':' ss:(ws st:|s:stmtbody|)+^> { ss }

  stmtbody     :: Stmt    <-
      d:def_stmt    { d }
    / cl:class_stmt { cl }
    / i:if_stmt     { i }
    / "while" ![a-zA-Z0-9_] ws wc:expr ws wb:block { SWhile wc wb }
    / "for" ![a-zA-Z0-9_] ws fn:name ws "in" ![a-zA-Z0-9_] ws fe:expr ws fb:block
        { SFor fn fe fb }
    / "return" ![a-zA-Z0-9_] ws re:(re2:expr { Just re2 } / { Nothing })
        { SReturn re }
    / "break"    ![a-zA-Z0-9_] { SBreak }
    / "continue" ![a-zA-Z0-9_] { SContinue }
    / "pass"     ![a-zA-Z0-9_] { SPass }
    / a:assign_stmt { a }

  def_stmt     :: Stmt    <-
      "def" ![a-zA-Z0-9_] ws n:name ws '(' ws
      ps:( p:param rest:(ws ',' ws q:param { q })* { p : rest }
         / { [] } )
      ws ')'
      rt:(ws "->" ws t:ann_type { Just t } / { Nothing })
      ws b:block
        { SDef n ps rt b }

  param        :: Param   <-
      "self" ![a-zA-Z0-9_] { Param "self" Nothing }
    / pn:name ws ':' ws pt:ann_type { Param pn (Just pt) }
    / pn:name { Param pn Nothing }

  class_stmt   :: Stmt    <-
      "class" ![a-zA-Z0-9_] ws n:name ws
      par:('(' ws cn:name ws ')' { Just cn } / { Nothing })
      ws b:class_block
        { SClass n par b }

  class_block  :: [Stmt]  <- ':' ss:(ws st:|s:class_member|)+^> { ss }

  class_member :: Stmt    <-
      n:name ws ':' ws t:ann_type !(ws '=' !'=') { SFieldDecl n t }
    / s:stmtbody { s }

  if_stmt      :: Stmt    <-
      "if" ![a-zA-Z0-9_] ws c:expr ws b:block
      elifs:(ws "elif" ![a-zA-Z0-9_] ws ec:expr ws eb:block { (ec, eb) })*
      alt:(ws "else" ![a-zA-Z0-9_] ws ab:block { Just ab } / { Nothing })
        { SIf ((c, b) : elifs) alt }

  assign_stmt  :: Stmt    <-
      n:name ws ':' ws t:ann_type ws '=' !'=' ws e:expr { SAssign n (Just t) e }
    / n:name ws "//=" ws e:expr { SAugAssign n IDiv e }
    / n:name ws "+="  ws e:expr { SAugAssign n Add  e }
    / n:name ws "-="  ws e:expr { SAugAssign n Sub  e }
    / n:name ws "*="  ws e:expr { SAugAssign n Mul  e }
    / n:name ws "/="  ws e:expr { SAugAssign n Div  e }
    / n:name ws "%="  ws e:expr { SAugAssign n Mod  e }
    / e:postfix_expr ws '=' !'=' ws r:expr { assignTo e r }
    / e:expr { SExpr e }

  ann_type     :: AnnType <-
      "int"   ![a-zA-Z0-9_] { ATInt }
    / "float" ![a-zA-Z0-9_] { ATFloat }
    / "bool"  ![a-zA-Z0-9_] { ATBool }
    / "str"   ![a-zA-Z0-9_] { ATStr }
    / "None"  ![a-zA-Z0-9_] { ATNone }
    / '[' ws t:ann_type ws ']' { ATList t }
    / '(' ws ts:(t:ann_type ts2:(ws ',' ws u:ann_type { u })* { t : ts2 } / { [] })
      ws ')' ws "->" ws r:ann_type
        { ATFunc ts r }
    / n:name ws '[' ws t2:ann_type ws ']'
        { if n == "list" then ATList t2 else ATClass n }
    / n2:name { ATClass n2 }

  expr         :: Expr    <-
      "lambda" ![a-zA-Z0-9_] ws
      ps:(n:name ns:(ws ',' ws m:name { m })* { n : ns } / { [] })
      ws ':' ws b:expr
        { ELambda ps b }
    / e:or_expr ws "if" ![a-zA-Z0-9_] ws c:or_expr ws "else" ![a-zA-Z0-9_] ws a:expr
        { EIfExpr c e a }
    / e:or_expr { e }

  or_expr      :: Expr    <- e:and_expr es:(ws "or" ![a-zA-Z0-9_] ws r:and_expr)*
                               { binLeft Or e es }

  and_expr     :: Expr    <- e:not_expr es:(ws "and" ![a-zA-Z0-9_] ws r:not_expr)*
                               { binLeft And e es }

  not_expr     :: Expr    <-
      "not" ![a-zA-Z0-9_] ws e:not_expr { EUnOp Not e }
    / e:add_expr ws o:cmp_op ws r:add_expr { EBinOp o e r }
    / e:add_expr { e }

  cmp_op       :: BinOp   <-
      "==" { Eq } / "!=" { Ne } / "<=" { Le } / ">=" { Ge } / '<' { Lt } / '>' { Gt }

  add_expr     :: Expr    <-
      e:mul_expr es:(ws o:('+' { Add } / '-' { Sub }) ws r:mul_expr { (o, r) })*
        { binOps e es }

  mul_expr     :: Expr    <-
      e:pow_expr
      es:(ws o:("//" { IDiv } / '/' { Div } / '%' { Mod } / '*' !'*' { Mul })
          ws r:pow_expr { (o, r) })*
        { binOps e es }

  pow_expr     :: Expr    <- e:unary_expr ws "**" ws r:pow_expr { EBinOp Pow e r }
                           / e:unary_expr { e }

  unary_expr   :: Expr    <- '-' ws e:unary_expr { EUnOp Neg e }
                           / e:postfix_expr { e }

  postfix_expr :: Expr    <-
      e:atom
      ps:( ws '(' ws as:(ea:expr eas:(ws ',' ws r:expr { r })* { ea : eas } / { [] })
           ws ')' { PFCall as }
         / ws '[' ws i:expr ws ']' { PFIndex i }
         / ws '.' ws fn:name { PFField fn } )*
        { applyPostfixes e ps }

  atom         :: Expr    <-
      "True"  ![a-zA-Z0-9_] { EBool True }
    / "False" ![a-zA-Z0-9_] { EBool False }
    / "None"  ![a-zA-Z0-9_] { ENone }
    / "self"  ![a-zA-Z0-9_] { EVar "self" }
    / "int"   ![a-zA-Z0-9_] { EVar "int" }
    / "float" ![a-zA-Z0-9_] { EVar "float" }
    / "bool"  ![a-zA-Z0-9_] { EVar "bool" }
    / "str"   ![a-zA-Z0-9_] { EVar "str" }
    / n:name { EVar n }
    / ds:[0-9]+ '.' fs:[0-9]+ ep:exponent
        { EFloat (read (ds ++ "." ++ fs ++ ep) :: Double) }
    / ds:[0-9]+ ep:(e:[eE] s:sign xs:[0-9]+ { (e : s) ++ xs })
        { EFloat (read (ds ++ ep) :: Double) }
    / d:[0-9] ds:[0-9_]* { EInt (read (d : filter (/= '_') ds) :: Integer) }
    / '"' cs:(c:str_char { c } / !'"' c3:. { c3 })* '"' { EStr cs }
    / '\'' cs:(c:str_char { c } / !'\'' c3:. { c3 })* '\'' { EStr cs }
    / '(' ws e:expr ws ')' { e }
    / '[' ws les:(le:expr les2:(ws ',' ws lr:expr { lr })* { le : les2 } / { [] })
      ws ']'
        { EList les }

  exponent     :: String  <-
      e:[eE] s:sign xs:[0-9]+ { (e : s) ++ xs }
    / { "" }

  sign         :: String  <- '+' { "+" } / '-' { "-" } / { "" }

  str_char     :: Char    <-
      '\\' c:( 'n' { '\n' } / 't' { '\t' } / 'r' { '\r' }
             / '\\' { '\\' } / '"' { '"' } / '\'' { '\'' }
             / '0' { '\0' } / c2:. { c2 } )
        { c }
|]

-- | Blocks are delimited by indentation, so tokens are compared with the
-- enclosing block's column.
mpyOpts :: Opts
mpyOpts = defaultOpts { optTokenMode = relD geR }

parseMiniPython :: String -> Either ParseError Program
parseMiniPython src = case parseWith mpyOpts miniPython src of
  OK p _ _ -> Right p
  Fail e   -> Left e

miniPythonMain :: IO ()
miniPythonMain = mapM_ run samples
  where
    run (label, src) = putStrLn $ label ++ " => " ++ case parseMiniPython src of
      Right (Program ss) -> "OK, " ++ show (length ss) ++ " statement(s): "
                             ++ take 100 (show ss)
      Left e             -> "Fail at " ++ show (errLine e) ++ ":"
                              ++ show (errColumn e)

    samples =
      [ ("assign", "x: int = 1 + 2 * 3\n")
      , ("def", unlines
          [ "def fib(n: int) -> int:"
          , "    if n < 2:"
          , "        return n"
          , "    else:"
          , "        return fib(n - 1) + fib(n - 2)"
          , "print(fib(10))"
          ])
      , ("while", unlines
          [ "i = 0"
          , "while i < 10:"
          , "    i += 1"
          , "    if i % 2 == 0:"
          , "        continue"
          , "    xs[i] = i ** 2"
          ])
      , ("class", unlines
          [ "class Point:"
          , "    x: float"
          , "    y: float"
          , "    def __init__(self, x: float, y: float) -> None:"
          , "        self.x = x"
          , "        self.y = y"
          , "    def norm(self) -> float:"
          , "        return self.x * self.x + self.y * self.y"
          , "p = Point(3.0, 4.0)"
          , "s = 'a\\n' if not p.norm() >= 1.5e3 else \"b\""
          ])
      , ("missing colon", "if x > 1\n    pass\n")
      ]
