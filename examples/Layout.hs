{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE QuasiQuotes           #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# OPTIONS_GHC -Wno-partial-type-signatures #-}

module Layout
  ( DoStmt (..)
  , DoEnv
  , doExp
  , layoutOpts
  ) where

import PEG
import PEG.QQ (pegExpr, pegRules)

data DoStmt
  = Atom   String
  | Nested [DoStmt]
  deriving (Eq, Show)

-- | The environment is parameterised by the stream, because @name@ is a
-- character class and so produces a chunk of the input rather than a
-- 'String'.  Any rule whose result is a chunk pushes @s@ into the
-- environment this way.
type DoEnv s =
  '[ '("doexp" , 'EnvEntry ('MkTy 'False '[])                               [DoStmt])
   , '("istmts", 'EnvEntry ('MkTy 'False '["ws", "stmt", "doexp", "name"]) [DoStmt])
   , '("stmts" , 'EnvEntry ('MkTy 'False '["ws"])                          [DoStmt])
   , '("stmt"  , 'EnvEntry ('MkTy 'False '["doexp", "name"])               DoStmt)
   , '("name"  , 'EnvEntry ('MkTy 'False '[])                              s)
   , '("ws"    , 'EnvEntry ('MkTy 'True  '[])                              ())
   ]

doExp :: Stream s => Grammar s (DoEnv s) _ [DoStmt]
doExp =
  Grammar
    [pegRules|
       doexp  <- "do" b:(i:istmts / j:stmts)

       istmts <- ss:(ws st:|s:stmt|)+^>

       stmts  <- r:(ws '{' ws s:stmt ss:(ws ';' ws t:stmt)* ws '}' { s : ss })^~

       stmt   <- d:doexp { Nested d } / n:name { Atom (chunkToString n) }

       name   <- cs:[a-z]+

       ws     <- [ \t\r\n]*_~
    |]
    [pegExpr| ws d:doexp ws !. |]

layoutOpts :: Opts
layoutOpts = defaultOpts { optTokenMode = relD geR }
