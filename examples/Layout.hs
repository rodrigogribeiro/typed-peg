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

type DoEnv =
  '[ '("doexp" , 'EnvEntry ('MkTy 'False '[])                               [DoStmt])
   , '("istmts", 'EnvEntry ('MkTy 'False '["ws", "stmt", "doexp", "name"]) [DoStmt])
   , '("stmts" , 'EnvEntry ('MkTy 'False '["ws"])                          [DoStmt])
   , '("stmt"  , 'EnvEntry ('MkTy 'False '["doexp", "name"])               DoStmt)
   , '("name"  , 'EnvEntry ('MkTy 'False '[])                              String)
   , '("ws"    , 'EnvEntry ('MkTy 'True  '[])                              ())
   ]

doExp :: Grammar DoEnv _ [DoStmt]
doExp =
  Grammar
    [pegRules|
       doexp  <- "do" b:(i:istmts / j:stmts)

       istmts <- ss:(ws st:|s:stmt|)+^>

       stmts  <- r:(ws '{' ws s:stmt ss:(ws ';' ws t:stmt)* ws '}' { s : ss })^~

       stmt   <- d:doexp { Nested d } / n:name { Atom n }

       name   <- cs:[a-z]+

       ws     <- [ \t\r\n]*_~
    |]
    [pegExpr| ws d:doexp ws !. |]

layoutOpts :: Opts
layoutOpts = defaultOpts { optTokenMode = relD geR }
