{-# LANGUAGE DataKinds        #-}
{-# LANGUAGE QuasiQuotes      #-}
{-# LANGUAGE TemplateHaskell  #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators    #-}

module Layout
  ( DoStmt (..)
  , DoEnv
  , doExp
  , layoutOpts
  ) where

import PEG
import PEG.QQ (pegGrammar)

data DoStmt
  = Atom   String
  | Nested [DoStmt]
  deriving (Eq, Show)

-- | @name@ is a character class, so its result is a chunk of the input rather
-- than a 'String' — which is why its annotation is @s@ and why the generated
-- environment takes the stream as a parameter.
--
-- @ws@ has neither a label nor an action, so it returns @()@: that is the
-- DSL's rule for a rule body, and the annotation has to agree with it.  A
-- start expression is different — @%start ws d:doexp ws !.@ returns what its
-- one labelled item returns.
[pegGrammar|
  %name  doExp
  %env   DoEnv
  %start ws d:doexp ws !.

  doexp  :: [DoStmt] <- "do" b:(i:istmts / j:stmts)

  istmts :: [DoStmt] <- ss:(ws st:|s:stmt|)+^>

  stmts  :: [DoStmt] <- r:(ws '{' ws s:stmt ss:(ws ';' ws t:stmt)* ws '}' { s : ss })^~

  stmt   :: DoStmt   <- d:doexp { Nested d } / n:name { Atom (chunkToString n) }

  name   :: s        <- cs:[a-z]+

  ws     :: ()       <- [ \t\r\n]*_~
|]

layoutOpts :: Opts
layoutOpts = defaultOpts { optTokenMode = relD geR }
