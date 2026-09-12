-- | Type-safe PEG (Parsing Expression Grammar) parser combinators.
--
-- Grammar non-terminals are checked at the type level against an environment
-- that binds each rule's name to the type it returns, so a reference to a
-- rule that does not exist, or a use of one at the wrong type, is a type
-- error.  Left recursion, a repetition that cannot consume input, an
-- undefined non-terminal and a duplicate rule are rejected by the
-- quasi-quoter when the grammar is spliced; see "PEG.Grammar" for exactly
-- what is checked where.
--
-- == Quick start
--
-- @
-- import PEG
-- import PEG.QQ (pegGrammar)
-- @
--
-- 1. Write the grammar with the 'PEG.QQ.pegGrammar' quasi-quoter, giving each
--    rule its result type.  It declares the environment, the grammar and its
--    signature.
-- 2. Run the grammar on a 'String' with 'parse' or 'parseWith'.
--
-- The environment can also be declared by hand — a type-level list of
-- @(name, entry)@ pairs, see 'PEG.Type.Env' — and the rules built with
-- 'PEG.QQ.pegRules' or the combinators in "PEG.Syntax".  That is what
-- 'PEG.QQ.pegGrammar' generates, and it stays supported; it is only more to
-- write and slower to compile.
--
-- See the @examples/@ directory for complete working grammars.
module PEG
  ( module PEG.CharSet
  , module PEG.Stream
  , module PEG.Type
  , module PEG.TyLevel
  , module PEG.Member
  , module PEG.Indent
  , module PEG.Syntax
  , module PEG.Grammar
  , module PEG.Parse
  ) where

import PEG.CharSet
import PEG.Grammar
import PEG.Stream
import PEG.Indent
import PEG.Member
import PEG.Parse
import PEG.Syntax
import PEG.TyLevel
import PEG.Type
