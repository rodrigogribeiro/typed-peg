-- | Type-safe PEG (Parsing Expression Grammar) parser combinators.
--
-- Grammar non-terminals are indexed at the type level by their nullability and
-- FIRST sets. Left-recursive grammars are rejected at compile time via a
-- 'GHC.TypeLits.TypeError'.
--
-- == Quick start
--
-- @
-- import PEG
-- import PEG.QQ (pegRules)
-- @
--
-- 1. Declare the grammar environment as a type-level list of @(name, entry)@
--    pairs (see 'PEG.Type.Env').
-- 2. Build a 'Grammar' using 'pegRules' (quasi-quoter) or the combinators in
--    "PEG.Syntax".
-- 3. Run the grammar on a 'String' with 'parse' or 'parseWith'.
--
-- See the @examples/@ directory for complete working grammars.
module PEG
  ( module PEG.CharSet
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
import PEG.Indent
import PEG.Member
import PEG.Parse
import PEG.Syntax
import PEG.TyLevel
import PEG.Type
