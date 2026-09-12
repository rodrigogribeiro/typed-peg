{-# LANGUAGE DataKinds      #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeFamilies   #-}
{-# LANGUAGE TypeOperators  #-}

-- | The grammar environment: what a non-terminal's name is bound to.
--
-- An environment maps each non-terminal's name to the Haskell type its rule
-- returns, and to nothing else.  A reference to a non-terminal is checked
-- against it — @nt \@\"expr\"@ is a type error unless @expr@ is a rule, and it
-- has whatever type @expr@'s rule has — which is the whole of what the
-- environment is for.
--
-- == What used to be here
--
-- Entries used to carry a 'Ty' as well: the rule's nullability and its FIRST
-- set, the set of non-terminals that can begin a derivation of it.  That is
-- what made left recursion a type error, by way of a @PEG.Grammar.Acyclic@
-- constraint that checked no rule was in its own FIRST set.
--
-- It was also, measurably, the whole cost of compiling a large grammar.  A
-- FIRST set grows with the grammar, so an environment of @n@ rules was
-- @O(n^2)@ type nodes, and each of the @2n@ reference constraints in the
-- rules had to be solved against it: 64 rules cost GHC 15 s, and the same
-- environment with a payload nothing reads at all was 15x an environment
-- without one.  Not reducing the FIRST-set arithmetic was worth nothing by
-- comparison — it was never the arithmetic, only the size.  See
-- @bench-compile/@.
--
-- Nullability and FIRST sets are still computed, and left recursion is still
-- rejected before a parser can be built from a left-recursive grammar — by
-- "PEG.Analysis", at splice time, once, in milliseconds, with the offending
-- rule and its cycle named.  What changed is that GHC no longer recomputes
-- them on every compilation of every module that mentions the grammar.  The
-- cost of that trade is real and is stated in "PEG.Grammar": a 'Rules' value
-- assembled by hand, without going through a quasi-quoter, is no longer
-- checked for left recursion by anything.
module PEG.Type
  ( EnvEntry (..)
  , Env
  , ResOf
  ) where

import Data.Kind    (Type)
import GHC.TypeLits (Symbol)

-- | An entry in the grammar environment: the type a rule's semantic action
-- produces.
data EnvEntry = EnvEntry Type

-- | A grammar environment: a type-level association list mapping non-terminal
-- names ('Symbol') to their 'EnvEntry'.
type Env = [(Symbol, EnvEntry)]

-- | Extract the result type from an 'EnvEntry'.
type family ResOf (e :: EnvEntry) :: Type where
  ResOf ('EnvEntry a) = a
