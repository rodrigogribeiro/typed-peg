{-# LANGUAGE DataKinds            #-}
{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE GADTs                #-}
{-# LANGUAGE KindSignatures       #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}

-- | Grammar and rule-set types.
--
-- A 'Grammar' bundles a set of named rules ('Rules') and a start expression.
--
-- == Where left recursion is caught
--
-- In the quasi-quoters, and only there.  'PEG.QQ.pegGrammar' and
-- 'PEG.QQ.pegRules' run "PEG.Analysis" at splice time: it computes each
-- rule's nullability and FIRST set and rejects a grammar in which any rule
-- can begin with itself, naming the rule and the chain of head references
-- that closes the cycle.  It also rejects a repetition of something nullable,
-- an undefined non-terminal and a duplicate rule.  That happens once, when
-- the grammar is written, in milliseconds.
--
-- It used to happen again, and differently, on every compilation of every
-- module that mentioned the grammar: entries of the environment carried the
-- FIRST set as type-level data and an @Acyclic@ constraint checked that no
-- rule was in its own.  "PEG.Type" records what that cost — it was the whole
-- cost of a large grammar — and why it is gone.
--
-- What is given up is the case the splice cannot see:
--
-- * A 'Rules' chain assembled by hand from 'RCons', or a 'Grammar' built
--   around one, is checked for /reference/ errors only.  A rule that begins
--   with itself compiles, and loops when run.
-- * 'PEG.QQ.pegRules' analyses its block open-world, because 'RCons' lets two
--   blocks be combined and a name the block does not define may be defined by
--   the other one.  Left recursion that closes /across/ two blocks is
--   therefore reported by neither.  A grammar written as one
--   'PEG.QQ.pegGrammar' has no such gap: it is closed-world, so every
--   reference is resolved and every cycle is visible.
--
-- Prefer 'PEG.QQ.pegGrammar'.  It is the only way to write a grammar that is
-- checked completely, and it is also the fastest to compile, because it knows
-- each rule's position and emits 'PEG.Syntax.ntw' with the membership proof
-- rather than a 'PEG.Member.KnownMember' search.
module PEG.Grammar
  ( Rules (..)
  , Grammar (..)
  ) where

import Data.Kind    (Type)

import PEG.Syntax  (Name, PExp)
import PEG.Type

-- | A typed, heterogeneous list of named grammar rules.
--
-- @'Rules' s env defs@ is a list of rules over the stream @s@ whose bodies
-- reference non-terminals in @env@ and whose definitions together form
-- @defs@.
data Rules (s :: Type) (env :: Env) (defs :: Env) where
  RNil  :: Rules s env '[]
  RCons :: Name n
        -> PExp s env a
        -> Rules s env rest
        -> Rules s env ('(n, 'EnvEntry a) ': rest)

-- | A complete PEG grammar over the stream @s@: a set of mutually recursive
-- rules and a start expression.
--
-- The @Rules s env env@ field is what ties the two halves together: every
-- rule's body is checked against the same environment the rule set defines,
-- so a reference can only name a rule that exists and only at the type that
-- rule has.
--
-- A 'Grammar' is monomorphic in its stream.  To reuse one grammar across
-- several stream types, give it a signature of the form
-- @forall s. 'PEG.Stream.Stream' s => Grammar s Env a@ — but note that
-- doing so turns the value into a function of a dictionary, so the compiled
-- parser is no longer shared between calls.  Prefer a monomorphic top-level
-- signature.
data Grammar (s :: Type) (env :: Env) (a :: Type) where
  Grammar :: Rules s env env
          -> PExp s env a
          -> Grammar s env a
