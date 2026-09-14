{-# LANGUAGE DataKinds            #-}
{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE GADTs                #-}
{-# LANGUAGE KindSignatures       #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE RankNTypes           #-}

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
--   with itself compiles, and loops when run.  So is a 'Keyed' grammar whose
--   key type and rules were written by hand.
-- * 'PEG.QQ.pegRules' analyses its block open-world, because 'RCons' lets two
--   blocks be combined and a name the block does not define may be defined by
--   the other one.  Left recursion that closes /across/ two blocks is
--   therefore reported by neither.  A grammar written as one
--   'PEG.QQ.pegGrammar' has no such gap: it is closed-world, so every
--   reference is resolved and every cycle is visible.
--
-- Prefer 'PEG.QQ.pegGrammar'.  It is the only way to write a grammar that is
-- checked completely, and it is also the fastest to compile: in declaration
-- position it declares a key type for the grammar, one constructor per rule,
-- and builds a 'Keyed' grammar whose references cost the type checker the
-- same however many rules there are.  See "PEG.Key".
module PEG.Grammar
  ( Rules (..)
  , Grammar (..)
  ) where

import Data.Kind    (Type)

import PEG.Key     (InEnv, Tabulate)
import PEG.Syntax  (Name, PExp)
import PEG.Type

-- | A typed, heterogeneous list of named grammar rules over a type-level
-- environment.
--
-- @'Rules' s env defs@ is a list of rules over the stream @s@ whose bodies
-- reference non-terminals in @env@ and whose definitions together form
-- @defs@.
data Rules (s :: Type) (env :: Env) (defs :: Env) where
  RNil  :: Rules s env '[]
  RCons :: Name n
        -> PExp s (InEnv env) a
        -> Rules s env rest
        -> Rules s env ('(n, 'EnvEntry a) ': rest)

-- | A complete PEG grammar over the stream @s@: a set of mutually recursive
-- rules and a start expression, with its non-terminals named by keys of type
-- @nt@.
--
-- A 'Grammar' is monomorphic in its stream.  To reuse one grammar across
-- several stream types, give it a signature of the form
-- @forall s. 'PEG.Stream.Stream' s => Grammar s (Env s) a@ — but note that
-- doing so turns the value into a function of a dictionary, so the compiled
-- parser is no longer shared between calls.  Prefer a monomorphic top-level
-- signature.
data Grammar (s :: Type) (nt :: Type -> Type) (a :: Type) where
  -- | A grammar over a type-level environment.
  --
  -- The @Rules s env env@ field is what ties the two halves together: every
  -- rule's body is checked against the same environment the rule set
  -- defines, so a reference can only name a rule that exists and only at the
  -- type that rule has.
  Grammar :: Rules s env env
          -> PExp s (InEnv env) a
          -> Grammar s (InEnv env) a
  -- | A grammar over a declared key type: the rule each key names, and the
  -- start expression.
  --
  -- The rules are a function rather than a list, so that a rule's body is
  -- found by matching on its key — a @case@ whose every branch is checked on
  -- its own — and not by walking a type-level structure.
  Keyed   :: Tabulate nt
          => (forall b. nt b -> PExp s nt b)
          -> PExp s nt a
          -> Grammar s nt a
