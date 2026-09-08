{-# LANGUAGE ConstraintKinds      #-}
{-# LANGUAGE DataKinds            #-}
{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE GADTs                #-}
{-# LANGUAGE KindSignatures       #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}

-- | Grammar type and the acyclicity constraint.
--
-- A 'Grammar' bundles a set of named rules ('Rules') and a start expression.
-- The 'Acyclic' constraint is checked at the definition site of every
-- 'Grammar' value: if any non-terminal is left-recursive (its own name appears
-- in its own FIRST set), GHC emits a 'GHC.TypeLits.TypeError' naming the
-- offending non-terminal.
module PEG.Grammar
  ( Rules (..)
  , Grammar (..)
  , Acyclic
  ) where

import Data.Kind    (Constraint, Type)
import GHC.TypeLits (ErrorMessage (..), Symbol, TypeError)

import PEG.Syntax  (Name, PExp)
import PEG.TyLevel (Elem)
import PEG.Type

-- | A typed, heterogeneous list of named grammar rules.
--
-- @'Rules' s env defs@ is a list of rules over the stream @s@ whose bodies
-- reference non-terminals in @env@ and whose definitions together form
-- @defs@.
data Rules (s :: Type) (env :: Env) (defs :: Env) where
  RNil  :: Rules s env '[]
  RCons :: Name n
        -> PExp s env ty a
        -> Rules s env rest
        -> Rules s env ('(n, 'EnvEntry ty a) ': rest)

type family Acyclic (env :: Env) :: Constraint where
  Acyclic '[]                                      = ()
  Acyclic ('(s, 'EnvEntry ('MkTy _ f) _) ': rest) =
    (NotLeftRec s (Elem s f) f, Acyclic rest)

type family NotLeftRec (s :: Symbol) (b :: Bool)
                       (f :: [Symbol]) :: Constraint where
  NotLeftRec _ 'False _ = ()
  NotLeftRec s 'True  f =
    TypeError ('Text "Left-recursive non-terminal: " ':<>: 'ShowType s
         ':$$: 'Text "Its head set already contains itself: "
               ':<>: 'ShowType f
         ':$$: 'Text "Violates the acyclicity condition i `notElem` Gamma(i).F.")

-- | A complete PEG grammar over the stream @s@: a set of mutually recursive
-- rules and a start expression.
--
-- A 'Grammar' is monomorphic in its stream.  To reuse one grammar across
-- several stream types, give it a signature of the form
-- @forall s. 'PEG.Stream.Stream' s => Grammar s Env ty a@ — but note that
-- doing so turns the value into a function of a dictionary, so the compiled
-- parser is no longer shared between calls.  Prefer a monomorphic top-level
-- signature.
--
-- Constructing a 'Grammar' value discharges the 'Acyclic' constraint, so
-- any left-recursion in @env@ becomes a compile-time type error.
data Grammar (s :: Type) (env :: Env) (startTy :: Ty) (startA :: Type) where
  Grammar :: Acyclic env
          => Rules s env env
          -> PExp s env startTy startA
          -> Grammar s env startTy startA
