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
-- @'Rules' env defs@ is a list of rules whose bodies reference non-terminals
-- in @env@ and whose definitions together form @defs@.
data Rules (env :: Env) (defs :: Env) where
  RNil  :: Rules env '[]
  RCons :: Name s
        -> PExp env ty a
        -> Rules env rest
        -> Rules env ('(s, 'EnvEntry ty a) ': rest)

type family Acyclic (env :: Env) :: Constraint where
  Acyclic '[]                             = ()
  Acyclic ('(s, 'EnvEntry ty _) ': rest) =
    (NotLeftRec s (Elem s (First ty)) ty, Acyclic rest)

type family NotLeftRec (s :: Symbol) (b :: Bool) (ty :: Ty) :: Constraint where
  NotLeftRec _ 'False _  = ()
  NotLeftRec s 'True  ty =
    TypeError ('Text "Left-recursive non-terminal: " ':<>: 'ShowType s
         ':$$: 'Text "Its head set already contains itself: "
               ':<>: 'ShowType (First ty)
         ':$$: 'Text "Violates the acyclicity condition i `notElem` Gamma(i).F.")

-- | A complete PEG grammar: a set of mutually recursive rules and a start
-- expression.
--
-- Constructing a 'Grammar' value discharges the 'Acyclic' constraint, so
-- any left-recursion in @env@ becomes a compile-time type error.
data Grammar (env :: Env) (startTy :: Ty) (startA :: Type) where
  Grammar :: Acyclic env
          => Rules env env
          -> PExp env startTy startA
          -> Grammar env startTy startA
