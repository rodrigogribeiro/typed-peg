{-# LANGUAGE DataKinds      #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeFamilies   #-}
{-# LANGUAGE TypeOperators  #-}

-- | Type-level representation of PEG type information.
--
-- Each non-terminal carries a 'Ty': a pair of its /nullability/
-- (can it match the empty string?) and its /FIRST set/ (which non-terminal
-- names can appear at the head of a derivation?).
-- Both pieces of information are tracked as type-level data and used by the
-- 'PEG.Grammar.Acyclic' constraint to reject left-recursive grammars at
-- compile time.
module PEG.Type
  ( Ty (..)
  , Nullable
  , First
  , EnvEntry (..)
  , Env
  , TyOf
  , ResOf
  ) where

import Data.Kind    (Type)
import GHC.TypeLits (Symbol)

-- | A PEG type: nullability flag and FIRST set.
--
-- @'MkTy' n fs@ means the expression may match the empty string iff @n ~ 'True@,
-- and the set of non-terminal names that can begin a derivation is @fs@.
data Ty = MkTy Bool [Symbol]

-- | Extract the nullability flag from a 'Ty'.
type family Nullable (t :: Ty) :: Bool where
  Nullable ('MkTy n _) = n

-- | Extract the FIRST set (list of non-terminal names) from a 'Ty'.
type family First (t :: Ty) :: [Symbol] where
  First ('MkTy _ f) = f

-- | An entry in the grammar environment: a 'Ty' paired with its result type.
data EnvEntry = EnvEntry Ty Type

-- | A grammar environment: a type-level association list mapping non-terminal
-- names ('Symbol') to their 'EnvEntry'.
type Env = [(Symbol, EnvEntry)]

-- | Extract the 'Ty' from an 'EnvEntry'.
type family TyOf (e :: EnvEntry) :: Ty where
  TyOf ('EnvEntry t _) = t

-- | Extract the result type from an 'EnvEntry'.
type family ResOf (e :: EnvEntry) :: Type where
  ResOf ('EnvEntry _ a) = a
