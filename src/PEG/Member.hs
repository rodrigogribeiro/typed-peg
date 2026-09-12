{-# LANGUAGE AllowAmbiguousTypes   #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE KindSignatures        #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE UndecidableInstances  #-}

-- | Membership witnesses for heterogeneous type-level environments.
--
-- 'Member' is a proof that a name @s@ with result type @a@ is present in the
-- environment @env@.  'KnownMember' is the class that allows the proof to be
-- materialised from type information at runtime, enabling non-terminal lookup
-- during parsing.
--
-- == Why the class has only the indices it has
--
-- Resolving @KnownMember s env a@ walks @env@ one instance at a time, and
-- every index of the class is carried along — and re-normalised — at each of
-- those steps.  An index whose size grows with the grammar therefore makes
-- each step cost @O(|env|)@ instead of @O(1)@.  Entries used to carry a FIRST
-- set for exactly that reason, and keeping it out of this class was worth a
-- large constant; it is now out of the environment altogether (see
-- "PEG.Type"), so the same discipline is cheap to keep and worth keeping.
--
-- Better still is not to search at all: 'PEG.Syntax.ntw' takes the witness
-- rather than deriving it, which is what a quasi-quoter emits, since a splice
-- knows every rule's position.
module PEG.Member
  ( Member (..)
  , KnownMember (..)
  ) where

import Data.Kind    (Type)
import Data.Proxy   (Proxy (..))
import GHC.TypeLits (CmpSymbol, ErrorMessage (..), Symbol, TypeError)

import PEG.Type

-- | @'Member' s env a@ witnesses that @env@ binds the name @s@ to a rule
-- returning @a@, and records /where/ in @env@ that binding is.
data Member (s :: Symbol) (env :: Env) (a :: Type) where
  Here  :: Member s ('(s, 'EnvEntry a) ': rest) a
  There :: Member s rest a -> Member s (e ': rest) a

class KnownMember (s :: Symbol) (env :: Env) (a :: Type) where
  member :: Member s env a

instance TypeError ('Text "Undefined non-terminal: " ':<>: 'ShowType s
               ':$$: 'Text "The grammar has no rule for this name.")
      => KnownMember s '[] a where
  member = error "PEG.Member: unreachable"

-- Dispatch on 'CmpSymbol' directly rather than through a @SymEq@ wrapper:
-- that is one fewer type-family application to reduce per entry scanned, and
-- an environment is scanned once per occurrence of every non-terminal.
instance KnownMemberStep (CmpSymbol s t) s ('(t, e) ': rest) a
      => KnownMember s ('(t, e) ': rest) a where
  member = memberStep (Proxy :: Proxy (CmpSymbol s t))

class KnownMemberStep (o :: Ordering) (s :: Symbol) (env :: Env) (a :: Type) where
  memberStep :: Proxy o -> Member s env a

-- The entry is taken apart in the instance head, so the result type is bound
-- by matching and never has to be threaded through the class.
instance (s ~ t) => KnownMemberStep 'EQ s ('(t, 'EnvEntry a) ': rest) a where
  memberStep _ = Here

instance KnownMember s rest a => KnownMemberStep 'LT s ('(t, e) ': rest) a where
  memberStep _ = There member

instance KnownMember s rest a => KnownMemberStep 'GT s ('(t, e) ': rest) a where
  memberStep _ = There member
