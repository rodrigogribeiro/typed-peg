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
-- == Why the 'PEG.Type.Ty' is not an index
--
-- The witness deliberately does /not/ record the non-terminal's
-- 'PEG.Type.Ty'.  Resolving @KnownMember s env a@ walks @env@ one instance at
-- a time, and every index of the class is carried along — and re-normalised —
-- at each of those steps.  A 'PEG.Type.Ty' carries a FIRST set, so an index
-- for it makes each step cost @O(|env|)@ instead of @O(1)@.  Nothing needs
-- it: 'Here' binds the entry's @ty@ existentially, which is enough to pull
-- the matching rule out of a rule table.
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
  Here  :: Member s ('(s, 'EnvEntry ty a) ': rest) a
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

-- The entry is taken apart in the instance head, so @ty@ is bound by
-- matching and never has to be threaded through the class.
instance (s ~ t) => KnownMemberStep 'EQ s ('(t, 'EnvEntry ty a) ': rest) a where
  memberStep _ = Here

instance KnownMember s rest a => KnownMemberStep 'LT s ('(t, e) ': rest) a where
  memberStep _ = There member

instance KnownMember s rest a => KnownMemberStep 'GT s ('(t, e) ': rest) a where
  memberStep _ = There member
