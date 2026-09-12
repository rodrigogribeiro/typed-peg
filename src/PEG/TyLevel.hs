{-# LANGUAGE DataKinds            #-}
{-# LANGUAGE PolyKinds            #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}

-- | Looking a non-terminal up in the grammar environment.
--
-- This is the only type-level computation the library still does, and it is
-- the hot path: there is one lookup per occurrence of every non-terminal in
-- the grammar, so it is written to do as little as possible per entry
-- scanned.
--
-- == What used to be here
--
-- Sorted-set machinery — 'Union', membership, insertion — over the FIRST sets
-- that environment entries used to carry, together with the boolean families
-- that combined their nullability.  Those sets now live in "PEG.Analysis",
-- which computes them at splice time; see "PEG.Type" for why they left the
-- types.  What remains is the search, and with the sets gone it is a search
-- over an environment that is linear in the size of the grammar rather than
-- quadratic.
module PEG.TyLevel
  ( Lookup
  , Names
  ) where

import GHC.TypeLits (ErrorMessage (..), Symbol, TypeError)

import PEG.Type

-- | Look up a non-terminal's entry in the environment.
--
-- Two things matter.  The search proper ('LookupMb') carries only the tail it
-- still has to scan — threading the /whole/ environment through it so the
-- not-found case could name the available non-terminals costs a traversal of
-- that environment at every step.  The environment is therefore named once,
-- in 'Found', which only reduces after the search has finished; measured
-- against a variant that does not name it at all, the good error message
-- costs about 5%.
--
-- And the match is on a /non-linear/ pattern — @s@ appears twice in the
-- second clause — rather than on @CmpSymbol s t@ dispatched through a helper
-- family.  GHC decides the clause by syntactic equality and by apartness for
-- the fall-through, which is one type-family reduction per entry instead of
-- two.  (The trick is @Data.Type.Map@'s, from @type-level-sets@.)
type family Lookup (s :: Symbol) (env :: Env) :: EnvEntry where
  Lookup s env = Found s env (LookupMb s env)

type family LookupMb (s :: Symbol) (env :: Env) :: Maybe EnvEntry where
  LookupMb _ '[]               = 'Nothing
  LookupMb s ('(s, e) ': rest) = 'Just e
  LookupMb s (_ ': rest)       = LookupMb s rest

type family Found (s :: Symbol) (env :: Env)
                  (r :: Maybe EnvEntry) :: EnvEntry where
  Found _ _ ('Just e) = e
  Found s env 'Nothing =
    TypeError ('Text "Undefined non-terminal: " ':<>: 'ShowType s
         ':$$: 'Text "Available non-terminals: " ':<>: 'ShowType (Names env))

-- | The names an environment defines, for the message above.
type family Names (env :: Env) :: [Symbol] where
  Names '[]               = '[]
  Names ('(s, _) ': rest) = s ': Names rest
