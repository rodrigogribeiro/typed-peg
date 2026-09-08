{-# LANGUAGE DataKinds            #-}
{-# LANGUAGE PolyKinds            #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}

-- | Type-level utilities: boolean logic, symbol equality, set operations,
-- and environment lookup.
--
-- These type families are used internally to compute the FIRST sets and
-- nullability of PEG expressions at the kind level, enabling the
-- 'PEG.Grammar.Acyclic' constraint to be resolved at compile time.
--
-- == Representation of FIRST sets
--
-- A FIRST set is a @['Symbol']@ kept /strictly sorted/ by 'CmpSymbol'.
-- Sortedness is the whole point: it makes the representation canonical (one
-- set, one type), so 'Union' is a single-pass merge and 'Elem' can stop at
-- the first symbol greater than the one it is looking for.
--
-- == Why the families are written this way
--
-- Every clause below mentions each of its arguments — and in particular each
-- recursive call — /exactly once/ on the right-hand side.  This is not a
-- style choice.  A clause such as
--
-- @
-- ConsIfAbsent x xs = If (Elem x xs) xs (x ': xs)   -- DON'T
-- @
--
-- mentions @xs@ three times, and @xs@ is normally an unreduced application
-- of 'Union'.  GHC therefore has three copies of the pending computation to
-- reduce, each of which triples again one level down: a union of two sets of
-- size @n@ costs @3^n@ reductions rather than @n@.  Dispatching on an
-- already-computed 'Ordering' in a separate family keeps every right-hand
-- side linear in its arguments.
module PEG.TyLevel
  ( If
  , And
  , Or
  , SymEq
  , Elem
  , Union
  , ConsIfAbsent
  , Lookup
  , Names
  ) where

import GHC.TypeLits (CmpSymbol, ErrorMessage (..), Symbol, TypeError)

import PEG.Type

type family If (c :: Bool) (t :: k) (e :: k) :: k where
  If 'True  t _ = t
  If 'False _ e = e

type family And (a :: Bool) (b :: Bool) :: Bool where
  And 'True  b = b
  And 'False _ = 'False

type family Or (a :: Bool) (b :: Bool) :: Bool where
  Or 'True  _ = 'True
  Or 'False b = b

type family SymEq (a :: Symbol) (b :: Symbol) :: Bool where
  SymEq a b = IsEQ (CmpSymbol a b)

type family IsEQ (o :: Ordering) :: Bool where
  IsEQ 'EQ = 'True
  IsEQ _   = 'False

-- | Is @x@ a member of the sorted set @xs@?
--
-- Stops as soon as it reaches a symbol greater than @x@, so a miss costs
-- half a scan on average rather than a full one.
type family Elem (x :: Symbol) (xs :: [Symbol]) :: Bool where
  Elem _ '[]       = 'False
  Elem x (y ': ys) = ElemGo (CmpSymbol x y) x ys

type family ElemGo (o :: Ordering) (x :: Symbol) (ys :: [Symbol]) :: Bool where
  ElemGo 'EQ _ _  = 'True
  ElemGo 'LT _ _  = 'False
  ElemGo 'GT x ys = Elem x ys

-- | Insert @x@ into the sorted set @xs@, keeping it sorted and duplicate-free.
type family ConsIfAbsent (x :: Symbol) (xs :: [Symbol]) :: [Symbol] where
  ConsIfAbsent x '[]       = '[x]
  ConsIfAbsent x (y ': ys) = InsGo (CmpSymbol x y) x y ys

type family InsGo (o :: Ordering) (x :: Symbol) (y :: Symbol)
                  (ys :: [Symbol]) :: [Symbol] where
  InsGo 'LT x y ys = x ': y ': ys
  InsGo 'EQ _ y ys = y ': ys
  InsGo 'GT x y ys = y ': ConsIfAbsent x ys

-- | Union of two sorted sets: a single merge pass, @O(|xs| + |ys|)@.
--
-- The merge nests one type-family reduction per element of the result, so a
-- FIRST set of more than about a hundred non-terminals runs into GHC's
-- default reduction limit and reports @Reduction stack overflow@.  That is a
-- limit, not a slowdown: @-freduction-depth=0@ lifts it, and a union of two
-- 128-element sets then takes about 0.3 s.
type family Union (xs :: [Symbol]) (ys :: [Symbol]) :: [Symbol] where
  Union '[]       ys        = ys
  Union (x ': xs) '[]       = x ': xs
  Union (x ': xs) (y ': ys) = MergeGo (CmpSymbol x y) x xs y ys

type family MergeGo (o :: Ordering) (x :: Symbol) (xs :: [Symbol])
                    (y :: Symbol) (ys :: [Symbol]) :: [Symbol] where
  MergeGo 'LT x xs y ys = x ': Union xs (y ': ys)
  MergeGo 'EQ x xs _ ys = x ': Union xs ys
  MergeGo 'GT x xs y ys = y ': Union (x ': xs) ys

-- | Look up a non-terminal's entry in the environment.
--
-- This is the hot path: there is one lookup per occurrence of every
-- non-terminal in the grammar, so it is written to do as little as possible
-- per entry scanned.
--
-- Two things matter.  The search proper ('LookupMb') carries only the tail it
-- still has to scan — threading the /whole/ environment through it so the
-- not-found case could name the available non-terminals costs a traversal of
-- that environment at every step, and an environment of @n@ rules is itself
-- @O(n^2)@ type nodes because every rule carries a FIRST set.  The
-- environment is therefore named once, in 'Found', which only reduces after
-- the search has finished.
--
-- And the match is on a /non-linear/ pattern — @s@ appears twice in the
-- second clause — rather than on @CmpSymbol s t@ dispatched through a helper
-- family.  GHC decides the clause by syntactic equality and by apartness for
-- the fall-through, which is one type-family reduction per entry instead of
-- two.  (The trick is @Data.Type.Map@'s, from @type-level-sets@.)  It costs
-- nothing here: unlike 'Elem', this search has no sortedness to exploit, so
-- there was never a third case to short-circuit on.
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

type family Names (env :: Env) :: [Symbol] where
  Names '[]               = '[]
  Names ('(s, _) ': rest) = s ': Names rest
