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

type family Elem (x :: Symbol) (xs :: [Symbol]) :: Bool where
  Elem _ '[]       = 'False
  Elem x (y ': ys) = Or (SymEq x y) (Elem x ys)

type family ConsIfAbsent (x :: Symbol) (xs :: [Symbol]) :: [Symbol] where
  ConsIfAbsent x xs = If (Elem x xs) xs (x ': xs)

type family Union (xs :: [Symbol]) (ys :: [Symbol]) :: [Symbol] where
  Union '[]       ys = ys
  Union (x ': xs) ys = ConsIfAbsent x (Union xs ys)

type family Lookup (s :: Symbol) (env :: Env) :: EnvEntry where
  Lookup s env = LookupGo s env env

type family LookupGo (s :: Symbol) (env :: Env) (full :: Env) :: EnvEntry where
  LookupGo s '[] full =
    TypeError ('Text "Undefined non-terminal: " ':<>: 'ShowType s
         ':$$: 'Text "Available non-terminals: " ':<>: 'ShowType (Names full))
  LookupGo s ('(t, e) ': rest) full = LookupStep (SymEq s t) s e rest full

type family LookupStep (b :: Bool) (s :: Symbol) (e :: EnvEntry)
                       (rest :: Env) (full :: Env) :: EnvEntry where
  LookupStep 'True  _ e _    _    = e
  LookupStep 'False s _ rest full = LookupGo s rest full

type family Names (env :: Env) :: [Symbol] where
  Names '[]               = '[]
  Names ('(s, _) ': rest) = s ': Names rest
