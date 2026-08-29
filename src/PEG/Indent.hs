{-# LANGUAGE DataKinds      #-}
{-# LANGUAGE KindSignatures #-}

-- | Indentation-sensitive parsing via column intervals and relations.
--
-- This module implements the algebraic model of indentation from
-- /Layout-sensitive grammars and combinators/ (Adams, 2013).
-- Columns are represented as integer positions; valid columns are maintained
-- as an 'Interval'.  Each parser step filters the interval through a 'RelD'
-- (a monotone column relation), allowing constructs such as \"must be
-- indented more than the enclosing block\".
--
-- == Predefined relations
--
-- * 'eqR'    — same column (align with enclosing block)
-- * 'geR'    — greater-or-equal column (standard indented block)
-- * 'gtR'    — strictly greater column
-- * 'anyR'   — any column (no constraint)
-- * 'gapR'   — indented by a fixed offset
-- * 'constR' — fixed column
-- * 'offsetR'— shifted by @k@ columns
module PEG.Indent
  ( Bound (..)
  , Interval (..)
  , emptyI
  , fullI
  , singletonI
  , nullI
  , memberI
  , interI
  , RelD (..)
  , Rel (..)
  , relName
  , image
  , preimage
  , eqR
  , gtR
  , geR
  , anyR
  , gapR
  , constR
  , offsetR
  ) where

import GHC.TypeLits (Symbol)

data Bound = Fin !Int | Inf
  deriving (Eq, Show)

instance Ord Bound where
  compare Inf     Inf     = EQ
  compare Inf     (Fin _) = GT
  compare (Fin _) Inf     = LT
  compare (Fin a) (Fin b) = compare a b

data Interval = Interval { ivLo :: !Int, ivHi :: !Bound }
  deriving (Eq, Show)

emptyI :: Interval
emptyI = Interval 1 (Fin 0)

fullI :: Interval
fullI = Interval 0 Inf

singletonI :: Int -> Interval
singletonI i = Interval i (Fin i)

nullI :: Interval -> Bool
nullI (Interval lo hi) = Fin lo > hi

memberI :: Int -> Interval -> Bool
memberI i (Interval lo hi) = i >= lo && Fin i <= hi

interI :: Interval -> Interval -> Interval
interI (Interval l1 h1) (Interval l2 h2) = Interval (max l1 l2) (min h1 h2)

data RelD = RelD
  { rdName      :: String
  , rdDom       :: Interval
  , rdLo        :: Int -> Int
  , rdHi        :: Int -> Bound
  , rdInvLo     :: Int -> Int
  , rdInvHi     :: Int -> Bound
  , rdModeLo    :: Bound
  , rdModeHi    :: Bound
  , rdModeInvLo :: Bound
  , rdModeInvHi :: Bound
  }

newtype Rel (n :: Symbol) = Rel { relD :: RelD }

relName :: Rel n -> String
relName = rdName . relD

instance Show (Rel n) where
  show = relName

clampMode :: Bound -> Interval -> Maybe Int
clampMode (Fin m) (Interval lo hi) = Just $ case hi of
  Inf   -> max lo m
  Fin h -> max lo (min m h)
clampMode Inf     (Interval lo hi) = case hi of
  Inf   -> Nothing
  Fin h -> Just (max lo h)

supOver :: Bound -> (Int -> Bound) -> Interval -> Bound
supOver mode f iv = maybe Inf f (clampMode mode iv)

infOver :: Bound -> (Int -> Int) -> Interval -> Int
infOver mode f iv = maybe 0 f (clampMode mode iv)

image :: RelD -> Interval -> Interval
image rd i0
  | nullI i   = emptyI
  | otherwise = Interval (infOver (rdModeLo rd) (rdLo rd) i)
                         (supOver (rdModeHi rd) (rdHi rd) i)
  where
    i = interI i0 (rdDom rd)

preimage :: RelD -> Interval -> Interval
preimage rd i
  | nullI i   = emptyI
  | otherwise = Interval (infOver (rdModeInvLo rd) (rdInvLo rd) i)
                         (supOver (rdModeInvHi rd) (rdInvHi rd) i)

eqR :: Rel "="
eqR = Rel RelD
  { rdName      = "="
  , rdDom       = fullI
  , rdLo        = id
  , rdHi        = Fin
  , rdInvLo     = id
  , rdInvHi     = Fin
  , rdModeLo    = Fin 0
  , rdModeHi    = Inf
  , rdModeInvLo = Fin 0
  , rdModeInvHi = Inf
  }

gapR :: Int -> Rel "gap"
gapR = Rel . gapD "gap"

gapD :: String -> Int -> RelD
gapD name k = RelD
  { rdName      = name
  , rdDom       = Interval k Inf
  , rdLo        = const 0
  , rdHi        = \i -> Fin (i - k)
  , rdInvLo     = \i -> i + k
  , rdInvHi     = const Inf
  , rdModeLo    = Fin 0
  , rdModeHi    = Inf
  , rdModeInvLo = Fin 0
  , rdModeInvHi = Fin 0
  }

gtR :: Rel ">"
gtR = Rel (gapD ">" 1)

geR :: Rel ">="
geR = Rel (gapD ">=" 0)

anyR :: Rel "~"
anyR = Rel RelD
  { rdName      = "~"
  , rdDom       = fullI
  , rdLo        = const 0
  , rdHi        = const Inf
  , rdInvLo     = const 0
  , rdInvHi     = const Inf
  , rdModeLo    = Fin 0
  , rdModeHi    = Fin 0
  , rdModeInvLo = Fin 0
  , rdModeInvHi = Fin 0
  }

constR :: Int -> Rel "const"
constR c = Rel RelD
  { rdName      = "const " ++ show c
  , rdDom       = singletonI c
  , rdLo        = const 0
  , rdHi        = const Inf
  , rdInvLo     = const c
  , rdInvHi     = const (Fin c)
  , rdModeLo    = Fin 0
  , rdModeHi    = Fin 0
  , rdModeInvLo = Fin 0
  , rdModeInvHi = Fin 0
  }

offsetR :: Int -> Rel "offset"
offsetR k = Rel RelD
  { rdName      = "+" ++ show k
  , rdDom       = Interval k Inf
  , rdLo        = \i -> i - k
  , rdHi        = \i -> Fin (i - k)
  , rdInvLo     = \i -> i + k
  , rdInvHi     = \i -> Fin (i + k)
  , rdModeLo    = Fin 0
  , rdModeHi    = Inf
  , rdModeInvLo = Fin 0
  , rdModeInvHi = Inf
  }
