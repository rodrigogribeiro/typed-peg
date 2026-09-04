{-# LANGUAGE BangPatterns #-}

-- | Compact character sets used by the 'PEG.Syntax.Sat' combinator.
--
-- A character class such as @[a-zA-Z0-9_]@ used to be compiled into a chain of
-- 63 ordered choices, so matching a single character could cost 63 parser
-- steps.  A 'CharSet' answers the same question with one bit test.
--
-- The Latin-1 range (@\\0@ .. @\\255@), which covers essentially every class
-- that appears in a practical grammar, is stored as a 256-bit bitmap held in
-- four 'Word64's.  Characters above that range fall back to a list of ranges.
module PEG.CharSet
  ( CharSet (..)
  , memberCS
  , fromRanges
  , notInRanges
  , fromList
  , singletonCS
  , complementCS
  , nullCS
  ) where

import Data.Bits (setBit, testBit)
import Data.Char (chr, ord)
import Data.Word (Word64)

-- | A set of characters.  The four 'Word64' fields form a bitmap of the
-- Latin-1 range; 'csWide' holds any ranges that reach beyond it.
--
-- Negation is a flag rather than an actual complement, so a negated class is
-- exactly as cheap to test as a positive one and stays exact for the whole of
-- 'Char' (complementing the ranges above Latin-1 explicitly would not).
data CharSet = CharSet
  { csNeg  :: !Bool
  , csB0   :: !Word64
  , csB1   :: !Word64
  , csB2   :: !Word64
  , csB3   :: !Word64
  , csWide :: ![(Char, Char)]
  }
  deriving (Eq, Show)

-- | Is the character a member of the set?  @O(1)@ for Latin-1 characters.
memberCS :: Char -> CharSet -> Bool
memberCS c cs = csNeg cs /= rawMember c cs
{-# INLINE memberCS #-}

-- | Membership ignoring the negation flag.
rawMember :: Char -> CharSet -> Bool
rawMember c (CharSet _ b0 b1 b2 b3 wide)
  | n < 64    = testBit b0 n
  | n < 128   = testBit b1 (n - 64)
  | n < 192   = testBit b2 (n - 128)
  | n < 256   = testBit b3 (n - 192)
  | otherwise = inWide wide
  where
    !n = ord c
    inWide []              = False
    inWide ((lo, hi) : rs) = (n >= ord lo && n <= ord hi) || inWide rs
{-# INLINE rawMember #-}

-- | Build a set from a list of inclusive character ranges.
fromRanges :: [(Char, Char)] -> CharSet
fromRanges = mkRanges False

-- | The complement of 'fromRanges': every character /outside/ the given
-- ranges.  This is what the quasi-quoter emits for @[^\"]@.
notInRanges :: [(Char, Char)] -> CharSet
notInRanges = mkRanges True

-- | Flip a set\'s polarity.
complementCS :: CharSet -> CharSet
complementCS cs = cs { csNeg = not (csNeg cs) }

mkRanges :: Bool -> [(Char, Char)] -> CharSet
mkRanges neg rs = CharSet neg (word 0) (word 64) (word 128) (word 192) wide
  where
    lows = [ n | (lo, hi) <- rs, n <- [ord lo .. min 255 (ord hi)] ]

    word base = go 0 lows
      where
        go !w []       = w
        go !w (n : ns)
          | n >= base && n < base + 64 = go (setBit w (n - base)) ns
          | otherwise                  = go w ns

    wide = [ (max lo (chr 256), hi) | (lo, hi) <- rs, ord hi > 255 ]

-- | Build a set from an explicit list of characters.
fromList :: [Char] -> CharSet
fromList cs = fromRanges [ (c, c) | c <- cs ]

-- | The set containing exactly one character.
singletonCS :: Char -> CharSet
singletonCS c = fromRanges [(c, c)]

-- | Is the set empty?
nullCS :: CharSet -> Bool
nullCS (CharSet False 0 0 0 0 []) = True
nullCS _                          = False
