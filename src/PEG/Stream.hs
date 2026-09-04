{-# LANGUAGE BangPatterns      #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MagicHash         #-}
{-# LANGUAGE UnboxedSums       #-}
{-# LANGUAGE UnboxedTuples     #-}

-- | Input streams the parser can consume.
--
-- A 'Stream' is anything the parser can read one 'Char' at a time and slice
-- chunks out of.  Instances are provided for 'String', strict and lazy
-- 'Data.Text.Text', and strict and lazy 'Data.ByteString.ByteString'.
--
-- == ByteString is Latin-1
--
-- The 'ByteString' instances read each byte as the 'Char' with that code
-- point, exactly as "Data.ByteString.Char8" does.  This is what makes them
-- fast — every character lands in the Latin-1 range that
-- "PEG.CharSet" answers with a single bit test — and it is correct for
-- grammars over ASCII or Latin-1 text.  It is /wrong/ for UTF-8: a
-- multi-byte character arrives as its individual bytes, and columns and
-- offsets count bytes rather than characters.  Decode to 'Data.Text.Text'
-- first if that matters.
--
-- Two laws follow, and only the 'ByteString' instances need the caveat:
--
-- * @'chunkToString' . 'packString' == 'id'@, for arguments in the range the
--   stream can represent (all of 'Char' except for 'ByteString', where it is
--   @\'\\0\'@ .. @\'\\255\'@).
-- * A 'PEG.CharSet.CharSet' containing only characters above @\'\\255\'@
--   never matches a 'ByteString', with no diagnostic.
--
-- == Writing an instance
--
-- Only 'unconsS' has no default.  Everything else is derived from it, so a
-- minimal instance is one method — but a type with native slicing should
-- override 'spanS', 'takeS', 'lengthS' and 'foldlS'' , which is where the
-- performance of 'Text' and 'ByteString' comes from.
module PEG.Stream
  ( Stream (..)
  ) where

import Data.Char (chr, ord)

import qualified Data.ByteString            as B
import qualified Data.ByteString.Char8      as BC
import qualified Data.ByteString.Lazy       as BL
import qualified Data.ByteString.Lazy.Char8 as BLC
import qualified Data.Text                  as T
import qualified Data.Text.Lazy             as TL

-- | A sequence of characters the parser can consume.
--
-- The chunk type is the stream type itself: slicing a 'Data.Text.Text'
-- yields a 'Data.Text.Text', so a character class such as @[a-z]+@ produces
-- a real slice rather than unpacking into a @['Char']@.
class Stream s where
  -- | Split off the first character.
  --
  -- This returns an unboxed sum rather than @'Maybe' ('Char', s)@ on
  -- purpose.  It is called once per character of input, and the boxed
  -- version would allocate a @Just@ and a pair every time — behind a class
  -- dictionary GHC cannot cancel them, so the parser's zero-allocation
  -- terminal path would be lost.
  unconsS :: s -> (# (# #) | (# Char, s #) #)

  -- | @'spanS' p s@ splits @s@ into the longest prefix all of whose
  -- characters satisfy @p@, and the rest.
  spanS :: (Char -> Bool) -> s -> (s, s)

  -- | Strict left fold over the characters.  Used to advance the column
  -- across a chunk that has already been matched in bulk.
  foldlS' :: (b -> Char -> b) -> b -> s -> b

  -- | Prepend a character.  @O(1)@ for 'String' and the lazy types; the
  -- strict types must copy.
  consS :: Char -> s -> s

  -- | @'takeS' n s@ is the first @n@ characters of @s@.
  takeS :: Int -> s -> s

  -- | Number of characters.
  lengthS :: s -> Int

  -- | Is the stream empty?
  nullS :: s -> Bool

  -- | Convert a chunk to a 'String'.  Semantic actions need this whenever a
  -- character class feeds something that expects a 'String', such as 'read'.
  chunkToString :: s -> String

  -- | Build a chunk from a 'String'.
  packString :: String -> s

  -- Defaults, all in terms of 'unconsS'.

  spanS p s0 = go id s0
    where
      go acc s = case unconsS s of
        (# | (# c, s' #) #) | p c -> go (acc . (c :)) s'
        _                         -> (packString (acc []), s)

  foldlS' f = go
    where
      go !acc s = case unconsS s of
        (# | (# c, s' #) #) -> go (f acc c) s'
        _                   -> acc

  consS c s = packString (c : chunkToString s)

  takeS n0 s0 = packString (go n0 s0)
    where
      go n s
        | n <= 0    = []
        | otherwise = case unconsS s of
            (# | (# c, s' #) #) -> c : go (n - 1) s'
            _                   -> []

  lengthS = foldlS' (\ !n _ -> n + 1) 0

  nullS s = case unconsS s of
    (# (# #) | #) -> True
    _             -> False

  chunkToString s = case unconsS s of
    (# | (# c, s' #) #) -> c : chunkToString s'
    _                   -> []

  {-# MINIMAL unconsS, packString #-}

--------------------------------------------------------------------------------
-- String
--------------------------------------------------------------------------------

instance Stream [Char] where
  unconsS (c : cs) = (# | (# c, cs #) #)
  unconsS []       = (# (# #) | #)
  {-# INLINE unconsS #-}

  -- NOT 'Data.List.span': that one is lazy in its pair, so it allocates a
  -- tuple and two selector thunks for every character it accepts.  Finding
  -- the split point first and slicing costs one tuple in total.
  spanS p s0    = go (0 :: Int) s0
    where
      go !n s = case s of
        (c : cs) | p c -> go (n + 1) cs
        _              -> (take n s0, s)
  foldlS' f     = go
    where
      go !acc (c : cs) = go (f acc c) cs
      go !acc []       = acc
  consS         = (:)
  takeS         = take
  lengthS       = length
  nullS         = null
  chunkToString = id
  packString    = id
  {-# INLINE spanS #-}
  {-# INLINE foldlS' #-}
  {-# INLINE consS #-}
  {-# INLINE takeS #-}
  {-# INLINE lengthS #-}
  {-# INLINE nullS #-}
  {-# INLINE chunkToString #-}
  {-# INLINE packString #-}

--------------------------------------------------------------------------------
-- Text
--------------------------------------------------------------------------------

instance Stream T.Text where
  unconsS t = case T.uncons t of
    Just (c, t') -> (# | (# c, t' #) #)
    Nothing      -> (# (# #) | #)
  {-# INLINE unconsS #-}

  spanS         = T.span
  foldlS'       = T.foldl'
  consS         = T.cons
  takeS         = T.take
  lengthS       = T.length
  nullS         = T.null
  chunkToString = T.unpack
  packString    = T.pack
  {-# INLINE spanS #-}
  {-# INLINE foldlS' #-}
  {-# INLINE takeS #-}
  {-# INLINE lengthS #-}
  {-# INLINE nullS #-}

instance Stream TL.Text where
  unconsS t = case TL.uncons t of
    Just (c, t') -> (# | (# c, t' #) #)
    Nothing      -> (# (# #) | #)
  {-# INLINE unconsS #-}

  spanS         = TL.span
  foldlS'       = TL.foldl'
  consS         = TL.cons
  takeS n       = TL.take (fromIntegral n)
  lengthS       = fromIntegral . TL.length
  nullS         = TL.null
  chunkToString = TL.unpack
  packString    = TL.pack
  {-# INLINE spanS #-}
  {-# INLINE foldlS' #-}
  {-# INLINE nullS #-}

--------------------------------------------------------------------------------
-- ByteString (Latin-1)
--------------------------------------------------------------------------------

-- | Byte to character, Latin-1.
w2c :: Int -> Char
w2c = chr
{-# INLINE w2c #-}

instance Stream B.ByteString where
  unconsS b = case B.uncons b of
    Just (w, b') -> (# | (# w2c (fromIntegral w), b' #) #)
    Nothing      -> (# (# #) | #)
  {-# INLINE unconsS #-}

  spanS         = BC.span
  foldlS'       = BC.foldl'
  consS         = BC.cons
  takeS         = B.take
  lengthS       = B.length
  nullS         = B.null
  chunkToString = BC.unpack
  -- 'BC.pack' truncates characters above '\255'; clamp explicitly so the
  -- behaviour is the documented one rather than whatever pack happens to do.
  packString    = BC.pack . map clampLatin1
  {-# INLINE spanS #-}
  {-# INLINE foldlS' #-}
  {-# INLINE takeS #-}
  {-# INLINE lengthS #-}
  {-# INLINE nullS #-}

instance Stream BL.ByteString where
  unconsS b = case BL.uncons b of
    Just (w, b') -> (# | (# w2c (fromIntegral w), b' #) #)
    Nothing      -> (# (# #) | #)
  {-# INLINE unconsS #-}

  spanS         = BLC.span
  foldlS'       = BLC.foldl'
  consS         = BLC.cons
  takeS n       = BL.take (fromIntegral n)
  lengthS       = fromIntegral . BL.length
  nullS         = BL.null
  chunkToString = BLC.unpack
  packString    = BLC.pack . map clampLatin1
  {-# INLINE spanS #-}
  {-# INLINE foldlS' #-}
  {-# INLINE nullS #-}

-- | Characters a 'ByteString' cannot represent become @\'\\255\'@ rather
-- than silently wrapping around modulo 256.
clampLatin1 :: Char -> Char
clampLatin1 c
  | ord c > 255 = '\255'
  | otherwise   = c
{-# INLINE clampLatin1 #-}
