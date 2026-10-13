{-# LANGUAGE BangPatterns #-}

-- | Lines and columns, computed from offsets.
--
-- The parser tracks only an offset — the number of characters consumed — and
-- 'PEG.Syntax.GetOffset' (@\@@ in the quasi-quoter) hands it to a semantic
-- action.  Lines are not tracked while parsing, so a grammar that never asks
-- for a position pays nothing for them.  Turning an offset into a line and a
-- column is done here, against the original input:
--
-- @
-- let idx = 'lineIndex' input       -- once per input
-- 'lineCol' idx off                 -- O(log lines) per lookup
-- @
--
-- Lines and columns are both counted from 1.  Every character, a tab
-- included, advances the column by one; this is the convention of most
-- editors' \"go to column\", not the tab-stop column "PEG.Indent" uses for
-- layout.  On a 'Data.ByteString.ByteString' an offset counts bytes, as
-- everything else does; see "PEG.Stream".
module PEG.Location
  ( LineIndex
  , lineIndex
  , lineCol
  , offsetToLineCol
  ) where

import qualified Data.IntMap.Strict as IM

import PEG.Stream (Stream (..))

-- | Where each line of an input starts: the offset of its first character,
-- mapped to its line number.
newtype LineIndex = LineIndex (IM.IntMap Int)

-- | Index the lines of an input.  One pass over it.
lineIndex :: Stream s => s -> LineIndex
lineIndex s = LineIndex (IM.fromList ((0, 1) : starts))
  where
    -- The fold keeps the offset and line of the next character; a newline
    -- starts a line at the offset after it.
    (_, _, starts) = foldlS' step (0 :: Int, 1 :: Int, []) s
    step (!off, !ln, acc) c
      | c == '\n' = (off + 1, ln + 1, (off + 1, ln + 1) : acc)
      | otherwise = (off + 1, ln, acc)

    -- 'IM.fromList' rather than 'IM.fromDistinctAscList': the fold collects
    -- the starts last first.

-- | The line and column, both from 1, of the character at an offset.
--
-- An offset past the end of the input is placed on the last line, as if that
-- line went on.
lineCol :: LineIndex -> Int -> (Int, Int)
lineCol (LineIndex m) off = case IM.lookupLE off m of
  Just (start, ln) -> (ln, off - start + 1)
  Nothing          -> (1, off + 1)   -- a negative offset; not produced by 'parse'

-- | @'lineCol' . 'lineIndex'@, for a single lookup.  Indexing costs a pass
-- over the input, so build a 'LineIndex' once when there are many offsets to
-- convert.
offsetToLineCol :: Stream s => s -> Int -> (Int, Int)
offsetToLineCol s = lineCol (lineIndex s)
