# typed-peg

Type-safe PEG (Parsing Expression Grammar) parser combinators for Haskell.

Grammar non-terminals are indexed at the type level by their nullability and
FIRST sets, so left-recursive grammars are caught at compile time rather than
looping at runtime.

## Features

- Type-level FIRST-set and nullability tracking
- Compile-time left-recursion detection (type error)
- Indentation-sensitive parsing (`PEG.Indent`)
- Quasi-quoter for concrete grammar syntax (`PEG.QQ`)
- Parses any `PEG.Stream`: `String`, strict/lazy `Text`, strict/lazy
  `ByteString`

## Input streams

A grammar is written once and runs over any stream:

```haskell
import qualified Data.Text as T

parse arith "1+2*3"              -- Result String Exp
parse arith (T.pack "1+2*3")     -- Result Text   Exp
```

Character classes produce a **chunk of the stream**, not a `[Char]`: matching
`[a-z]+` against a `Text` yields a `Text` slice and copies nothing.  Semantic
actions that want a `String` ask for one:

```haskell
number <- ds:[0-9]+   { Lit (read (chunkToString ds)) }
strlit <- '"' cs:[^"]* '"'   { cs }     -- :: s, no copy
```

Only `unconsS` has no default, so adding a stream is one method.

`ByteString` is read as Latin-1, like `Data.ByteString.Char8`: fast and
correct for ASCII, wrong for multi-byte UTF-8.  Decode to `Text` if that
matters.

A `Grammar` is monomorphic in its stream.  To reuse one across several, give
it a `forall s. Stream s => Grammar s Env _ A` signature — but note that makes
it a function of a dictionary, so the compiled parser is no longer shared
between calls.  Bind a monomorphic parser where that matters:

```haskell
arithString :: String -> Result String Exp
arithString = parse arith
{-# NOINLINE arithString #-}
```

## Quick start

```haskell
import PEG

-- Define a grammar using the quasi-quoter
-- See examples/Arith.hs for a complete arithmetic expression parser
```

## Building

```bash
cabal build
```

## Examples

```bash
cabal test typed-peg-examples
```

## Benchmarks

`bench/` holds a criterion suite that measures typed-peg against
[megaparsec](https://hackage.haskell.org/package/megaparsec) on seven grammars
(arithmetic expressions, CSV, identifier lists, a mini JSON, deeply nested
parentheses, and quoted strings spelled two ways) written twice, rule for
rule.  Both libraries consume byte-identical inputs, and the suite
cross-checks that they produce the same result before timing anything.

```bash
cabal bench
```

`cabal bench --benchmark-options=--alloc` prints bytes allocated per parse
instead of running criterion; allocation is the number that separates the two
libraries most clearly once the algorithmic differences are gone.

On GHC 9.10.3 against megaparsec 9.8.1, bytes allocated per input byte on the
largest input of each group:

| grammar | typed-peg `String` | `Text` | `ByteString` | megaparsec `String` |
|---|---|---|---|---|
| arithmetic | 943 | 1127 | 969 | 1239 |
| CSV | 787 | 951 | 805 | 1035 |
| identifiers | 100 | 190 | 84 | 179 |
| JSON | 404 | 583 | 452 | 782 |
| nested parens | 312 | 481 | 336 | 1283 |
| `'"' [^"]* '"'` | 90 | 167 | 65 | 128 |
| `'"' (!'"' .)* '"'` | 209 | 320 | 250 | 128 |

`ByteString` is the cheapest column on five of the seven grammars and beats
megaparsec on six.  `Text` costs more than `String` throughout — the same
result the study found for megaparsec, so reach for it for interoperability
rather than for speed.

Allocation is deterministic and reproduces exactly.  Time is the noisier
measurement: on a machine with heterogeneous cores, unpinned runs of the
*same* megaparsec binary varied by up to 1.8x, so only the ratio taken within
one run is meaningful.

The reference implementation is `Bench.Peg`; its megaparsec twin is
`Bench.Mega`.  Since PEG ordered choice backtracks unconditionally while
megaparsec's `<|>` does not, every megaparsec alternative that can consume
input before failing is wrapped in `try`, so the two are recognising the same
language.

### Parsing many inputs

`parseWith opts grammar` traverses the grammar and returns a compiled closure.
Bind it once and reuse it, rather than calling `parse grammar input` inline in
a loop:

```haskell
myParser :: String -> Result Exp
myParser = parse myGrammar
```

## License

BSD-3-Clause. See [LICENSE](LICENSE).
