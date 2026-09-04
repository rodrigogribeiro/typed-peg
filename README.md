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

On GHC 9.10.3 against megaparsec 9.8.1, on the largest input of each group
(mean of 100+ criterion samples, process pinned to one core):

| grammar | time vs. megaparsec `String` | bytes/input byte, typed-peg | megaparsec `String` |
|---|---|---|---|
| arithmetic | 0.99x | 990 | 1238 |
| CSV | 1.01x | 834 | 1035 |
| identifiers | 1.13x | 133 | 158 |
| JSON | 1.07x | 459 | 782 |
| nested parens | 0.99x | 265 | 1283 |
| `'"' [^"]* '"'` | 1.23x | 113 | 128 |
| `'"' (!'"' .)* '"'` | 2.15x | 162 | 128 |

typed-peg is faster than megaparsec over `Text` on every benchmark here.  Time
is the noisier of the two measurements: on a machine with heterogeneous cores,
unpinned runs of the *same* megaparsec binary varied by up to 1.8x, so only the
ratio taken within one run is meaningful.  Allocation is deterministic and
reproduces exactly.

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
