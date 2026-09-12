# typed-peg

Type-safe PEG (Parsing Expression Grammar) parser combinators for Haskell.

Grammar non-terminals are checked at the type level against an environment
that binds each rule to the type it returns, and left-recursive grammars are
caught when the grammar is written rather than looping at runtime.

## Features

- Non-terminal references checked at the type level
- Left recursion, a repetition that cannot consume input, an undefined
  non-terminal and a duplicate rule reported at the splice, naming the rule
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
import PEG.QQ (pegGrammar)

data Exp = Lit Int | Add Exp Exp | Mul Exp Exp

[pegGrammar|
  %name  arith
  %start expr

  expr   :: Exp <- t:term ts:(o:[+] u:term)*     { foldl addOp t ts }
  term   :: Exp <- f:factor fs:(o:[*] g:factor)* { foldl addOp f fs }
  factor :: Exp <- n:number / '(' e:expr ')'
  number :: Exp <- ds:[0-9]+ { Lit (read (chunkToString ds)) }
|]
```

That declares three things: `type ArithEnv s`, the signature
`arith :: Stream s => Grammar s (ArithEnv s) Exp`, and `arith` itself.  Run
it with `parse arith "1+2*3"`.

A rule's **result type** is the one thing the grammar does not determine — it
comes from the Haskell in the semantic action — which is what the `:: T`
annotations are for.  They are claims, and GHC checks them: `Grammar` demands
`Rules s env env`, so an annotation that disagrees with what the body returns
is a type error.

`pegRules` remains, for a rule set that is only part of a grammar or that is
combined with hand-written `PExp` combinators.  It needs the environment
written out by hand; `examples/Compat.hs` and `examples/Patterns.hs` show
that style.  See `examples/Arith.hs` and `examples/Layout.hs` for the
generated one.

## Grammar size, and what is checked where

A grammar's size shows up as compile time, because every reference in it is a
constraint GHC has to solve against the environment.  An entry of that
environment is a rule's name and the type it returns:

```haskell
type CalcEnv =
  '[ '("expr" , 'EnvEntry Expr)
   , '("term" , 'EnvEntry Expr)
   , '("unary", 'EnvEntry Expr)
   , '("atom" , 'EnvEntry Expr)
   ]
```

Entries used to carry more: each rule's nullability and its FIRST set, the
non-terminals that can begin it.  That is what made left recursion a type
error — an `Acyclic` constraint checked that no rule was in its own FIRST set
— and it was also, measurably, the entire cost of compiling a large grammar.
A FIRST set grows with the grammar, so the environment was quadratic in the
number of rules, and each of the two reference constraints per rule was solved
against the whole of it.  Removing it took a 64-rule grammar from 15 s to 2 s,
and a 128-rule one from more than two minutes to 5 s.  `bench-compile/` has
the measurements.

Nullability and FIRST sets are still computed — by `PEG.Analysis`, in ordinary
Haskell, when the quasi-quoter runs, in 6 ms for a 64-rule grammar.  It is
what reports left recursion, a nullable repetition, an undefined non-terminal
or a duplicate rule **from the splice**, naming the rule and the chain of head
references that closes the cycle:

```
Arith.hs:8:13: error: [GHC-39584]
    • pegRules:
      left-recursive non-terminal: expr
        the cycle is expr -> term -> factor -> expr
        a PEG cannot backtrack into a committed choice, so this rule
        would not consume input before calling itself
```

So the checks divide like this:

| what | checked by | when |
|---|---|---|
| a reference names a rule that exists, at the right type | GHC | every compilation |
| a rule's `:: T` annotation matches what its body returns | GHC | every compilation |
| left recursion, nullable repetition, duplicate rule | `PEG.Analysis` | at the splice |

The second half of that table is the trade.  A `Rules` chain assembled by hand
from `RCons`, without a quasi-quoter, is checked for reference errors only: a
rule that begins with itself compiles and loops.  And `pegRules` analyses its
block open-world, since two blocks can be combined, so left recursion that
closes *across* two blocks is reported by neither it nor GHC.  Writing the
grammar as one `pegGrammar` closes both gaps — it is closed-world, so every
reference resolves and every cycle is visible — and it is also the fastest to
compile, because it knows each rule's position and emits the membership proof
instead of a `KnownMember` search.

Since nothing recomputes what `PEG.Analysis` concludes, the
`typed-peg-analysis` test-suite checks it against a separate statement of what
nullability and a FIRST set mean, over the grammars in `examples/` and a few
hundred generated ones.

## Patterns

[`peg-patterns.md`](peg-patterns.md) works through patterns for specifying
languages with PEGs and this library, following Willis and Wu's *Design
Patterns for Parser Combinators* (Haskell 2021) and noting where a PEG differs
— committed choice, left recursion as a type error, keywords as negative
lookahead — and where typed-peg cannot yet follow.  Every fragment in it
compiles, in [`examples/Patterns.hs`](examples/Patterns.hs).

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
