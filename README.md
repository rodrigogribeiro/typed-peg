# typed-peg

Type-safe PEG (Parsing Expression Grammar) parser combinators for Haskell.

Grammar non-terminals are checked at the type level — a reference is a key
whose type is the result of the rule it names — and left-recursive grammars
are caught when the grammar is written rather than looping at runtime.
Checking a grammar costs GHC time and memory linear in its size: a 1024-rule
grammar type-checks in about a second.

## Features

- Non-terminal references checked at the type level
- Left recursion, a repetition that cannot consume input, an undefined
  non-terminal and a duplicate rule reported at the splice, naming the rule
- Indentation-sensitive parsing (`PEG.Indent`)
- Quasi-quoter for concrete grammar syntax (`PEG.QQ`)
- Source positions in semantic actions (`@`, `PEG.Location`)
- Syntax errors reported with a line and a column — the furthest point the
  parse reached — what was found there and what was expected, with rules
  named by `%label`
- Parses any `PEG.Stream`: `String`, strict/lazy `Text`, strict/lazy
  `ByteString`

## Source positions

`@` consumes nothing and returns the current offset, the number of characters
consumed so far.  Label it to give an action the position of what follows,
and turn offsets into lines and columns with `PEG.Location`:

```haskell
[pegGrammar|
  %name   lang
  %stream String
  %param  idx :: LineIndex
  %start  stmt

  stmt :: Stmt <- p:@ v:name ":=" ws e:expr   { Assign (lineCol idx p) v e }
  ...
|]

parse (lang (lineIndex src)) src
```

Lines and columns count from 1.  The parser tracks only the offset, so a
grammar that does not use `@` pays nothing for it.

## Syntax errors

A parse that fails says where, what it found there, and what it expected:

```haskell
data Result s a = OK a s s | Fail !ParseError

data ParseError = ParseError
  { errLine, errColumn, errOffset :: !Int
  , errFound    :: Found          -- a word, a character, or the end
  , errExpected :: [Expected]     -- 'x', "while", [0-9], end of input, a label
  }

renderParseError :: ParseError -> String
```

`%label` names a rule in that list, and `%label rule ""` keeps it out — which
is what whitespace wants:

```haskell
[pegGrammar|
  %name   prog
  %stream String
  %start  ss:prog !.
  %label  factor "an operand"
  %label  name   "a name"
  %label  ws     ""
  ...
|]
```

`renderParseError` on three inputs that do not parse:

```
x := (1 + 2;                1:12: unexpected ';', expecting [0-9], '*', '+' or ')'
x := 1;                     2:11: unexpected ')', expecting an operand
y := (2 + ) * x;
x := 1;                     2:10: unexpected '@', expecting "print", a name or end of input
print x; @
```

A label replaces what its rule looked for when the rule *starts* at the
error; one that started earlier lists what it looked for, which is more
precise — above, one more digit would have continued the `2`.

The position is the **furthest** point at which any part of the grammar
failed to match — an ordered choice backtracks before it tries its next
alternative, so the point where the start expression finally gave up is
usually the start of a rule, well before the mistake.  A string literal fails
where it starts; nothing inside a lookahead (`!e`, `&e`) counts.  End the start
expression with `!.` to make leftover input an error rather than `rest`.

Only the offset is tracked while parsing; the line and column are computed
once, when the parse has failed.  What was expected is found by running the
grammar a second time, after a failure and only if `errExpected` is looked
at, so a parse that succeeds costs exactly what it did without any of this.

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
it a `forall s. Stream s => Grammar s (Env s) A` signature — but note that makes
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

That declares the grammar's key type, one constructor per rule,

```haskell
data ArithEnv s a where
  ArithEnv_expr   :: ArithEnv s Exp
  ArithEnv_term   :: ArithEnv s Exp
  ...
```

a binding per rule (`arith'expr :: Stream s => PExp s (ArithEnv s) Exp`, ...),
and `arith :: Stream s => Grammar s (ArithEnv s) Exp`.  Run it with
`parse arith "1+2*3"`.  The module needs `GADTs`.

A rule's **result type** is the one thing the grammar does not determine — it
comes from the Haskell in the semantic action — which is what the `:: T`
annotations are for.  They are claims, and GHC checks them: each is the
signature of that rule's binding, so an annotation that disagrees with what the
body returns is a type error reported against the rule.

A grammar that needs a value from outside — a file name for error positions,
a table of operators — takes it as a parameter:

```haskell
[pegGrammar|
  %name   lang
  %stream String
  %param  file :: FilePath
  %start  program
  ...
|]
-- lang :: FilePath -> Grammar String (LangEnv String) Program
```

`pegRules` remains, for a rule set that is only part of a grammar or that is
combined with hand-written `PExp` combinators.  Its non-terminals are a
type-level list written out by hand, and the grammar is a
`Grammar s (InEnv env) a`; `examples/Compat.hs` and `examples/Patterns.hs`
show that style.  See `examples/Arith.hs`, `examples/Layout.hs` and
`examples/MiniPython.hs` for the generated one.

## Grammar size, and what is checked where

A grammar's size shows up as compile time, because every reference in it is a
constraint GHC has to solve.  How much each one costs depends on what the
reference points into.

**A declared key type** — what `pegGrammar` generates — makes a reference a
constructor, `NT ArithEnv_term`, whose type GHC checks without looking at the
rest of the grammar.  The cost is linear in the number of rules
(`ghc -fno-code`, GHC 9.10; `bench-compile/`):

| rules | through a key type | through a type-level list |
|---|---|---|
| 64   | 0.44 s,  49 MiB | 1.10 s,   375 MiB |
| 128  | 0.50 s,  51 MiB | 5.74 s, 2 298 MiB |
| 256  | 0.57 s,  80 MiB | exhausts 8 GB |
| 1024 | 1.17 s, 159 MiB | — |

The 27-rule MiniPython grammar in `examples/` takes 0.43 s and 57 MiB.

**A type-level list** is what `nt @"expr"`, `pegRules` and `pegGrammar` in
expression position use.  A reference carries a proof of where its rule sits
in the list, `There (There Here)`, and GHC's evidence for it grows with the
rule's depth and the size of the list, so the total grows faster than the
grammar.  An entry of that list is a rule's name and the type it returns:

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
Haskell, when the quasi-quoter runs, in time linear in the grammar.  It is
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

A PEG does not memoise, so `A B / A C` parses `A` twice when `B` fails.  The
quasi-quoters factor such alternatives into `A (B / C)` when they are
consecutive, which keeps a grammar whose precedence levels are written that
way linear in the input rather than exponential in its nesting.

So the checks divide like this:

| what | checked by | when |
|---|---|---|
| a reference names a rule that exists, at the right type | GHC, or the splice for `pegGrammar` | every compilation |
| a rule's `:: T` annotation matches what its body returns | GHC | every compilation |
| left recursion, nullable repetition, duplicate rule | `PEG.Analysis` | at the splice |

The second half of that table is the trade.  A `Rules` chain assembled by hand
from `RCons`, without a quasi-quoter, is checked for reference errors only: a
rule that begins with itself compiles and loops.  And `pegRules` analyses its
block open-world, since two blocks can be combined, so left recursion that
closes *across* two blocks is reported by neither it nor GHC.  Writing the
grammar as one `pegGrammar` closes both gaps — it is closed-world, so every
reference resolves and every cycle is visible — and it is also the fastest to
compile, because it declares a key type instead of a list.

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
myParser :: String -> Result String Exp
myParser = parse myGrammar
```

## License

BSD-3-Clause. See [LICENSE](LICENSE).
