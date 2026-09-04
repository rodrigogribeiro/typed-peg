# Changelog

## 0.2.0.0 — 2026-09-04

This release is **not source-compatible with 0.1.0.0**: `PExp`, `Rules`,
`Grammar`, `Result` and `PState` all gain a leading stream type parameter, and
a rule whose result is a character-class repetition changes result type. See
*Changed* below for the migration.

### Added — parsing any stream, not just `String`

`PEG.Stream` introduces a `Stream` class, with instances for `String`, strict
and lazy `Data.Text.Text`, and strict and lazy `Data.ByteString.ByteString`.
A grammar written once runs over any of them.

The genericity reaches the *results*, not just the input: a character-class
repetition such as `cs:[a-zA-Z0-9_]+` now produces a **chunk of the input
stream** — a real `Text` slice — instead of unpacking into a `[Char]`.  Two new
`PExp` constructors, `Span` and `Span1`, carry this; the quasi-quoter emits
them for `[...]*`, `[...]+`, `'c'*`, `'c'+`, `.*` and `.+`.

`ByteString` is read as Latin-1, exactly as `Data.ByteString.Char8` does: fast,
correct for ASCII, and wrong for multi-byte UTF-8.  `PEG.Stream`'s Haddock
states this as a law rather than a footnote.

Only `unconsS` has no default, so a user instance is one method.  It returns an
unboxed sum rather than `Maybe (Char, s)` on purpose — behind a class
dictionary the boxed version would allocate a `Just` and a pair for every
character, losing the zero-allocation terminal path.

### Changed

- **Breaking.** `PExp`, `Rules` and `Grammar` take a leading stream parameter:
  `PExp s env ty a`, `Rules s env defs`, `Grammar s env ty a`.  `Result` and
  `PState` likewise: `Result s a`, `PState s`.
- **Breaking.** A rule whose result is a character-class repetition now has
  result type `s`, so its `Env` synonym takes a parameter.  Semantic actions
  that fed such a result to something expecting a `String` need
  `chunkToString`: `number <- ds:[0-9]+ { Lit (read (chunkToString ds)) }`.
- **Breaking.** The symbol variable in `PExp`'s `NT`, in `nt`, and in
  `Rules`'s `RCons` is now named `n`; `s` is the stream.  `nt @"name"` is
  unaffected — the name is deliberately still the first quantified variable.
- `PEG.Semantics.Simple`'s unrelated `Stream` class is renamed
  `SimpleStream`, to leave the name to `PEG.Stream`.
- `PState`'s input field is now strict.

A `Grammar` is monomorphic in its stream.  Reusing one across stream types
needs a `forall s. Stream s => Grammar s env ty a` signature, which turns the
value into a function of a dictionary and so stops the compiled parser being
shared between calls.  Give parsers a monomorphic top-level binding where that
matters; `PEG.Parse`'s Haddock spells this out.

### Performance

Measured on the benchmark suite, bytes allocated per input byte, against the
previous release of the evaluator:

| grammar | before (String) | String | Text | ByteString | megaparsec |
|---|---|---|---|---|---|
| arith  | 990 | 943 | 1127 |  969 | 1239 |
| csv    | 834 | 787 |  951 |  805 | 1035 |
| json   | 459 | 404 |  583 |  452 |  782 |
| nested | 265 | 312 |  481 |  336 | 1283 |
| quoted `(!'"' .)*` | 162 | 209 | 320 | 250 | 128 |

`ByteString` is the cheapest column on five of the seven grammars and beats
megaparsec on six.  `Text` costs more than `String` throughout — the same
result the earlier study found for megaparsec, and worth knowing before
reaching for it.

Two grammars regressed on `String` (`nested` +18%, the `(!'"' .)*` idiom
+29%).  Both are dominated by single-character steps rather than bulk scans,
where `unconsS` is one indirect call that the previous direct cons-cell match
did not need.  The five grammars that do any bulk scanning improved by 5-12%.

The `idents` and `quoted [^"]*` groups are not in the table because their
grammars changed: `ident` moved from `c:[a-zA-Z_] cs:[a-zA-Z0-9_]*` to
`&[a-zA-Z_] cs:[a-zA-Z0-9_]+` so that it returns a chunk rather than consing a
character onto one, and `Bench.Mega`'s `identP` moved to `takeWhile1P` to keep
the comparison like-for-like.  On the new grammars typed-peg allocates 100
B/byte over `String` and 84 over `ByteString`, against megaparsec's 179.

### Performance

The evaluator was rewritten twice: once around a compilation step, once around
an unboxed step result.  On the benchmark suite in `bench/` (see `cabal bench`),
measured against megaparsec 9.8 in the same run, typed-peg went from taking
2.1x-58x the time megaparsec takes to taking 0.95x-1.17x of it — and it now
allocates less than megaparsec on six of the seven grammars.  The one grammar
where it still loses is the `(!'"' .)*` idiom, which scans every character
twice by construction; written as `[^"]*` it costs 1.23x-1.35x.

- A compiled step returns an unboxed sum, `(# (# #) | (# a, PState #) #)`,
  rather than `Maybe (a, PState)`.  The two are isomorphic, but the unboxed
  sum travels in registers, so a step that succeeds no longer allocates a
  `Just` *and* a pair on top of the new state, and a step that fails
  allocates nothing at all.  This makes `Seq` and `Map` — the two
  constructors the quasi-quoter emits for every grammar item — completely
  allocation-free, and cuts total allocation by a further 9–53%.
- String literals match in a single loop that builds one `PState`, rather
  than one per character, whenever the grammar does not use layout.
- `PEG.Parse` now *compiles* a `Grammar` into a closure once, instead of
  walking the `PExp` GADT and the rule list on every step.  Resolving a
  non-terminal is now one indirect call rather than a linear scan of the rule
  environment.  `parseWith opts g` is written so that partially applying it
  yields the compiled parser; bind it to a name to reuse it.
- Character classes compile to a single `Sat` node holding a `PEG.CharSet`
  (a 256-bit bitmap), instead of expanding into a chain of ordered choices.
  Matching one character of `[a-zA-Z0-9_]` used to cost 63 parser steps.
- String literals compile to a single `Str` node instead of a chain of
  `Seq`/`Map`/`Term`.
- The parser no longer builds a `[(Char, Int)]` copy of the input; the column
  of the current character is carried in the state and updated incrementally.
- Terminals take a fast path that skips all interval arithmetic when the
  ambient column relation is total (`anyR`), which is the case for every
  grammar that does not use layout.  The new `rdTotal` field of `RelD` records
  this.
- `parse` returns the unconsumed suffix in `O(1)` instead of recomputing it
  with two `length` calls and a `drop`.
- `Star` no longer builds a chain of selector thunks.

### Added

- Negated character classes in the quasi-quoter: `[^"]` matches any character
  other than a quote.  Previously the only way to write this was
  `(!'"' .)`, which scans every character twice — once for the lookahead and
  once for the dot.  On the `quoted` benchmark the class form halves the
  allocation.
- `PEG.CharSet`: compact character sets, re-exported from `PEG`.
- `PEG.Syntax.Sat` / `PEG.Syntax.Str` constructors, and the `sat`,
  `charClass` and `notCharClass` smart constructors.
- `PEG.Parse.compileGrammar` and the `Step` and `Res` types, for callers that
  want the compiled parser directly.
- `PEG.Indent.rdTotal`.
- A criterion benchmark suite comparing typed-peg with megaparsec
  (`bench/`, run with `cabal bench`).
- `examples/Compat.hs`: a differential battery used to check that the
  optimisation work did not change any observable behaviour.

### Changed

- **Breaking.** `PState` now holds the remaining input as a `String` plus the
  current column and offset (`stInput`, `stCol`, `stOff`), rather than a
  precomputed `[(Char, Int)]`.  `PEG.Parse.Input`, `PEG.Parse.columns` and
  `PEG.Parse.eval` are gone; use `compileGrammar` instead of `eval`.
- **Breaking.** `RelD` has a new `rdTotal` field.
- **Breaking.** `PEG.Parse.Step` now returns the unboxed sum `Res a` instead
  of `Maybe (a, PState)`.  This only affects code that called
  `compileGrammar` directly; `parse` and `parseWith` are unchanged.
- **Breaking.** In a quasi-quoted grammar, a `^` immediately after `[` now
  negates the class instead of standing for itself; write `[\^]` for a class
  containing a caret.
- The `template-haskell` upper bound now admits the version shipped with
  GHC 9.10 (`< 2.24`).

## 0.1.0.0 — 2026-08-28

### Added

- Initial release.
- Type-safe PEG parser combinators with compile-time left-recursion detection
  via type families (`PEG.Grammar`).
- FIRST-set and nullability information tracked at the type level (`PEG.Type`,
  `PEG.TyLevel`).
- Indentation-sensitive parsing primitives (`PEG.Indent`).
- Quasi-quoter `pegRules` for writing grammars in a concrete DSL (`PEG.QQ`).
- Simple semantics interpreter (`PEG.Semantics.Simple`).
