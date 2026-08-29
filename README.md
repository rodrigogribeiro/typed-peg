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

## License

BSD-3-Clause. See [LICENSE](LICENSE).
