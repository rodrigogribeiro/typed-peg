# Benchmark results

Raw data behind the performance claims in `README.md` and `CHANGELOG.md`.
Regenerate with `cabal bench` (timings) and
`cabal bench --benchmark-options=--alloc` (allocation).

## Allocation — deterministic, reproduces exactly

| file | evaluator |
|---|---|
| `alloc-baseline.txt`   | 0.1.0.0, tree-walking |
| `alloc-v1-compiled.txt`| grammar compiled once, `CharSet` bitmaps |
| `alloc-v2-unboxed.txt` | unboxed step result |
| `alloc-v3-stream.txt`  | generic over `PEG.Stream` |

## Timings — noisy, only within-run ratios are meaningful

| file | notes |
|---|---|
| `baseline.csv`, `optimized.csv`, `v1-compiled.csv`, `v2-unboxed.csv` | unpinned |
| `pinned-v1-compiled.csv`, `pinned-v2-unboxed.csv` | `taskset -c 3`, quiet machine |
| `pinned-v3-stream.csv` | `taskset -c 3`, machine at load ~4.5 |

Absolute times are **not** comparable between the pinned files: the v3 run was
taken on a loaded machine and every column, megaparsec's included, is roughly
2.5x slower than in the v2 run.  The typed-peg / megaparsec ratio *within* one
run is the figure to read.

## Differential battery

`compat-old.txt` / `compat-new.txt` / `compat-new2.txt` are captures of
`examples/Compat.hs`, compared byte-for-byte across evaluator versions.  From
v3 the battery also runs over `Text` and `ByteString` and asserts all three
agree.

## Caveats that apply to every number here

- Both libraries are built at `-O1` (cabal's default); only the benchmark
  modules use `-O2`.  Symmetric, but not what a user building with `-O2` sees.
- megaparsec is measured over `String` and `Text` only: its
  `Token ByteString` is `Word8`, so the same grammars do not typecheck over
  `ByteString`.
- The `idents` and `quoted-*` grammars changed in v3 (see
  `alloc-v3-stream.txt`), so those rows are not comparable with earlier files.
