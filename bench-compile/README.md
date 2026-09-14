# What a grammar costs GHC

A grammar in this library is checked by the type checker, so its size is paid
in compile time — once per compilation of every module that mentions it.  This
directory measures that, so that changes to the type-level machinery can be
argued from numbers rather than from reading the type families.

```
./bench-compile/run.sh                 # the default modes, N = 16 32 48 64
./bench-compile/run.sh minipython 0    # the MiniPython grammar
./bench-compile/run.sh dense 16 32     # one mode, chosen sizes
./bench-compile/run.sh wild 16 64      # the environment left to inference
```

`Gen.hs` writes the module, `run.sh` times `ghc -fno-code` on it and reports
GHC's peak heap as the RTS measures it.  The grammar
is the same shape in every mode: `N` rules, rule `i` referring to rules `i+1`
and `i+2`, so there are `2N` non-terminal occurrences and an environment of
`N` entries.  It is the shape of a precedence ladder, which is what used to
make FIRST sets grow — `FIRST(r_i)` was every rule after `i` — and so the
worst case for the machinery this directory was written to measure.

## The modes

| mode | what it holds fixed | what it changes |
|---|---|---|
| `dense` | environment written out, references through `nt` | rule `i` begins with a non-terminal — the shape whose FIRST sets used to be every rule after `i` |
| `sparse` | same rules, same `2N` occurrences | every rule starts with a terminal, so nothing can be at the head of anything |
| `witness` | the `dense` grammar | every reference uses `ntw` and a generated `Member` proof instead of `nt` |
| `witness-sparse` | the `sparse` grammar | ditto |
| `qq-grammar` | the `dense` grammar | written with `pegGrammar` in declaration position: a key type is declared and every reference is a constructor |
| `qq-grammar-sparse` | the `sparse` grammar | ditto |
| `qq-grammar-expr` | the `dense` grammar | `pegGrammar` in expression position: the environment is a list, inferred, and every reference carries its proof |
| `minipython` | — | `examples/MiniPython.hs`, a real grammar of 27 rules; `N` is ignored |
| `wild` | the `dense` grammar | the environment is left to GHC as a wildcard |
| `lookup-class` | `N` entries, `2N` references, no library | references resolve through `Lookup` and the `KnownMember` instance chain, as `nt` does |
| `lookup-witness-eq` | ditto | the witness is supplied, but the `Lookup` equality that says which rule it is for is kept |
| `lookup-witness` | ditto | the witness is supplied and no equality is demanded |
| `lookup-nameenv` | `lookup-witness-eq` | the family that reports a failed lookup takes the environment, as the library's does |
| `lookup-big` | `lookup-witness-eq` | every entry carries an `N`-symbol list, so the environment is `O(N^2)` nodes |
| `lookup-big-nameenv` | both of the above at once | — |
| `lookup-key` | `N` rules, `2N` references, no library | references are constructors of a key type, as `pegGrammar` now generates |

`dense` against `witness` measures, end to end, what replacing the
`KnownMember` search with a generated proof is worth.  `dense` against
`sparse` used to measure what the FIRST sets inside the environment cost; the
environment no longer has any, so the two now differ only by an extra terminal
per alternative, and their being equal is the result.  `lookup-big` is the
reason it matters, and the constraint on anything added to an entry in future.

## Baseline

GHC 9.10.3, `-fno-code -freduction-depth=0`, heap capped at 8 GB.  About
0.15 s of each figure is GHC's own start-up, which matters for the `lookup-*`
rows.

Run-to-run variation on this machine reaches 25%, so the tables below are one
sweep each and every ratio is taken from within its own table.

## What an entry used to carry, and what it cost

Entries of the environment used to hold each rule's nullability and FIRST set,
so that an `Acyclic` constraint could reject left recursion.  These are the
numbers that removed them.

**The two levers, and that they compose.**  Before the change:

| N | `dense` | `witness` | `witness-sparse` | `qq-grammar` | `qq-grammar-sparse` |
|---|---|---|---|---|---|
| 16 | 0.48 s | 0.32 s | 0.25 s | 0.45 s | 0.43 s |
| 32 | 1.38 s | 0.74 s | 0.44 s | 1.07 s | 0.61 s |
| 48 | 4.86 s | 2.21 s | 0.73 s | 2.66 s | 0.94 s |
| 64 | 15.15 s | 6.11 s | 1.23 s | 7.23 s | 1.61 s |

Emptying the FIRST sets was worth **5.0x** on top of the witness and **4.5x**
on top of `pegGrammar` — as much as it had been worth against `dense` before
the witness lever was taken, so the two were independent.  More to the point,
doubling `N` from 32 to 64 cost `witness` 8.3x and `witness-sparse` 2.8x: the
sets were not a constant factor on the curve, they were the reason it was a
cubic.

**And none of it was the arithmetic.**  `witness-literal-ty` — a mode that no
longer exists, since there is no index left to splice — kept the large
environment and the lookup but handed GHC each body's index as a literal, so
`SeqTy`, `ChoiceTy`, `Union` and `NTGo` were never reduced:

| N | `witness` | `witness-literal-ty` | `witness-sparse` |
|---|---|---|---|
| 16 | 0.27 s | 0.26 s | 0.26 s |
| 32 | 0.65 s | 0.72 s | 0.44 s |
| 48 | 2.00 s | 2.19 s | 0.75 s |
| 64 | 5.83 s | 6.18 s | 1.31 s |

Not reducing the FIRST-set arithmetic at all was worth *nothing* — a shade
slower, in fact.  So the 4.4x between `witness` and `witness-sparse` was not
the cost of *computing* the sets.  It was the cost of an environment whose
entries *carried* them, `O(N^2)` type nodes, being named by each of the `2N`
reference constraints solved against it.

**The micro-benchmark, with nothing else in the picture.**  Its entries are
given an `N`-symbol list that no family ever reads, present only to make the
environment quadratic:

| N | `lookup-witness-eq` | `lookup-nameenv` | `lookup-big` | `lookup-big-nameenv` |
|---|---|---|---|---|
| 32 | 0.19 s | 0.20 s | 0.87 s | 1.12 s |
| 64 | 0.77 s | 0.87 s | 11.80 s | 13.26 s |
| 96 | 1.85 s | 2.37 s | heap overflow | heap overflow |

**Entry size was the whole cost, and not a factor but an exponent.**  A
payload nothing reads took `N = 64` from 0.77 s to 11.80 s — **15x** — and at
`N = 96` exhausted 8 GB where the small entries take 1.85 s.  Resolving
`Lookup n env ~ 'EnvEntry ...` costs what the entry is worth in type nodes,
once per occurrence, whether or not anything looks inside it.

**Naming the environment in the error family was not the problem.**
`lookup-nameenv` gives `Found` the environment argument that the library's
`Lookup` passes it, so that a failed lookup can list the names that are
defined.  It costs 5% on small entries and 12% on large ones, so the good
error message stays.

## Where it landed

An entry is now a rule's name and its result type.  Same machine, same sweep:

| N | `dense` | `sparse` | `witness` | `witness-sparse` | `qq-grammar` | `qq-grammar-sparse` |
|---|---|---|---|---|---|---|
| 16 | 0.37 s | 0.37 s | 0.23 s | 0.23 s | 0.40 s | 0.39 s |
| 32 | 0.60 s | 0.67 s | 0.30 s | 0.31 s | 0.51 s | 0.52 s |
| 48 | 1.14 s | 1.15 s | 0.54 s | 0.54 s | 0.76 s | 0.76 s |
| 64 | 1.99 s | 2.07 s | 0.89 s | 0.94 s | 1.19 s | 1.19 s |

At `N = 64`, against the table above: `dense` **7.6x**, `witness` **6.9x**,
`qq-grammar` **6.1x**.

`dense` and `sparse` now agree, and so do `witness` and `witness-sparse`, and
`qq-grammar` and `qq-grammar-sparse`.  That is the check that the cost is
actually gone rather than moved: the grammar shape that used to be 4.9x worse
than the other is no longer distinguishable from it.

**The curve changed, not just the constant.**  32 to 64 costs `dense` 3.3x
where it used to cost about 8x, so what was cubic in the number of rules is
now closer to quadratic, and grammars the old machinery could not finish are
ordinary:

| N | `dense` | `witness` | `qq-grammar` |
|---|---|---|---|
| 96 | 6.97 s | 2.36 s | 2.45 s |
| 128 | 15.24 s | 5.32 s | 5.28 s |

A 128-rule grammar through `pegGrammar` now costs what a 64-rule grammar used
to cost written the fastest way available, and less than half what one cost
written the ordinary way.

**Inference is no longer out of the question.**  `wild` leaves the environment
to GHC.  It used to be unusable — the entries it inferred were unreduced
type-family applications over FIRST sets, and at `N = 16` it was still
climbing past 24 GB of heap when it was stopped.  There are no type families
left for it to leave unreduced:

| N | 16 | 32 | 64 |
|---|---|---|---|
| `wild` | 0.39 s | 0.65 s | 2.25 s |

That is `dense` to within noise, which means a hand-written rule set no longer
has to write its environment down at all.

**What is left is the search.**  `dense` resolves each reference through the
`KnownMember` instance chain and `qq-grammar` is handed the proof; at
`N = 128` that is 15.24 s against 5.28 s.  The environment search is now the
dominant cost of a large grammar, and `pegGrammar` is how to avoid it.

For comparison, `PEG.Analysis` computes nullability and the FIRST sets for the
64-rule grammar in 6 ms, 40 ms at `N = 128` and 286 ms at `N = 256`.

## Keeping the generator honest

`Gen.hs` used to compute the FIRST sets that the type families would compute
and write them into the module, so that a passing sweep was also a check on
the generator: get a set wrong and GHC rejects the module.  An environment no
longer states them, so that check is gone with them, and what a passing sweep
now confirms is only that the generated grammar type-checks — which is still
enough to catch a mode that has stopped generating what its row in the table
claims.

## Keys instead of a list

What the section above left — "the search" — turned out not to be the search.
Handing GHC the proof instead of having it search is a constant factor, and
the proof still has to be checked: a reference carries `There (There ...
Here)`, and GHC's evidence for it grows with the rule's depth and with what
is left of the list.  Summed over `2N` references, that grew much faster than
the grammar, and memory was what gave out first.

The lookup micro-benchmark, same session, with peak heap:

| N | `lookup-witness-eq` | `lookup-witness` | `lookup-key` |
|---|---|---|---|
| 128 | 5.75 s, 3 125 MiB | 3.16 s, 1 643 MiB | 0.12 s, 24 MiB |
| 256 | exhausts 8 GB | exhausts 8 GB | 0.14 s, 28 MiB |
| 512 | exhausts 8 GB | exhausts 8 GB | 0.21 s, 49 MiB |
| 1024 | — | — | 0.39 s, 73 MiB |

**Dropping the `Lookup` equality was worth 2x and did not change the curve.**
`lookup-witness` has no type family at all, and still does not fit in 8 GB at
`N = 256`.  A key type — one constructor per rule, `K_r1 :: GKey Int` — is a
reference whose type does not mention the rest of the grammar, and it is flat.

So `pegGrammar` now declares one.  Through the library:

| N | `qq-grammar` before | `qq-grammar-expr` | `qq-grammar` | `qq-grammar-sparse` |
|---|---|---|---|---|
| 64   | 1.16 s,   385 MiB | 1.10 s,   375 MiB | 0.44 s,  49 MiB | 0.48 s,  48 MiB |
| 96   | —                 | 2.35 s,   744 MiB | — | — |
| 128  | 5.70 s, 2 180 MiB | 5.74 s, 2 298 MiB | 0.50 s,  51 MiB | 0.53 s,  51 MiB |
| 256  | exhausts 8 GB     | —                 | 0.57 s,  80 MiB | 0.70 s,  85 MiB |
| 512  | —                 | —                 | 0.70 s,  98 MiB | 0.89 s, 119 MiB |
| 1024 | —                 | —                 | 1.17 s, 159 MiB | 1.18 s, 201 MiB |

"Before" is the same mode on the previous commit.  `qq-grammar-expr` is the
list the expression form still builds, and it is the "before" curve, as it
should be.  For scale, `dense` (a hand-written list searched by `KnownMember`)
is 7.29 s and 2 416 MiB at `N = 96` and 15.6 s and 5 108 MiB at `N = 128`;
`witness` 2.65 s / 1 179 MiB and 5.84 s / 2 819 MiB.

`minipython` went from 0.47 s and 111 MiB to 0.45 s and 57 MiB.  The 25-rule
grammar was never where the list hurt; it was measured to check that the keys
cost a small grammar nothing.

**The last superlinear cost was the analysis.**  With keys alone, `qq-grammar`
was 5.2 s and 921 MiB at `N = 512` and 58 s and 5.8 GB at `N = 1024`, while
`qq-grammar-sparse` was flat — and the two grammars differ only in their FIRST
sets.  `PEG.Analysis` computed them for every splice, by iterating over whole
sets: on its own, outside GHC, 3.9 s at 512 rules and 48.8 s at 1024.  The
diagnostics need only nullability and the graph of direct head references, so
that is what it now computes, and the FIRST sets are built only when the
environment is inspected (26 ms at 256 rules, 0.5 s at 1024, when they are).
That is the difference between the two `qq-grammar` columns above at 512 and
1024, and `qq-grammar` and `qq-grammar-sparse` agree again.

**A pitfall, measured.**  `compileGrammar` first took `Tabulate nt` as a
constraint of the function that compiles a keyed grammar.  GHC specialises on
dictionaries it knows, and the key type is still a variable there, so the
`SPECIALIZE` pragmas for `String`, `Text` and `ByteString` never reached it:
MiniPython parsed 37% slower, allocating 48% more per character, than the same
grammar over a list — every `Stream` method a dictionary call.  `tabulate` is
now passed as an argument, and the two allocate the same to the byte.
