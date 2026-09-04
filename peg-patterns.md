# PEG patterns for typed-peg

A companion to Jamie Willis and Nicolas Wu, *Design Patterns for Parser
Combinators (Functional Pearl)*, Haskell 2021
([10.1145/3471874.3472984](https://doi.org/10.1145/3471874.3472984)).

That paper collects eleven patterns for writing parsers with a backtracking
combinator library of the `parsec` family. Most of them transfer to typed-peg,
but three things change the picture:

- **Ordered choice is committed.** Once an alternative succeeds, a PEG never
  reconsiders it. There is no `try`, because there is nothing to undo — but the
  order in which you write alternatives becomes part of the specification.
- **Left recursion is a type error**, not a discipline to remember. The
  `Acyclic` constraint is checked when you construct a `Grammar`.
- **The grammar's shape is written down in a type.** The `Env` records every
  rule's nullability, FIRST set and result type. Several of the paper's
  patterns become things the compiler enforces rather than things you adopt.

Every code fragment below is compiled: it lives in
[`examples/Patterns.hs`](examples/Patterns.hs) and runs as part of
`cabal test`.

## The patterns at a glance

| Willis & Wu | In typed-peg |
|---|---|
| 1a Homogeneous Chains | [§1.2](#12-chains-fold-a-starred-tail) — write the fold out; no `chainl1` |
| 1b Heterogeneous Chains | [§1.3](#13-one-rule-per-precedence-level) — one rule per level, types declared in the `Env` |
| 1c Precedence Tables | [§1.4](#14-precedence-tables-absent-but-not-impossible) — absent; what it would take |
| 2a Whitespace Combinators | [§2.1](#21-consume-trailing-whitespace-only) — `lexeme` / `fully`, same discipline |
| 2bi Tokenizing Combinators | [§2.2](#22-tokens) — same |
| 2bii Keyword Combinators | [§2.3](#23-keywords-are-negative-lookahead) — **simpler**: `!` instead of `try` |
| 2c Overloaded Strings | [§2.4](#24-the-quasi-quoter-is-the-facade) — subsumed by the quasi-quoter |
| 3a Lifted Constructors | [§3.1](#31-lifted-constructors) — same |
| 3b Deferred Constructors | [§3.2](#32-deferred-constructors-and-the-position-gap) — **partly**; no source positions |
| 4a Verified Errors | [§4](#4-errors-the-shape-without-the-message) — shape only; no messages |
| 4b Preventative Errors | [§4](#4-errors-the-shape-without-the-message) — shape only; no messages |

Sections [§5](#5-patterns-that-are-specific-to-pegs) and
[§6](#6-what-typed-peg-cannot-do-yet) add patterns the paper has no reason to
cover, and summarise the gaps.

---

## 1. Expressions

### 1.1 Left recursion is a type error

The paper opens by writing the textbook grammar directly:

```haskell
expr = Add <$> expr <*> (char '+' *> term) <|> ... <|> term
```

and observing that it loops. Section 2 is then about the rewrite that fixes it.

In typed-peg you cannot write it in the first place. Each rule's type carries
its FIRST set, and `Grammar` demands `Acyclic env`:

```
expr <- e:expr '+' t:term { Add e t }
```

```
Left-recursive non-terminal: "expr"
Its head set already contains itself: ["expr", "term"]
Violates the acyclicity condition i `notElem` Gamma(i).F.
```

reported at the `Grammar` constructor, before anything runs.

**Pattern.** Do not treat left-recursion removal as a step you perform. Write
the grammar; if it compiles, no rule can loop on its own head. The rewrite
below is then the *only* shape available, which is why it is worth having a
name for.

### 1.2 Chains: fold a starred tail

*(Willis & Wu, Pattern 1a: Homogeneous Chains.)*

Their advice is to reach for `chainl1`/`chainr1` rather than hand-rolling
associativity. typed-peg has no chain combinator, so the pattern is the shape
you write instead: **an operand, then a starred tail of (operator, operand)
pairs, folded in the semantic action.**

```
expr <- t:term  ts:(o:[+-] u:term)*  { chainl t ts }
```

Left association comes from `foldl`, right association from `foldr`. Keep the
fold itself in Haskell, out of the grammar:

```haskell
chainl :: Expr -> [(Char, Expr)] -> Expr
chainl = foldl step
  where
    step l ('+', r) = Add l r
    step l ('-', r) = Sub l r
    step l ('*', r) = Mul l r
    step l ('/', r) = Div l r
    step _ (c  , _) = error ("chainl: unexpected operator " ++ show c)
```

The `error` case is the price of a homogeneous chain: the operator is a `Char`,
so nothing stops a mismatched table. The paper makes exactly this observation,
and its answer is the next pattern.

### 1.3 One rule per precedence level

*(Willis & Wu, Pattern 1b: Heterogeneous Chains.)*

Their fix is to give each precedence level its own AST layer so the types rule
out a mismatched chain. In typed-peg the level structure is *already* forced on
you — a PEG expresses precedence by descent — and the `Env` makes you declare
what each level produces:

```haskell
type CalcEnv s =
  '[ '("expr" , 'EnvEntry ('MkTy 'False '["term", "unary", "atom"]) Expr)
   , '("term" , 'EnvEntry ('MkTy 'False '["unary", "atom"])         Expr)
   , '("unary", 'EnvEntry ('MkTy 'False '["atom"])                  Expr)
   , '("atom" , 'EnvEntry ('MkTy 'False '[])                        Expr)
   ]
```

```
expr  <- t:term  ts:(o:[+-] u:term)*  { chainl t ts }
term  <- f:unary fs:(o:[*/] g:unary)* { chainl f fs }
unary <- '-' e:unary                  { Neg e }
       / a:atom
atom  <- '(' e:expr ')'
       / ds:[0-9]+                    { mkNum ds }
       / &[a-zA-Z_] cs:[a-zA-Z0-9_]+  { mkVar cs }
```

**Pattern.** Give each level a distinct result type in the `Env` when you want
the paper's type safety. Above, every level produces `Expr`, which is the
homogeneous choice; changing `term` to produce a `Term` and `expr` an `Expr`
makes a misplaced operator a type error, exactly as in the paper — at the cost
of an AST with one constructor per layer.

Note the FIRST set columns. They are not decoration: `'["term", "unary",
"atom"]` says that entering `expr` can immediately enter any of those, and it
is what the acyclicity check consumes. Getting them wrong is a compile error,
so they double as a checked comment.

### 1.4 Precedence tables: absent, but not impossible

*(Willis & Wu, Pattern 1c: Precedence Tables.)*

Their `precedence` combinator folds a table of levels into the ladder:

```haskell
expr = precedence $
  sops InfixL [Add <$ char '+', Sub <$ char '-'] +<
  sops InfixL [Mul <$ char '*']                  +<
  sops Prefix [Neg <$ string "negate"]           +<
  Atom atom
```

**typed-peg does not provide this**, and adding it is more than a convenience
wrapper — but less than impossible, so it is worth being precise about what it
would take.

`Prec` in the paper is already a type-indexed structure: each `Op a b`
connects a layer producing `a` to one producing `b`, which is what makes
adding or removing a level a type error. A typed-peg version would have to
carry the `Ty` index as well, since every `PExp` is indexed by its nullability
and FIRST set:

```haskell
data Prec s env ty a where ...      -- sketch, not implemented
```

The good news is that the `Ty` arithmetic is tractable. Precedence layers are
anonymous `PExp` values rather than named non-terminals, and FIRST sets track
only non-terminal names — so every layer built from operators and a starred
tail has an empty FIRST set, and its nullability follows from `SeqTy`. What is
needed is a GADT whose indices compose the way `SeqTy` and `ChoiceTy` do, plus
`infixl1`/`infixr1`/`prefix`/`postfix` at the `PExp` level.

Until then, write the levels out as in §1.3. For four or five levels that is
barely longer than the table, and it keeps each level visible in the `Env`.

---

## 2. Lexing

### 2.1 Consume trailing whitespace only

*(Willis & Wu, Pattern 2a: Whitespace Combinators.)*

Their rule, which transfers unchanged: **every lexeme consumes the whitespace
*after* it, never before; one `fully` at the top consumes leading whitespace
and demands end of input.** Consuming leading whitespace inside a lexeme breaks
position reporting and makes it ambiguous who is responsible for a given space.

```haskell
ws :: PExp s env ('MkTy 'True '[]) s
ws = spanOf (fromRanges [(' ', ' '), ('\t', '\t'), ('\r', '\r'), ('\n', '\n')])

lexeme :: PExp s env ty a -> PExp s env (SeqTy ty ('MkTy 'True '[])) a
lexeme p = (\x _ -> x) <$>. p <*>. ws

eof :: PExp s env ('MkTy 'True '[]) ()
eof = Not AnyChar

fully :: PExp s env ty a
      -> PExp s env (SeqTy ('MkTy 'True '[])
                           (SeqTy ty ('MkTy 'True '[]))) a
fully p = (\_ x _ -> x) <$>. ws <*>. p <*>. eof
```

```
"12"     => OK "12"
"  12  " => OK "12"
"12 x"   => Fail
""       => Fail
```

Two typed-peg specifics. `ws` is a character class, so it compiles to a single
`Span` node and returns a chunk of the input — over `Text` that is a slice, and
when the item is unlabelled in a quasi-quoted rule the chunk is discarded
anyway. And `eof` is `Not AnyChar`, written `!.` in the quasi-quoter: a PEG
gets end-of-input from negative lookahead rather than from a primitive.

**`fully` matters more in a PEG than in `parsec`.** A PEG parser is happy to
succeed on a prefix:

```
"a:=1;" => OK [Asgn "a" (Num 1)] rest=";"
```

Nothing is wrong here — the grammar matched what it could. If you want the
whole input consumed you must say so, and `fully` is where you say it.

### 2.2 Tokens

*(Willis & Wu, Pattern 2bi: Tokenizing Combinators.)*

Same pattern: annotate terminals with `lexeme`, not the composite rules. Their
`token = lexeme . try` loses its `try` here, since ordered choice needs no
backtracking marker.

In a quasi-quoted grammar the usual spelling is a `ws` rule invoked after each
terminal, as `examples/Layout.hs` and the JSON benchmark do:

```
pair <- k:strlit ws ':' ws v:value  { (k, v) }
```

**Keep the `ws` calls at terminal boundaries and nowhere else.** A `ws` in the
middle of a composite rule is the same mistake as leading whitespace in a
lexeme: it makes two rules disagree about who owns the space between them.

### 2.3 Keywords are negative lookahead

*(Willis & Wu, Pattern 2bii: Keyword Combinators.)*

This is the pattern a PEG expresses best. The problem is that `string "negate"`
happily matches the prefix of `negatex`. Their answer is a `keyword` combinator
that checks no identifier character follows — which in `parsec` needs `try` to
undo the partial match.

In a PEG it is just `!`:

```haskell
keyword :: String -> PExp s env ('MkTy 'False '[]) ()
keyword k = (\_ _ -> ()) <$>. stringNE k <*>. Not (sat identCont)
```

or, in the quasi-quoter, `"negate" ![a-zA-Z0-9_]`.

```
"negate"   keyword => OK ()          | bare => OK ()
"negatex"  keyword => Fail           | bare => OK () rest="x"
"negate2"  keyword => Fail           | bare => OK () rest="2"
"negate x" keyword => OK () rest=" x"| bare => OK () rest=" x"
```

The `bare` column is the bug the pattern prevents: without the lookahead,
`negatex` parses as the keyword `negate` followed by the variable `x`.

**The same shape covers every longest-match ambiguity**, not only keywords:
`'<' !'='` is "less-than, but not the start of `<=`". See §5.1 for the
alternative spelling.

### 2.4 The quasi-quoter is the facade

*(Willis & Wu, Pattern 2c: Overloaded Strings.)*

Their goal is to write `"if" *> expr` and have the string literal quietly
become a tokenizing parser, via `IsString`. The quasi-quoter already provides
this, and more directly: inside `[pegRules| ... |]`, `"do"` *is* a string
literal in grammar syntax, `[a-z]` is a character class, and `/` is ordered
choice. There is no Haskell-level plumbing to hide.

The residue of the pattern still applies: **keep token definitions in one
place.** A rule named `ident` or `number` used everywhere beats the same
character class copy-pasted into five rules — not for concision, but because
the `Env` then names it, and a change happens once.

---

## 3. Building the AST

### 3.1 Lifted constructors

*(Willis & Wu, Pattern 3a: Lifted Constructors.)*

Their advice — put bookkeeping in a smart constructor so the parser reads like
the grammar — transfers unchanged, and typed-peg gives it an extra job. Because
a character class produces a chunk of the stream rather than a `String`, the
conversion belongs in the smart constructor rather than smeared through the
actions:

```haskell
mkNum :: Stream s => s -> Expr
mkNum = Num . read . chunkToString

mkVar :: Stream s => s -> Expr
mkVar = Var . chunkToString
```

```
atom <- '(' e:expr ')'
      / ds:[0-9]+                    { mkNum ds }
      / &[a-zA-Z_] cs:[a-zA-Z0-9_]+  { mkVar cs }
```

**Keep semantic actions one application wide.** An action is Haskell spliced
unhygienically into the generated code; a long one is hard to read in grammar
syntax and hard to debug when it fails to typecheck, because the error points
at the quasi-quote.

### 3.2 Deferred constructors, and the position gap

*(Willis & Wu, Pattern 3b: Deferred Constructors.)*

Their motivating example is source positions: a node needs the position from
*before* its first token, so the constructor is returned by a parser and
applied later.

**typed-peg cannot do this**, because no combinator exposes the current
position to a semantic action. `PState` tracks `stCol` and `stOff`, and
`PEG.Indent` uses columns for layout, but neither is reachable from `{ ... }`.
A grammar cannot annotate its AST with source locations.

What does transfer is the general form — returning a function to be applied
later, so that bookkeeping is decoupled from the parser. In typed-peg this is
just a rule whose result type is a function:

```haskell
type OpEnv = '[ '("op", 'EnvEntry ('MkTy 'False '[]) (Expr -> Expr -> Expr)) ]

addOp :: Stream s => Grammar s OpEnv _ (Expr -> Expr -> Expr)
addOp = Grammar [pegRules| op <- '+' { Add } / '-' { Sub } |] (nt @"op")
```

```
"+" => Add (Num 1) (Num 2)
"-" => Sub (Num 1) (Num 2)
"*" => Fail
```

The rule's result type is a function, and the chain rule applies it. This is the same defunctionalisation the paper describes, and it
removes the partial `error` case from §1.2's `chainl`.

See §6: exposing position is the single change that would unlock the most of
this paper.

---

## 4. Errors: the shape without the message

*(Willis & Wu, Patterns 4a Verified Errors and 4b Preventative Errors.)*

Their patterns are about *messages*: use `lookAhead` to check that an error is
warranted before raising it, and `notFollowedBy` to rule out input that would
otherwise produce a confusing failure further along.

**typed-peg has no error messages at all.** `Result` is

```haskell
data Result s a = OK a s s | Fail
```

There is no position, no expected set, no label. Both patterns are therefore
unavailable in their stated form.

The *rejection* half still works, and is worth using. Preventative errors
become preventative failures:

```
asgn <- &[a-zA-Z_] v:[a-zA-Z0-9_]+ ":=" e:expr !'<'  { mkAsgn v e }
```

— an assignment whose right-hand side is followed by `<` is rejected here
rather than half-consumed and rejected somewhere less obvious. You lose the
message; you keep the locality.

Positive lookahead `&e` is `Not (Not e)`, so the verification half of Pattern
4a is expressible as a guard even though nothing can be reported.

---

## 5. Patterns that are specific to PEGs

### 5.1 In an ordered choice, the longest alternative goes first

Nothing in the paper needs this, because `<|>` with `try` reconsiders. A PEG
commits to the first success:

```
op <- '<'  / '<='      -- WRONG: '<=' is never reached
op <- '<=' / '<'       -- right
```

The first line silently parses `a <= b` as `a < (= b)` and then fails
somewhere else entirely. There is no warning: both grammars typecheck, and both
have the same FIRST set.

**Pattern.** When two alternatives share a prefix, order them longest-first.
When that is awkward — because the alternatives are non-terminals whose lengths
are not obvious — use the §2.3 lookahead spelling instead, which states the
constraint locally rather than relying on the order of a list.

This is the one place where typed-peg's type-level machinery does *not* help,
and it is worth knowing that the acyclicity check is not a substitute for
thinking about the order.

### 5.2 Prefer a negated class to the `!c .` idiom

The traditional PEG spelling of "any character except a quote" is
`(!'"' .)*` — a negative lookahead followed by a wildcard, which inspects
every character twice. typed-peg's quasi-quoter accepts a negated class:

```
q <- '"' cs:[^"]* '"'        -- one bit test per character
q <- '"' cs:(!'"' c:.)* '"'  -- two passes per character, and a cons list
```

The two describe the same language. On the benchmark suite the class form
allocates **90 bytes per input byte against 209**, and runs about **1.5×
faster**. It also returns a chunk of the stream rather than a `[Char]`.

**Pattern.** Reach for `[^...]` whenever the lookahead is a single character.
Keep `!e` for the cases a class cannot express — a keyword boundary, a
multi-character sentinel, a non-terminal.

### 5.3 A starred character class returns a chunk

`[a-z]*` and `[a-z]+` compile to `Span`/`Span1` and produce a slice of the
input stream, not a `[Char]`. That has a consequence for a very common idiom:

```
ident <- c:[a-zA-Z_] cs:[a-zA-Z0-9_]*  { c : cs }
```

`c` is a `Char` and `cs` is a chunk. This still compiles if the grammar is
fixed to `String` — where a chunk *is* a `[Char]` — but a stream-polymorphic
grammar is rejected:

```
Couldn't match expected type 's' with actual type '[Char]'
  's' is a rigid type variable bound by the inferred type of
    identG :: Stream s => Grammar s (IdEnv s) (MkTy False '["ident"]) s
```

So the idiom quietly ties a grammar to one stream. The fix is also faster,
because it scans once instead of twice and copies nothing:

```
ident <- &[a-zA-Z_] cs:[a-zA-Z0-9_]+   { cs }
```

The positive lookahead pins the first character to the narrower class without
consuming it, then one span takes the whole identifier.

**Pattern.** When a token is "one character from class A, then characters from
class B" and A is a subset of B, write it as `&A B+`.

### 5.4 The `Env` is a specification, so write it first

The environment is not boilerplate to be derived from the rules — it is the
grammar's interface, and it is checked:

```haskell
type CalcEnv s =
  '[ '("expr" , 'EnvEntry ('MkTy 'False '["term", "unary", "atom"]) Expr)
   , ...
   ]
```

Each entry states three things: whether the rule can match the empty string,
which non-terminals it can enter first, and what it produces. All three are
verified against the rule bodies.

**Pattern.** Write the `Env` before the rules, as you would write a signature
before a function. When a rule's FIRST set surprises you, that is usually the
grammar telling you something — a rule that is unexpectedly nullable is often a
`*` that should have been a `+`.

Two practical notes. A rule whose result is a character-class repetition has
result type `s`, so its `Env` synonym takes the stream as a parameter
(`CalcEnv s`). And GHC's error when an entry is wrong points at the whole
quasi-quote, not at the offending rule — so add rules a few at a time.

### 5.5 Layout is a grammar concern, not a lexer concern

`PEG.Indent` gives rules a column relation, so indentation-sensitive syntax
stays in the grammar instead of being pushed into a layout-inserting lexer:

```
istmts <- ss:(ws st:|s:stmt|)+^>          -- each statement strictly indented
stmts  <- r:(ws '{' ... ws '}')^~         -- braces: any column
```

`^>`, `^~`, `^=` and `_~` attach a relation to a sub-expression. This has no
counterpart in the paper, whose language is layout-insensitive.

**Pattern.** Give the brace form and the layout form as two alternatives of one
rule, with the relation attached to each, rather than deciding between them
before parsing.

---

## 6. What typed-peg cannot do yet

Collected from above, in the order that would most help a user of this library:

1. **Source positions in semantic actions.** Blocks Pattern 3b's motivating
   use and any AST that records where its nodes came from. `PState` already
   carries `stOff` and `stCol`; what is missing is a `PExp` constructor that
   hands them to an action.
2. **Error messages.** `Result` is `OK` or `Fail`. Patterns 4a and 4b are
   about phrasing good errors, and neither can be expressed. This is the
   largest single gap between typed-peg and the paper.
3. **A `precedence` combinator.** Needs a `Ty`-indexed `Prec` GADT and
   `infixl1`/`infixr1`/`prefix`/`postfix` at the `PExp` level (§1.4). Real
   work, but the index arithmetic is tractable.
4. **Chain combinators.** `chainl1`/`chainr1` are a small, unblocked
   convenience: they would remove the hand-written `foldl` from every
   expression grammar.
5. **A token/lexeme vocabulary in the quasi-quoter.** `lexeme`, `keyword` and
   `fully` are ten lines each (§2.1, §2.3) but every user writes them again.

None of 1, 2, 4 or 5 is blocked by the type-level design; they are absent
rather than impossible.

---

## Reading the examples

```bash
cabal test typed-peg-examples
```

runs `examples/Patterns.hs` along with the rest, printing the output quoted
throughout this document. The grammars are in:

- [`examples/Patterns.hs`](examples/Patterns.hs) — every fragment above
- [`examples/Arith.hs`](examples/Arith.hs) — the minimal precedence ladder
- [`examples/Layout.hs`](examples/Layout.hs) — indentation-sensitive `do`
- [`bench/Bench/Peg.hs`](bench/Bench/Peg.hs) — JSON, CSV, and the two
  quoted-string spellings of §5.2
