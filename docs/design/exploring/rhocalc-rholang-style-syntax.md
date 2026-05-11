# RhoCalc Rholang-Style Surface Syntax (Phases 1–2: Map, List, Bag)

**Status:** Implemented
**Date:** May 2026
**Author:** Mettail team

Cross-links:

- [docs/design/made/native-types/map-type-design.md](../made/native-types/map-type-design.md) — base Map design
- [docs/examples/rhocalc/01-language-spec.md](../../examples/rhocalc/01-language-spec.md) — surface-syntax reference
- [docs/manual/language/features/collections/00-overview.md](../../manual/language/features/collections/00-overview.md) — collection overview

---

## 1. Goal & Scope

Align the rhocalc surface syntax with [Rholang](https://rholang.io)'s syntax for
process/data terms so that programs written for either language read
identically at the source level.

- **Phase 1:** `Map` (full eight-method surface, including unary `m.size()`,
  `m.keys()`, `m.values()`).
- **Phase 2:** `List` (`[…]` literals; `.length()`, `.nth(i)`, `.concat(l)`
  method-call sugar) and `Bag` (kept as `#{…}#` — no Rholang counterpart —
  with `.size()`, `.count(e)`, `.diff(b)`, `.remove(e)`, `.union(b)` method
  sugar). `Set` is deferred.

The change is purely surface-level: AST, semantics, equations, congruence, and
rewrite rules are unchanged. The new surface forms are syntactic sugar that
`fold` to the existing prefix builtins (`GetMap`, `PutMap`, `HasMap`,
`KeysMap`, `ValuesMap`, `DeleteMap`, `MergeMap`, `Len`, `ElemList`,
`ConcatList`, `UnionBag`, `DiffBag`, `RemoveBag`, `CountBag`).

---

## 2. Background

Prior to this change, rhocalc used:

| Construct | Old rhocalc surface | Rholang |
|-----------|---------------------|---------|
| Zero process | `{}` | `Nil` |
| Parallel composition | `{ P \| Q }` (braced) or `P \| Q` (bare infix) | `P \| Q` |
| Body of `for`/`new` | `{ … }` | `{ … }` |
| Map literal | `map(k₁:v₁, k₂:v₂)` | `{k₁: v₁, k₂: v₂}` |
| Map ops | `get(m, k)`, `put(m, k, v)`, `keys(m)`, … | `m.get(k)`, `m.set(k, v)`, `m.keys()`, … |

Two collisions surfaced once we wanted Rholang-style map literals:

1. `{}` was reserved for `PZero`.
2. `{ P | Q }` (braced parallel) competed with `{ k:v }` (map literal) on the
   same opener `{`.

---

## 3. Design Decisions

### 3.1 `Nil` for the zero process

Replace `PZero . |- "{}" : Proc;` with:

```rust
PZero . |- "Nil" : Proc;
```

This frees `{}` for the empty Map literal and matches Rholang.

### 3.2 No top-level braced `PPar`

The braced rule

```rust
PPar . ps:HashBag(Proc) |- "{" ps.*sep("|") "}" : Proc;
```

is **removed** from the user-facing grammar. The infix rule

```rust
PParInfix . a:Proc, b:Proc |- a "|" b : Proc ![{
    crate::rhocalc::runtime::merge_pp_parallel(a.clone(), b.clone())
}] fold;
```

remains the canonical surface syntax for parallel composition. `PParInfix`
folds into the multiset `Proc::PPar(HashBag<Proc>)` via `merge_pp_parallel` at
the Datalog/ascent stage.

To keep equations and congruence rules that match on `Proc::PPar(...)`
compiling, the AST constructor is retained behind an internal-only grammar
rule using a reserved label `__ppar` (it never appears in user input):

```rust
PPar . ps:HashBag(Proc) |- "__ppar" "(" ps.*sep(",") ")" : Proc;
```

`{}` is therefore reserved exclusively for:

- The empty `Map` literal at expression position.
- The body of `for(...) { P }`, `new(x) in { P }`, and (future) `contract`.

### 3.3 Brace-delimited `Map` literal

`Map` overrides the default collection delimiters:

```rust
![HashMap<Proc, Proc>] as Map [ "{", "}", ",", ":" ]
```

This produces literal forms `{}`, `{k: v}`, `{k₁: v₁, k₂: v₂, …}`. We also
expose an explicit alias `Map()` for the empty case, useful in chained method
calls (e.g. `Map().set("a", 1).set("b", 2)`):

```rust
MapEmpty . |- "Map" "(" ")" : Proc ![{
    Proc::CastMap(Box::new(Map::MapLit(Default::default())))
}] fold;
```

### 3.4 Method-call sugar

Eight method-call rules `fold` into existing builtins. Each preserves the
exact semantics of its prefix counterpart:

| Method form | Lowering |
|-------------|----------|
| `m.get(k)` | `GetMap(m, k)` |
| `m.set(k, v)` | `PutMap(m, k, v)` |
| `m.contains(k)` | `HasMap(m, k)` |
| `m.delete(k)` | `DeleteMap(m, k)` |
| `m.union(n)` | `MergeMap(m, n)` |
| `m.size()` | `CastInt(NumLit(entries.len()))` (constant fold) |
| `m.keys()` | `KeysMap(m)` |
| `m.values()` | `ValuesMap(m)` |

These rules use the `[mixfix-trigger leading-terminal]` pattern introduced
into `prattail` to permit chained method calls of the form
`Map().set(1, 10).get(1)` etc. The mixfix detector accepts both the standard
shape (≥2 NTs with ≥2 terminals) and the zero-operand-after-trigger shape
(1 NT with ≥3 terminals) needed for unary methods like `m.size()`.

### 3.5 Pattern positions

`for`-receive patterns now use the new literal form:

```rhocalc
for(@{1:x, 3:4} <- c) { x }
```

instead of the old `for(@map(1:x, 3:4) <- c)`.

### 3.6 List & Bag method-call sugar

`List` already uses the Rholang-style `[a, b, c]` literal (via the
collection-delimiter override `![Vec<Proc>] as List ["[", "]", ","]`); no
literal change is needed in Phase 2. `Bag` keeps its rhocalc-only `#{a|b|…}#`
spelling — Rholang has no bag type — but gains a method-call surface for
consistency with `Map`/`List`.

| Method form | Lowering | Receiver |
|-------------|----------|----------|
| `l.length()` | `Len(l)` | List |
| `l.nth(i)` | `ElemList(l, i)` | List |
| `l.concat(r)` | `ConcatList(l, r)` | List |
| `b.size()` | `Len(b)` (extended below) | Bag (& Map via `MSize`) |
| `b.count(e)` | `CastInt(Int::CountBag(b, e))` | Bag |
| `b.diff(c)` | `DiffBag(b, c)` | Bag |
| `b.remove(e)` | `RemoveBag(b, e)` | Bag |
| `b.union(c)` | `UnionBag(b, c)` *or* `MergeMap(a, b)` | Bag *or* Map (see below) |

Each rule is a zero/one/two-operand-after-trigger mixfix that reuses the same
prattail `leading_terminals` dispatch as the Map method sugars (§3.4). Unary
methods (`.length()`, `.size()`) compile inline via the extended mixfix
detector (1 NT + ≥3 terminals).

`Len`'s native body is extended to a fourth arm handling `Proc::CastBag(_)`:
the result is the bag's total element count (sum of all multiplicities,
computed after `normalize_bag_elements` to give canonical-form bags a stable
size irrespective of surface spelling).

**Polymorphic dispatch for `.union` and `.size`:**  Both `Map` and `Bag`
expose a `union` method, and a single grammar rule cannot dispatch by
receiver category at parse time. We therefore make `MUnion`'s `fold` action
inspect the (already-folded) receiver and lower to either `MergeMap` or
`UnionBag`:

```rust
MUnion . a:Proc, b:Proc
|- a "." "union" "(" b ")" : Proc ![{
    match &a {
        Proc::CastMap(_) => Proc::MergeMap(Box::new(a.clone()), Box::new(b.clone())),
        Proc::CastBag(_) => Proc::UnionBag(Box::new(a.clone()), Box::new(b.clone())),
        _ => Proc::Err,
    }
}] fold;
```

`MSize` follows the same pattern (`CastMap` → constant-fold to a `CastInt` of
the entry count; `CastBag` → defer to `Len`, which handles bag-size
normalization). Since `fold` rules in this codebase fire on terms that are
already in canonical-literal form, the static match is sufficient — any other
shape returns `Proc::Err`, matching the existing prefix-builtin behaviour
when receivers are mistyped.

### 3.7 `@Nil` shorthand

Rholang spells `Name::NQuote(Proc::PZero)` as `@Nil` (rather than `@(Nil)`).
We add the same shorthand by introducing a Name-category fold rule that lowers
to the canonical `NQuote(PZero)` AST:

```rust
NQuoteNil .
|- "@" "Nil" : Name ![{
    Name::NQuote(Box::new(Proc::PZero))
}] fold;
```

Because `Nil` is the keyword spelling of `PZero` (§3.1), it is not in `Name`'s
FIRST set; therefore `NQuoteNil` cannot appear inside `POutputQuoted`'s
`@ <Name> ! ( q )` shape (where the `@` is consumed at the Proc level and the
inner Name parser sees `Nil` as a bare keyword it does not accept). To make
`@Nil!(q)` and `@Nil!!(q)` write the way Rholang does, we add two dedicated
send-sugar rules in `Proc`:

```rust
POutputNil . q:Proc
|- "@" "Nil" "!" "(" q ")" : Proc ![{
    Proc::POutput(
        Box::new(Name::NQuote(Box::new(Proc::PZero))),
        Box::new(q.clone()),
    )
}] fold;

PPersistOutputNil . q:Proc
|- "@" "Nil" "!!" "(" q ")" : Proc ![{
    Proc::PPersistOutput(
        Box::new(Name::NQuote(Box::new(Proc::PZero))),
        Box::new(q.clone()),
    )
}] fold;
```

They fold to the same `POutput` / `PPersistOutput` AST shape that
`POutputQuoted` would produce if its inner Name slot accepted `Nil`. Three
`Proc`-category rules now share the `@` first token (`POutputNil`,
`PPersistOutputNil`, `POutputQuoted`); the prattail dispatcher tries each
through its generated `parse_<label>` standalone function in declaration order
(NFA-style — first success wins). See §4.2 for the dispatcher change.

### 3.8 Generalised `@P` shorthand for arbitrary `P:Proc`

Rholang lets `@` quote *any* process, not just `Nil` — `@1`, `@"k"`, `@*x`,
`@(P|Q)`, etc. are all valid Names. We add a single fold rule that
generalises both `NQuote` (`@(P)`) and `NQuoteNil` (`@Nil`):

```rust
NQuoteShort . p:Proc
|- "@" p : Name ![{
    Name::NQuote(Box::new(p.clone()))
}] fold;
```

Declared *after* `NQuote` and `NQuoteNil` so that the NFA dispatcher tries
the specific forms first; `@(P)` still parses through `NQuote` (which
explicitly resets binding power at the `(` so `@(a|b)` works as expected),
and `@Nil` still parses through `NQuoteNil`. Only when both fail does the
parser fall through to `NQuoteShort`, which then drives the Proc parser at
the position after `@`.

To make literal-typed quoted channels write the way Rholang does on the
send side (`@1!(q)`, `@"k"!!(q)`), we likewise add generalised send sugars
parallel to `POutputNil` / `PPersistOutputNil`:

```rust
POutputShort . p:Proc, q:Proc
|- "@" p "!" "(" q ")" : Proc ![{
    Proc::POutput(
        Box::new(Name::NQuote(Box::new(p.clone()))),
        Box::new(q.clone()),
    )
}] fold;

PPersistOutputShort . p:Proc, q:Proc
|- "@" p "!!" "(" q ")" : Proc ![{
    Proc::PPersistOutput(
        Box::new(Name::NQuote(Box::new(p.clone()))),
        Box::new(q.clone()),
    )
}] fold;
```

These are needed because `POutputQuoted`'s `@ <Name>` slot rejects anything
not in Name FIRST (e.g. integer/string literals after `@`). Five Proc-level
rules now share the `@` opener (`POutputNil`, `PPersistOutputNil`,
`POutputQuoted`, `POutputShort`, `PPersistOutputShort`); the NFA dispatch
(§4.2) handles all of them. For inputs where multiple rules succeed (e.g.
`@Nil!(0)` matches both `POutputNil` and `POutputShort`), the fold actions
collapse to the same canonical `POutput(NQuote(PZero), 0)` AST, so the
choice is semantically transparent.

**Caveat — precedence:** Cross-category prefix rules in the current
framework cannot carry an explicit operand binding power (the
`prefix(N)` annotation is only honoured for *same-category* unary
prefix rules where `is_unary_prefix == true`). As a result, `NQuoteShort`
calls the inner Proc parser with `min_bp = 0` and consumes any Proc-level
infix that follows. Concretely, `*@1 + 0` parses as `*(@(1 + 0))`, not
`(*@1) + 0` — users who want the latter must parenthesise: `(*@1) + 0` or
fall back to the parens form `*(@1) + 0`. This matches the documented
behaviour of `POutputShort` / `PPersistOutputShort` as well: `@1+2!(0)`
parses as `(@(1+2))!(0)`. Adding an explicit cross-category prefix BP is
tracked as a future framework extension; see "out of scope" below.

---

## 4. Disambiguation

### 4.1 `{` opener

After removing braced `PPar`, the only top-level rule that opens with `{` at
an expression position is the `Map` literal. Disambiguation is therefore not
required at parse time — `{` always begins a `Map` literal.

The body braces of `for`/`new`/`contract` are matched as part of those rules'
own grammar (`for(…) { p }`, `new(…) in { p }`) and never participate in the
expression-level `{` dispatch.

A single-process body group (`{ P }` at expression position, e.g. inside a
function-call argument like `int({1 + 2}, 8)`) is no longer supported; the
expression must be written bare: `int(1 + 2, 8)`. Inside a `for`/`new` body
this never bit, since the keyword-prefixed rule already opens its own braces.

### 4.2 `@` opener with multiple frame-pushing rules

`POutputQuoted`, `POutputNil`, and `PPersistOutputNil` all dispatch from
`Token::At` in `Proc`. Prior to this change, prattail's
`write_nfa_merged_prefix_arm` (in `prattail/src/trampoline.rs`) only emitted a
fast-path frame-push for `frame_pushing[0]`, silently dropping all other
frame-pushing alternatives — only the first declared rule could fire for a
shared FIRST token.

The fix promotes any token group containing more than one frame-pushing rule
(or any frame-pushing rule alongside an inlineable rule) to a true NFA dispatch
that calls the generated standalone `parse_<label>` function for each
candidate. Each `parse_<label>` recurses through the regular `parse_<cat>`
entry, so inner sub-parses still run through the trampoline with correct
binding-power tracking. The first parser that succeeds (declaration order)
wins; if none succeed, the first error is reported. The legacy single-frame
fast path is retained for the common case of exactly one frame-pushing rule
per token.

---

## 5. Display & Semantic Invariants

- `Proc::PZero` displays as `Nil`.
- `Proc::PParInfix(a, b)` displays as `a | b`.
- `Proc::PPar(bag)` is reachable only after `fold` and displays through its
  internal-only template `__ppar(p₁, p₂, …)`. The internal form is acceptable
  for debugging and tests; it round-trips through the parser by re-parsing
  the original infix surface form. Tests that compare PPar normal forms use
  `term_eq` or substring containment rather than exact display matching.
- Map normal forms display as `{k: v, …}` via the macro-generated display
  template from the collection delimiters override.

No rewrite rules, equations, congruence rules, or runtime helpers
(`merge_pp_parallel`, `normalize_bag_elements`, COMM dispatch, etc.) were
touched. Method-call sugar produces the same reduction graph as the
corresponding prefix-form calls.

---

## 6. Migration Checklist

- [x] `languages/src/rhocalc.rs` — `PZero`, `Map` delimiter override, `Map()`
  alias, removed braced `PPar`, internal `__ppar` rule, eight Map method-call
  sugars, three List method sugars (`LLength`, `LNth`, `LConcat`), three
  bag-specific Bag method sugars (`BCount`, `BDiff`, `BRemove`),
  polymorphic `MUnion` / `MSize` (Map ∪ Bag), `Len` extended to `CastBag`,
  `NQuoteNil` Name shorthand, `POutputNil` / `PPersistOutputNil` send
  sugars, generalised `NQuoteShort` Name shorthand and
  `POutputShort` / `PPersistOutputShort` send sugars for arbitrary
  `P:Proc`.
- [x] `languages/tests/rhocalc_tests.rs` — strip outer `{…}` wraps in test
  inputs, switch `map(…)` literals to `{…}` form, switch `mod map` to method
  syntax + brace literals, refit `assert_never_reaches` helper for the new
  display, regression tests for `@Nil` (`*@Nil → Nil`,
  `for(x <- @Nil){x} | @Nil!(0) → 0`, `@Nil!!(0)` parses), regression tests
  for `@P` (`*@1 → 1`, `*@"hello" → "hello"`, `*@true → true`,
  `for(x <- @1){x} | @1!(42) → 42`, `*@*y → *y` via `QuoteDrop`, plus the
  documented greedy-precedence cases), new `mod list` + `mod bag`
  sub-modules covering `.length()`, `.nth(i)`, `.concat(r)`, `.size()`
  (via extended `Len`), `.count(e)`, `.diff(b)`, `.remove(e)`, and
  polymorphic `.union`.
- [x] `repl/src/examples/rhocalc.rs` — strip outer braces from process
  examples; `{}` empty processes become `Nil`.
- [x] `repl/src/examples/rhocalc-patterns.txt`,
  `repl/src/examples/rhocalc-casting.txt` — replace `{ P | Q }` wrappers with
  bare infix.
- [x] `prattail` — `InfixOperator.leading_terminals` and `write_mixfix_led`
  grouping by trigger to support method-call dispatch; mixfix detection
  extended to 1-NT/3+T shape so zero-operand-after-trigger rules
  (`m.size()`, `m.keys()`, `m.values()`) compile inline without a frame
  push; `write_nfa_merged_prefix_arm` extended to NFA-try multiple
  frame-pushing rules sharing a dispatch token via their generated
  `parse_<label>` standalone functions.
- [x] `docs/design/made/native-types/map-type-design.md` — note rhocalc
  override and method-call sugar layer.
- [x] `docs/manual/language/features/collections/00-overview.md` — refresh
  Map subsection.
- [x] `docs/examples/rhocalc/01-language-spec.md`,
  `docs/examples/rhocalc/06-runtime-evaluation.md` — refresh surface
  examples.

---

## 7. Out of Scope (Followups)

- Rholang-style `Set` (`Set(…)`).
- Rholang `++` infix concat for `List` / `Str` (currently only the
  method-call form `l.concat(r)` is sugared).
- Map / List pattern matching beyond literal swap (e.g., `{k: x, ..}` /
  `[a, ..rest]` partial patterns).
- Rholang `contract` keyword.
- Explicit binding power for cross-category prefix rules (`@P`,
  `POutputShort`, …): currently the framework's `prefix(N)` annotation
  only fires for *same-category* unary prefixes (`is_unary_prefix == true`),
  so `@P` consumes any trailing Proc infix greedily. Extending
  `prefix_bp` propagation to cross-category prefix rules and threading it
  into the unary-prefix dispatch would let `*@1 + 0` parse as
  `(*@1) + 0` without explicit parentheses.

---

## 8. Status

**Implemented** (May 2026). Tests pass under
`cargo test -p mettail-languages --test rhocalc_tests`. Once the design doc
review is complete this document moves to
`docs/design/made/native-types/`.
