# RhoCalc Rholang-Style Surface Syntax (Phase 1: Map)

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
identically at the source level. Phase 1 covers **`Map`** only; `List`, `Bag`,
and `Set` are deferred to a follow-up. The full eight-method Map surface
(including unary `m.size()`, `m.keys()`, `m.values()`) is now in scope.

The change is purely surface-level: AST, semantics, equations, congruence, and
rewrite rules are unchanged. The new surface forms are syntactic sugar that
`fold` to the existing builtins (`GetMap`, `PutMap`, `HasMap`, `KeysMap`,
`ValuesMap`, `DeleteMap`, `MergeMap`, `Len`).

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

---

## 4. Disambiguation: `{` opener

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
  alias, removed braced `PPar`, internal `__ppar` rule, six method-call sugar
  rules.
- [x] `languages/tests/rhocalc_tests.rs` — strip outer `{…}` wraps in test
  inputs, switch `map(…)` literals to `{…}` form, switch `mod map` to method
  syntax + brace literals, refit `assert_never_reaches` helper for the new
  display.
- [x] `repl/src/examples/rhocalc.rs` — strip outer braces from process
  examples; `{}` empty processes become `Nil`.
- [x] `repl/src/examples/rhocalc-patterns.txt`,
  `repl/src/examples/rhocalc-casting.txt` — replace `{ P | Q }` wrappers with
  bare infix.
- [x] `prattail` — `InfixOperator.leading_terminals` and `write_mixfix_led`
  grouping by trigger to support method-call dispatch; mixfix detection
  extended to 1-NT/3+T shape so zero-operand-after-trigger rules
  (`m.size()`, `m.keys()`, `m.values()`) compile inline without a frame
  push.
- [ ] `docs/design/made/native-types/map-type-design.md` — note rhocalc
  override and method-call sugar layer.
- [ ] `docs/manual/language/features/collections/00-overview.md` — refresh
  Map subsection.
- [ ] `docs/examples/rhocalc/01-language-spec.md`,
  `docs/examples/rhocalc/06-runtime-evaluation.md` — refresh surface
  examples.

---

## 7. Out of Scope (Followups)

- Rholang-style `List` (`[…]`), `Bag` (no Rholang counterpart; keep `#{…}#`),
  `Set` (`Set(…)`).
- `@Nil` shorthand for `Name::NQuote(Proc::PZero)`.
- Map pattern matching beyond literal swap (e.g., `{k: x, ..}` partial
  patterns).
- Rholang `contract` keyword.

---

## 8. Status

**Implemented** (May 2026). Tests pass under
`cargo test -p mettail-languages --test rhocalc_tests`. Once the design doc
review is complete this document moves to
`docs/design/made/native-types/`.
