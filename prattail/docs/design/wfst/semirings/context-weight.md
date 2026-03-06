# ContextWeight -- Design & Pipeline Integration

*Date: 2026-03-01*

The set semiring `(P(Labels), union, intersection, empty, U)` tracks which grammar
rules contribute to each dispatch token using a 128-bit bitset. It answers two
questions: "which rules can fire for this token?" and "do any tokens have
overlapping rule coverage?" A set cardinality greater than 1 signals ambiguity
that requires tropical resolution or NFA spillover.

---

## Table of Contents

1. [Role in Pipeline](#1-role-in-pipeline)
2. [BitSet Representation](#2-bitset-representation)
3. [API Surface](#3-api-surface)
4. [Display Format](#4-display-format)
5. [Ordering](#5-ordering)
6. [Pipeline Integration](#6-pipeline-integration)
7. [ProductWeight Composition](#7-productweight-composition)
8. [Semiring Properties](#8-semiring-properties)
9. [Test Coverage](#9-test-coverage)
10. [Source Reference & See Also](#10-source-reference--see-also)

---

## 1. Role in Pipeline

ContextWeight serves three codegen-time analysis functions:

| Function                    | Integration Point                    | Description                                                                                                                  |
|-----------------------------|--------------------------------------|------------------------------------------------------------------------------------------------------------------------------|
| **Ambiguity diagnosis**     | `compute_composed_dispatch()`        | Tokens where `\|ContextWeight\| > 1` indicate multiple rules competing for the same dispatch token                           |
| **Follow-set tightening**   | Recovery WFST construction           | Intersection of context weights narrows sync token candidates to only those tokens where rules actually overlap              |
| **NFA spillover decisions** | `categories_needing_nfa_spillover()` | Categories where any dispatch token has `\|ContextWeight\| > 1` need forced-prefix replay via thread-local spillover buffers |

ContextWeight is a **type-level formalization** of "which rules reach this token."
The information it carries is equivalent to the set-valued annotation that
`compute_composed_dispatch()` (`prediction.rs:1461-1584`) builds implicitly when
it collects multiple `ComposedEntry` values per (category, token) key. The
semiring abstraction makes this explicit and composable.

---

## 2. BitSet Representation

ContextWeight wraps a bare `u128` (`semiring.rs:643`):

```rust
#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash)]
pub struct ContextWeight(u128);
```

**Design rationale**:

- **128-bit capacity**: Supports up to 128 distinct rule labels per category.
  Real-world grammars (including rhocalc with 36+ rules across categories)
  are well within this limit.
- **Copy semantics**: `u128` is `Copy`, so ContextWeight passes by value with
  no heap allocation, no reference counting, and no lifetime entanglement.
  This is critical for embedding in `ProductWeight<TropicalWeight, ContextWeight>`
  which must also be `Copy`.
- **Single-instruction operations**: On x86-64, `u128` bitwise OR, AND, and
  `count_ones` (popcnt) compile to 2-instruction sequences (one per 64-bit
  half). No branching, no allocation, no function calls.
- **No external dependency**: A `BitVec` or `FixedBitSet` would add a crate
  dependency and lose `Copy`. The raw `u128` is the simplest correct
  representation for the capacity needed.

**Capacity limitation**: If a grammar exceeds 128 rule labels per category,
ContextWeight would need to be widened (e.g., to `[u128; 2]` for 256 labels)
or replaced with a heap-allocated bitset. This scenario is unlikely for
practical grammars and is not currently handled.

---

## 3. API Surface

ContextWeight provides five methods beyond the Semiring trait (`semiring.rs:645-682`):

### 3a. Constructor: `new(bits: u128)`

Creates a ContextWeight from a raw bitset. Used primarily in tests and for
deserializing precomputed context sets.

```rust
pub const fn new(bits: u128) -> Self {
    ContextWeight(bits)
}
```

### 3b. Singleton: `singleton(label_id: u8)`

Creates a ContextWeight with exactly one rule label set. This is the primary
constructor for pipeline use: each rule in the grammar gets a unique `label_id`
in `[0, 128)`, and `singleton(label_id)` produces its context weight.

```rust
pub const fn singleton(label_id: u8) -> Self {
    assert!(label_id < 128, "label_id must be < 128");
    ContextWeight(1u128 << label_id)
}
```

The `assert!` is a compile-time check (the function is `const`). At runtime,
the shift would overflow for `label_id >= 128`, producing incorrect results.
The assert prevents this.

### 3c. Membership: `contains(label_id: u8)`

Tests whether a specific rule label is in the set. Used to check if a
particular rule contributes to a given dispatch token.

```rust
pub const fn contains(&self, label_id: u8) -> bool {
    (self.0 >> label_id) & 1 == 1
}
```

### 3d. Insertion: `insert(label_id: u8)`

Returns a new ContextWeight with the given label added. Functional (returns
a new value, does not mutate) because ContextWeight is `Copy`.

```rust
pub const fn insert(self, label_id: u8) -> Self {
    ContextWeight(self.0 | (1u128 << label_id))
}
```

### 3e. Cardinality: `count()`

Returns the number of set bits (contributing rules). This is the key metric:
`count() > 1` indicates ambiguity.

```rust
pub const fn count(&self) -> u32 {
    self.0.count_ones()
}
```

Compiles to a hardware `popcnt` instruction on x86-64 (two `popcnt` + `add`
for the two 64-bit halves).

---

## 4. Display Format

The `Display` implementation (`semiring.rs:741-751`) uses three formats:

| Condition           | Output       | Meaning                              |
|---------------------|--------------|--------------------------------------|
| `bits == 0`         | `∅`          | Empty set -- no rules reachable      |
| `bits == u128::MAX` | `U`          | Universal set -- all rules reachable |
| Otherwise           | `{Nb\|bits}` | N set bits, raw bitset value         |

Example outputs:

```
∅                     — zero (empty set)
U                     — one (universal set)
{2b|10}               — 2 bits set, raw value 10 (binary: 1010 → rules 1 and 3)
{1b|32}               — 1 bit set, raw value 32 (binary: 100000 → rule 5)
```

The raw bits value enables debugging: `{2b|10}` can be decoded to binary `1010`
to identify the exact contributing rules (labels 1 and 3).

---

## 5. Ordering

ContextWeight implements `Ord` with a two-level comparison (`semiring.rs:732-738`):

```rust
impl Ord for ContextWeight {
    fn cmp(&self, other: &Self) -> Ordering {
        self.0
            .count_ones()
            .cmp(&other.0.count_ones())
            .then_with(|| self.0.cmp(&other.0))
    }
}
```

**Level 1: Set cardinality** (`count_ones`). Fewer contributing rules = lower
weight = more specific dispatch. A singleton set (`count = 1`) is unambiguous
and ranks below a 3-element set (`count = 3`) which has 3-way ambiguity.

**Level 2: Raw bits** (deterministic tiebreaker). Two context weights with the
same cardinality are distinguished by their raw u128 value. This ensures `Ord`
is total and deterministic: codegen output does not depend on hash map iteration
order or other non-deterministic factors.

**Compatibility with ProductWeight**: When composed as
`ProductWeight<TropicalWeight, ContextWeight>`, the lexicographic ordering
compares TropicalWeight first (priority ranking), then ContextWeight (specificity
tiebreaker). Among paths with equal tropical cost, the more specific path
(fewer contributing rules) wins.

---

## 6. Pipeline Integration

### 6a. Where ContextWeight Is Computed

During WFST construction, each dispatch token accumulates a ContextWeight by
unioning the singletons of all rules that can fire for that token:

```
for each (category, token) in dispatch table:
    context = ContextWeight::zero()    // ∅
    for each rule R dispatched by token:
        context = context.plus(&ContextWeight::singleton(R.label_id))
    // context now contains the set of all rules for this token
```

This computation is the ContextWeight analog of the `CountingWeight::new(entries.len())`
in `compute_composed_dispatch()` (`prediction.rs:1555`). Where CountingWeight
counts alternatives, ContextWeight names them.

### 6b. Ambiguity Diagnosis

Tokens where `|ContextWeight| > 1` have multiple contributing rules. The
context weight identifies exactly **which** rules are involved:

```
Given: context = ContextWeight::new(0b1010)  // rules 1 and 3
  count() == 2  →  2-way ambiguity
  contains(1) == true  →  rule 1 participates
  contains(3) == true  →  rule 3 participates
```

This is strictly more informative than `CountingWeight::new(2)`, which only
reports the count without identifying the contributing rules. The ambiguity
warning can include rule labels:

```
warning: 2-way ambiguity at (Proc, DFA state 5): rules PInput, POutput
  both dispatch on Token::Ident
  Resolved by tropical shortest path → PInput
```

### 6c. Follow-Set Tightening

ContextWeight enables a more precise selection of sync tokens for error
recovery. The current recovery WFST uses the category's full FOLLOW set
plus structural delimiters as sync tokens (`recovery.rs:441-442`). With
ContextWeight, the sync token set can be narrowed:

```
for each candidate sync token T:
    context_at_T = accumulated ContextWeight for T
    // Only include T as a sync token if it participates in rules
    // that are actually reachable from the error position
    if context_at_T.times(&reachable_rules).is_zero():
        skip T  // no overlap with reachable rules
```

The intersection (`times`) of the token's context weight with the set of
reachable rules filters out sync tokens that belong exclusively to
unreachable rules. This reduces false synchronization points, preventing the
recovery system from "snapping" to a token that will immediately fail again.

### 6d. NFA Spillover Decisions

The NFA disambiguation system (`trampoline.rs:129-136,
categories_needing_nfa_spillover()`) determines which categories need
forced-prefix replay. ContextWeight provides a precise predicate: a category
needs NFA spillover if and only if any dispatch token in that category has
`|ContextWeight| > 1`. This replaces the current structural analysis
(`group_rd_by_dispatch_token()`) with a weight-based criterion that accounts
for WFST pruning -- a token may have multiple rules in the grammar but only
one surviving rule after beam pruning, eliminating the need for spillover.

---

## 7. ProductWeight Composition

### 7a. `ProductWeight<TropicalWeight, ContextWeight>`

The primary composition pairs tropical priority with rule-set tracking:

```rust
type ContextDispatch = ProductWeight<TropicalWeight, ContextWeight>;
```

| Operation | Left (Tropical) | Right (Context)      | Combined Semantics                   |
|-----------|-----------------|----------------------|--------------------------------------|
| `plus`    | `min(a, b)`     | `union(A, B)`        | Best weight + all contributing rules |
| `times`   | `a + b`         | `intersection(A, B)` | Accumulated cost + shared rules      |
| `zero`    | `+inf`          | `∅`                  | Unreachable, no rules                |
| `one`     | `0.0`           | `U`                  | Zero cost, all rules eligible        |

**Plus semantics** (`min`, `union`): When merging parallel paths, select the
best tropical weight while collecting **all** rules that contributed to any
path. This answers: "What is the best priority, and which rules participated
in the competition?"

**Times semantics** (`add`, `intersection`): When sequencing path segments,
accumulate the tropical cost while retaining only rules common to **both**
segments. This answers: "What is the total cost, and which rules are consistent
across both segments?"

### 7b. Example: Composed Dispatch

Consider category `Proc` with two rules dispatched by `Token::Ident`:

```
Rule PInput:  TropicalWeight(0.5),  ContextWeight::singleton(0)  →  {0}
Rule POutput: TropicalWeight(1.0),  ContextWeight::singleton(1)  →  {1}
```

Product weights:

```
pw_input  = (0.5, {0})
pw_output = (1.0, {1})
```

Plus (merge alternatives):

```
pw_input.plus(&pw_output) = (min(0.5, 1.0), {0} ∪ {1}) = (0.5, {0, 1})
```

Result: best weight is 0.5 (PInput), but both rules {0, 1} contributed.
The `count() == 2` signals ambiguity; the tropical component resolves it.

### 7c. Viterbi Compatibility

ContextWeight has `zero = ∅` which is the smallest value under `Ord`
(`count_ones() == 0`). This means zero is "better" than non-zero, which is
the **opposite** of what Viterbi requires (zero should be worst). The same
caveat applies as for CountingWeight (see `product-weight.md` section 4).

**Workaround**: Always compose with TropicalWeight via ProductWeight. The
lexicographic ordering ensures TropicalWeight (`zero = +inf`, largest under
`Ord`) dominates, making the product safe for Viterbi. The ContextWeight
component is carried along as metadata for post-Viterbi analysis, not used
for path selection.

---

## 8. Semiring Properties

### 8a. Idempotent Plus

ContextWeight `plus` (union) is **idempotent**: `A union A = A`. This means
repeated merging of the same rule evidence does not change the result -- a
desirable property for fixed-point reachability analysis.

### 8b. Distributivity

Intersection distributes over union, as required by the semiring axioms:

```
A intersection (B union C) = (A intersection B) union (A intersection C)
```

This is a fundamental property of set algebra and is verified by
`test_context_weight_distributivity` (`semiring.rs:1578-1588`).

### 8c. Position in Semiring Hierarchy

```
           ┌─────────┐               ┌───────┐
Boolean ◀──┤ project ├──  Context  ──┤ embed ├──▶  Counting
   ▲       └─────────┘       ▲       └───────┘
   │                         │
   │                         └── "which rules contribute?"
   │
   └── "is there any path?"
```

- **Boolean projection**: `ContextWeight -> BooleanWeight` via
  `BooleanWeight(!context.is_zero())`. Any non-empty context set is reachable.
- **Counting projection**: `ContextWeight -> CountingWeight` via
  `CountingWeight(context.count() as u64)`. The set cardinality equals the
  derivation count for non-overlapping singletons.
- **Inverse**: CountingWeight cannot recover ContextWeight (it loses which
  rules are in the set). ContextWeight is strictly more informative.

---

## 9. Test Coverage

Seven tests in `semiring.rs:1519-1735` cover ContextWeight:

| Test                                         | Lines     | What It Verifies                                                                                       |
|----------------------------------------------|-----------|--------------------------------------------------------------------------------------------------------|
| `test_context_weight_semiring_laws`          | 1519-1543 | Zero/one identity, zero annihilation, commutativity of plus and times                                  |
| `test_context_weight_union_intersection`     | 1545-1555 | Plus = union (`0b1010 \| 0b1100 = 0b1110`), times = intersection (`0b1010 & 0b1100 = 0b1000`)          |
| `test_context_weight_singleton_and_contains` | 1557-1569 | `singleton(5)` sets bit 5, `contains()` membership, `insert()` adds bit, `count()` reports cardinality |
| `test_context_weight_idempotent_plus`        | 1571-1576 | `a.plus(&a) == a` -- union idempotency                                                                 |
| `test_context_weight_distributivity`         | 1578-1588 | `a.times(&b.plus(&c)) == a.times(&b).plus(&a.times(&c))` -- intersection distributes over union        |
| `test_context_weight_ordering`               | 1590-1601 | `empty < singleton < two_bits < universal` -- cardinality-based ordering                               |
| `test_context_weight_display`                | 1603-1608 | Format strings: `"∅"` for zero, `"U"` for one, `"{2b\|10}"` for `0b1010`                               |

One additional test covers ProductWeight composition:

| Test                                        | Lines     | What It Verifies                                                                                    |
|---------------------------------------------|-----------|-----------------------------------------------------------------------------------------------------|
| `test_context_weight_product_with_tropical` | 1720-1735 | `ProductWeight<TropicalWeight, ContextWeight>` plus = `(min, union)`, times = `(add, intersection)` |

---

## 10. Source Reference & See Also

- **Type definition**: `semiring.rs:622-757`
- **Struct and constructor**: `semiring.rs:642-682`
- **Semiring impl**: `semiring.rs:684-722`
- **Ord impl (cardinality + tiebreak)**: `semiring.rs:724-738`
- **Display impl**: `semiring.rs:741-751`
- **Tests (7 ContextWeight)**: `semiring.rs:1515-1609`
- **ProductWeight composition test**: `semiring.rs:1719-1735`
- **Ambiguity detection (CountingWeight analog)**: `prediction.rs:1544-1577`
- **NFA spillover categories**: `trampoline.rs:129-136`
- **Recovery WFST sync tokens**: `recovery.rs:430-466`
- **Theory**: `prattail/docs/theory/wfst/semirings.md` (to be extended with ContextWeight section)
- **Product semiring**: `product-weight.md` -- generic composition framework
- **Counting semiring**: `counting-weight.md` -- the cardinality-only projection
- **Boolean semiring**: `boolean-weight.md` -- the reachability projection
