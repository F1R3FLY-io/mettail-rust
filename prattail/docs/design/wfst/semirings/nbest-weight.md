# NbestWeight -- Viterbi-N-Best Semiring

> **Date:** 2026-03-01

The N-best semiring `(Sorted[N], merge_nbest, concat_nbest, [], [(0, 0.0)])`
tracks the top N parse alternatives simultaneously in a fixed-size, weight-sorted
array. Where TropicalWeight retains only the single best path (Viterbi-1),
NbestWeight generalizes to Viterbi-N: it carries up to N alternative derivations
ranked by tropical cost, enabling lazy disambiguation, confidence scoring, and
compact parse forest construction.

---

## Table of Contents

1. [Problem: Tracking Multiple Parse Alternatives](#1-problem-tracking-multiple-parse-alternatives)
2. [Data Structures](#2-data-structures)
3. [The Copy Constraint Solution](#3-the-copy-constraint-solution)
4. [Key Methods](#4-key-methods)
5. [merge_nbest Algorithm (Plus)](#5-merge_nbest-algorithm-plus)
6. [concat_nbest Algorithm (Times)](#6-concat_nbest-algorithm-times)
7. [Semiring Axioms](#7-semiring-axioms)
8. [Ordering](#8-ordering)
9. [Display Format](#9-display-format)
10. [Use Cases](#10-use-cases)
11. [NbestWeight<2>: Binary Confidence Decisions](#11-nbestweight2-binary-confidence-decisions)
12. [Test Coverage](#12-test-coverage)
13. [Source Reference & See Also](#13-source-reference--see-also)

---

## 1. Problem: Tracking Multiple Parse Alternatives

TropicalWeight (Viterbi-1) computes the single lowest-cost parse path. This is
correct and efficient, but it discards all runners-up at each `plus` (min)
operation. Three scenarios demand awareness of alternatives:

| Scenario                | What Is Lost                                                                                   | Consequence                                       |
|-------------------------|------------------------------------------------------------------------------------------------|---------------------------------------------------|
| **Lazy disambiguation** | If the best parse fails downstream (e.g., type error), there is no second-best to fall back to | Hard failure where soft recovery was possible     |
| **Confidence scoring**  | Without the second-best weight, we cannot measure how decisively the best parse won            | Cannot distinguish "clear winner" from "near-tie" |
| **Parse forest**        | N > 1 alternatives form a compact forest for downstream analysis                               | Cannot enumerate alternative readings             |

NbestWeight solves all three by carrying the top N entries through every semiring
operation. Each entry is a `(path_id, TropicalWeight)` pair identifying both
**which** derivation it represents and **how costly** it is.

---

## 2. Data Structures

### 2a. NbestEntry

A single entry in the N-best list (`semiring.rs:1373-1391`):

```rust
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct NbestEntry {
    pub path_id: u32,
    pub weight: TropicalWeight,
}
```

| Field     | Type             | Semantics                                                                                                                   |
|-----------|------------------|-----------------------------------------------------------------------------------------------------------------------------|
| `path_id` | `u32`            | Unique identifier for the derivation path. Assigned at construction; combined via wrapping arithmetic during `concat_nbest` |
| `weight`  | `TropicalWeight` | Tropical cost of this derivation. Lower = better                                                                            |

The `path_id` enables deduplication: when two paths through different WFST arcs
converge on the same derivation, `merge_nbest` keeps the lower-weight occurrence
and discards the duplicate.

### 2b. NbestWeight\<const N: usize\>

The semiring carrier type (`semiring.rs:1417-1424`):

```rust
#[derive(Clone, Copy, Debug)]
pub struct NbestWeight<const N: usize> {
    entries: [Option<NbestEntry>; N],
    len: usize,
}
```

| Field     | Type                      | Invariants                                                                                                                              |
|-----------|---------------------------|-----------------------------------------------------------------------------------------------------------------------------------------|
| `entries` | `[Option<NbestEntry>; N]` | Sorted by weight (ascending). `Some` values are packed at the front: `entries[0..len]` are all `Some`, `entries[len..N]` are all `None` |
| `len`     | `usize`                   | Count of valid entries. `0 <= len <= N`                                                                                                 |

The array is **packed**: valid entries occupy contiguous positions `[0, len)`.
This invariant is maintained by all constructors and operations, enabling
efficient iteration without scanning the full array.

---

## 3. The Copy Constraint Solution

The `Semiring` trait requires `Copy` (`semiring.rs:36`):

```rust
pub trait Semiring: Clone + Copy + fmt::Debug + PartialEq + Send + Sync + 'static { ... }
```

This rules out heap-allocated containers like `Vec<NbestEntry>` or
`BinaryHeap<NbestEntry>`. The solution is to use a **const-generic fixed-size
array**:

```
[Option<NbestEntry>; N]
```

This works because:

1. **`NbestEntry` is `Copy`**: It contains `u32` (Copy) and `TropicalWeight`
   (Copy, wraps `f64`).
2. **`Option<NbestEntry>` is `Copy`**: `Option<T>` derives `Copy` when `T: Copy`.
3. **`[T; N]` is `Copy`**: Fixed-size arrays derive `Copy` when `T: Copy`.
4. **`usize` is `Copy`**: The `len` field is trivially copyable.

Therefore `NbestWeight<N>` as a whole is `Copy` for any `N`. The const generic
`N` is resolved at compile time, so `NbestWeight<2>` and `NbestWeight<4>` are
distinct types with distinct array sizes -- no runtime overhead, no allocator
involvement.

```
 NbestWeight<4> memory layout (stack-allocated)
 ┌─────────────────────────────────────────────────────────┐
 │ entries[0]   entries[1]   entries[2]   entries[3]   len │
 │ ┌──────────┐ ┌──────────┐ ┌──────────┐ ┌──────────┐     │
 │ │Some(e0)  │ │Some(e1)  │ │None      │ │None      │  2  │
 │ └──────────┘ └──────────┘ └──────────┘ └──────────┘     │
 │  path_id=1    path_id=3                                 │
 │  weight=0.5   weight=2.0                                │
 └─────────────────────────────────────────────────────────┘
```

**Trade-off**: The fixed-size array wastes space when `len < N`. For small N
(2-8), this is negligible. For N = 64, each `NbestWeight` occupies
64 x (4 + 8) + 8 = 776 bytes on the stack. Practical N values are 2 (confidence
gap) and 4 (parse forest), keeping the per-weight overhead at 32-56 bytes.

---

## 4. Key Methods

Six methods beyond the `Semiring` trait provide the NbestWeight API
(`semiring.rs:1426-1497`):

### 4a. `empty() -> Self`

Creates the zero element: an empty N-best list with no valid entries.

```rust
pub const fn empty() -> Self {
    NbestWeight { entries: [None; N], len: 0 }
}
```

### 4b. `singleton(path_id: u32, weight: TropicalWeight) -> Self`

Creates an N-best weight with exactly one entry. This is the primary constructor
for embedding a single derivation path into the semiring.

```rust
pub fn singleton(path_id: u32, weight: TropicalWeight) -> Self {
    let mut entries = [None; N];
    entries[0] = Some(NbestEntry::new(path_id, weight));
    NbestWeight { entries, len: 1 }
}
```

### 4c. `from_entries(input: Vec<NbestEntry>) -> Self`

Bulk constructor: sorts by weight, deduplicates by `path_id`, and truncates to
N entries. Used when the entry set is not pre-sorted (e.g., collecting
cross-product results in `concat_nbest`).

```rust
pub fn from_entries(mut input: Vec<NbestEntry>) -> Self {
    input.sort_by(|a, b| a.weight.cmp(&b.weight));
    input.dedup_by(|a, b| a.path_id == b.path_id);
    // ... truncate to N, pack into array
}
```

**Sort-then-dedup correctness**: `dedup_by` removes consecutive duplicates.
Since the input is sorted by weight, duplicate `path_id`s are adjacent only if
they happen to have nearby weights. For the general case (duplicates scattered
by weight), the two-pointer merge in `merge_nbest` handles dedup explicitly.
`from_entries` is intended for freshly-generated candidates (cross-product
output) where `path_id` collisions are rare.

### 4d. `best() -> Option<&NbestEntry>`

Returns the lowest-weight entry, or `None` if the list is empty. Equivalent
to `self.get(0)`.

```rust
pub const fn best(&self) -> Option<&NbestEntry> {
    self.get(0)
}
```

### 4e. `confidence_gap() -> f64`

Returns the weight difference between the best and second-best entries. A large
gap indicates high confidence; the best parse is decisively better than the
runner-up.

```rust
pub fn confidence_gap(&self) -> f64 {
    match (self.get(0), self.get(1)) {
        (Some(best), Some(second)) => second.weight.value() - best.weight.value(),
        _ => f64::INFINITY,
    }
}
```

Returns `f64::INFINITY` when fewer than 2 entries exist, indicating maximum
confidence (no competitor).

### 4f. `iter() -> impl Iterator<Item = &NbestEntry>`

Iterates over valid entries in weight-ascending order (best first).

```rust
pub fn iter(&self) -> impl Iterator<Item = &NbestEntry> {
    self.entries[..self.len].iter().filter_map(|e| e.as_ref())
}
```

---

## 5. merge_nbest Algorithm (Plus)

The `plus` operation merges two N-best lists, keeping the top N entries by weight
with deduplication by `path_id` (`semiring.rs:1501-1543`).

### 5a. Algorithm: Two-Pointer Merge with Dedup

Both input lists are sorted by weight (invariant maintained by all operations).
A standard two-pointer merge produces a sorted output:

```
 self:   [(1, 0.5), (3, 2.0)]              -- sorted by weight
 other:  [(2, 1.0), (1, 3.0), (4, 4.0)]    -- sorted by weight
                                             ─────────────────
 merged: [(1, 0.5), (2, 1.0), (3, 2.0)]    -- top 3, deduped
```

Pseudocode:

```
merge_nbest(self, other) -> NbestWeight<N>:
    merged = [None; N]
    count = 0
    i = 0   // pointer into self.entries
    j = 0   // pointer into other.entries

    while count < N and (i < self.len or j < other.len):
        // Select the entry with the lower weight
        if i exhausted:       take from other[j++]
        else if j exhausted:  take from self[i++]
        else if self[i].weight <= other[j].weight:
                              take from self[i++]
        else:                 take from other[j++]

        // Dedup: skip if path_id already in merged[0..count]
        if entry.path_id not in merged[0..count]:
            merged[count++] = entry

    return NbestWeight { entries: merged, len: count }
```

### 5b. Complexity

| Component             | Cost                          |
|-----------------------|-------------------------------|
| Two-pointer scan      | O(self.len + other.len)       |
| Dedup check per entry | O(count), where count <= N    |
| Total                 | O((self.len + other.len) x N) |

Since both `self.len` and `other.len` are bounded by N, the total complexity is
**O(N^2)**. For typical N values (2-8), this is 4-64 operations -- entirely
negligible.

### 5c. Dedup Semantics

When two entries share the same `path_id`, the lower-weight occurrence wins.
This is guaranteed by the two-pointer merge order: entries are consumed in
weight-ascending order, so the first occurrence of any `path_id` is
necessarily the lowest-weight one. Subsequent occurrences are skipped by the
linear scan of `merged[0..count]`.

```
 Input:  self  = [(path 1, weight 2.0)]
         other = [(path 1, weight 5.0)]
                          ─────────────
 Step 1: take self[0] = (1, 2.0)        → merged = [(1, 2.0)]
 Step 2: take other[0] = (1, 5.0)       → path_id 1 already in merged, skip
                          ─────────────
 Result: [(1, 2.0)]                      -- kept the better weight
```

---

## 6. concat_nbest Algorithm (Times)

The `times` operation computes the cross-product of two N-best lists, combining
weights via tropical multiplication (addition of f64 values) and combining
path IDs via a hash-like function (`semiring.rs:1547-1566`).

### 6a. Algorithm: Cross-Product with Sort and Truncate

```
concat_nbest(self, other) -> NbestWeight<N>:
    if self.is_empty() or other.is_empty():
        return empty()

    candidates = []
    for a in self.iter():
        for b in other.iter():
            combined_weight = a.weight.times(&b.weight)   // f64 addition
            combined_id = a.path_id * 31 + b.path_id      // wrapping arithmetic
            candidates.push((combined_id, combined_weight))

    return from_entries(candidates)   // sort, dedup, truncate to N
```

### 6b. Path ID Combination

Path IDs are combined using wrapping multiply-and-add:

```
combined_id = a.path_id.wrapping_mul(31).wrapping_add(b.path_id)
```

This is a lightweight hash combination that distributes well for small integer
inputs. The constant 31 is a standard hash multiplier (used in Java's
`String.hashCode()`). Wrapping arithmetic prevents overflow panics while
maintaining the distribution properties.

**Collision risk**: Two distinct `(a, b)` pairs can produce the same
`combined_id`. This is acceptable because `from_entries` deduplicates by
`path_id`, keeping the lower-weight occurrence. In practice, path IDs are
assigned sequentially from small integers, and collisions are rare for N <= 8.

### 6c. Complexity

| Component                 | Cost                             |
|---------------------------|----------------------------------|
| Cross-product enumeration | O(self.len x other.len) = O(N^2) |
| Sort candidates           | O(N^2 log N^2) = O(N^2 log N)    |
| Dedup + truncate          | O(N^2)                           |
| Total                     | **O(N^2 log N)**                 |

For N = 4, this is at most 16 candidates sorted -- effectively constant time.

### 6d. Diagram: Cross-Product Merge

```
 self = [(A, 1.0), (B, 2.0)]
 other = [(X, 0.5), (Y, 1.5)]
                    ────────────────────────────
 Cross-product:
   (A, X) → weight 1.0 + 0.5 = 1.5
   (A, Y) → weight 1.0 + 1.5 = 2.5
   (B, X) → weight 2.0 + 0.5 = 2.5
   (B, Y) → weight 2.0 + 1.5 = 3.5
                    ────────────────────────────
 Sorted:  [(AX, 1.5), (AY, 2.5), (BX, 2.5), (BY, 3.5)]
 Top N=2: [(AX, 1.5), (AY, 2.5)]
```

---

## 7. Semiring Axioms

NbestWeight implements `Semiring` (`semiring.rs:1569-1622`) with the following
identity and annihilation properties:

### 7a. Carrier, Operations, and Identities

```
Carrier:    Sorted arrays of up to N (path_id, TropicalWeight) pairs
⊕  (plus):   merge_nbest — two-pointer merge, keep top N, dedup
⊗  (times):  concat_nbest — cross-product, sort, truncate to N
0̄ (zero):   [] (empty array, no paths)
1̄ (one):    [(0, 0.0)] (single zero-cost path with id 0)
```

### 7b. Axiom Verification

| Axiom                    | Holds       | Justification                                                                                                                                                                                                                                             |
|--------------------------|-------------|-----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
| 0̄ ⊕  a = a               | Yes         | Merging empty with a produces a unchanged                                                                                                                                                                                                                 |
| a ⊕  0̄ = a               | Yes         | Symmetric case                                                                                                                                                                                                                                            |
| 1̄ ⊗  a = a               | Yes         | Cross-product of `[(0, 0.0)]` with a adds 0.0 to each weight, preserving order. Path IDs change (0*31 + id = id), preserving the entries                                                                                                                  |
| a ⊗  1̄ = a               | Yes         | Symmetric: `id*31 + 0 = id*31`. Weight preserved. Path ID transforms but remains unique                                                                                                                                                                   |
| 0̄ ⊗  a = 0̄               | Yes         | Empty cross-product returns empty immediately (`semiring.rs:1548-1549`)                                                                                                                                                                                   |
| a ⊗  0̄ = 0̄               | Yes         | Symmetric case                                                                                                                                                                                                                                            |
| ⊕  commutativity         | Yes         | Two-pointer merge produces same sorted result regardless of argument order (merge is stable on equal weights)                                                                                                                                             |
| ⊗  distributivity over ⊕ | Approximate | Due to truncation at N, `a ⊗  (b ⊕  c)` and `(a ⊗  b) ⊕  (a ⊗  c)` may differ when intermediate results exceed N entries. For exact (untruncated) arrays, distributivity holds. The truncation approximation is acceptable for the bounded-best semantics |

### 7c. Non-Exact Distributivity Note

The N-best semiring is technically a **truncated** semiring. Full distributivity
requires unlimited capacity. With truncation:

```
a ⊗  (b ⊕  c):  b ⊕  c may discard entries, then a ⊗  (truncated) misses some products
(a ⊗  b) ⊕  (a ⊗  c):  products computed first (more entries), then merge truncates
```

These may disagree when the intermediate sets exceed N. In practice, N is chosen
large enough to capture the alternatives of interest, and the truncation error
is bounded. This is the standard trade-off in N-best WFST algorithms (see
Mohri & Riley, "An Efficient Algorithm for the N-Best-Strings Problem").

---

## 8. Ordering

NbestWeight implements `Ord` with best-entry-first comparison
(`semiring.rs:1647-1658`):

```rust
impl<const N: usize> Ord for NbestWeight<N> {
    fn cmp(&self, other: &Self) -> Ordering {
        match (self.best(), other.best()) {
            (None, None) => Ordering::Equal,
            (None, Some(_)) => Ordering::Greater,  // empty = worst
            (Some(_), None) => Ordering::Less,
            (Some(a), Some(b)) => a.weight.cmp(&b.weight)
                .then_with(|| self.len.cmp(&other.len)),
        }
    }
}
```

**Level 1: Best entry weight**. Lower best weight = smaller (better) N-best
weight. This is consistent with TropicalWeight ordering.

**Level 2: Entry count** (tiebreaker). Among two N-best weights with the same
best weight, the one with fewer entries is "smaller." This favors simpler
derivations (fewer alternatives) when the best path cost is tied.

**Empty is worst**: An empty N-best weight (zero) compares as `Greater` than
any non-empty weight. This is the correct Viterbi convention: zero (no paths)
is the worst possible outcome, ensuring that any real path beats "unreachable."

```
 Ordering chain:
 [(1, 0.5)]  <  [(2, 1.0)]  <  [(3, 5.0)]  <  []
     ↑              ↑              ↑            ↑
 best=0.5       best=1.0       best=5.0      empty (worst)
```

**Viterbi compatibility**: Unlike CountingWeight (where `zero = 0` is smallest,
breaking Viterbi), NbestWeight's `zero = []` is the **largest** element under
`Ord`. This makes NbestWeight directly compatible with Viterbi shortest-path
extraction without needing a ProductWeight wrapper for ordering correctness.

---

## 9. Display Format

The `Display` implementation (`semiring.rs:1670-1682`) uses bracket notation
with `(path_id:weight)` pairs:

```rust
impl<const N: usize> fmt::Display for NbestWeight<N> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "[")?;
        for i in 0..self.len {
            if i > 0 { write!(f, ", ")?; }
            if let Some(e) = &self.entries[i] {
                write!(f, "({}:{:.1})", e.path_id, e.weight.value())?;
            }
        }
        write!(f, "]")
    }
}
```

| Value     | Output               | Meaning                                |
|-----------|----------------------|----------------------------------------|
| `zero()`  | `[]`                 | Empty list (no paths)                  |
| `one()`   | `[(0:0.0)]`          | Single zero-cost path                  |
| 2 entries | `[(1:2.5), (3:4.0)]` | Path 1 at cost 2.5, path 3 at cost 4.0 |

The format is intentionally compact for embedding in diagnostic messages and
debug output. Weights use one decimal place (`{:.1}`) for readability.

---

## 10. Use Cases

### 10a. Lazy Disambiguation

When the parser encounters an ambiguous dispatch token with N > 1 competing
rules, NbestWeight enables a **try-best-first** strategy:

```
 Token: Ident("x")
 Alternatives: [(rule PInput, w=0.5), (rule POutput, w=1.0)]

 Step 1: Try best (PInput, w=0.5)
   → parse succeeds → done

 Step 1: Try best (PInput, w=0.5)
   → parse fails (type error downstream)
 Step 2: Try second-best (POutput, w=1.0)
   → parse succeeds → done
```

This avoids the cost of NFA spillover (forced-prefix replay) for cases where the
best alternative is almost always correct. The fallback to the second-best is
invoked only on failure, amortizing the cost of disambiguation over many parse
decisions.

### 10b. Confidence Scoring

The `confidence_gap()` method measures how decisively the best parse won:

```
 gap = w₂ - w₁ (second-best weight minus best weight)

 Large gap (e.g., 5.0):  high confidence → commit immediately
 Small gap (e.g., 0.1):  near-tie → may need NFA spillover for certainty
 Infinite gap:           only one candidate → maximum confidence
```

This enables an adaptive disambiguation strategy: use beam pruning aggressively
when confidence is high, fall back to exhaustive NFA analysis when confidence
is low.

### 10c. Parse Forest Construction

With N = 4 or higher, NbestWeight carries a compact parse forest:

```
 NbestWeight<4> for "x + y":
   [(path 1, w=0.5),  — ProcExpr reading: process expression
    (path 2, w=1.0),  — NameExpr reading: name expression
    (path 3, w=2.0),  — IntExpr reading: integer addition
    (path 4, w=3.5)]  — StringConcat reading: string concatenation
```

Downstream passes can enumerate these alternatives for semantic analysis,
type-directed disambiguation, or error reporting that shows the user "did you
mean...?" suggestions.

---

## 11. NbestWeight\<2\>: Binary Confidence Decisions

The specialization `NbestWeight<2>` is optimized for the most common use case:
binary confidence decisions.

### 11a. Memory Layout

```
 NbestWeight<2> — 28 bytes on stack
 ┌─────────────────────────────────────┐
 │ entries[0]      entries[1]      len │
 │ ┌─────────────┐ ┌─────────────┐     │
 │ │ path_id: u32│ │ path_id: u32│     │
 │ │ weight:  f64│ │ weight:  f64│  2  │
 │ └─────────────┘ └─────────────┘     │
 └─────────────────────────────────────┘
```

With `Option<NbestEntry>` (12 bytes per entry with padding) + `len` (8 bytes),
the total is small enough to pass by value in registers on x86-64.

### 11b. Decision Logic

```rust
type ConfidenceWeight = NbestWeight<2>;

let w: ConfidenceWeight = /* from WFST dispatch */;

match w.len() {
    0 => unreachable!("no parse path"),
    1 => {
        // Only one candidate: commit immediately
        parse_with(w.best().expect("single entry"));
    }
    2 => {
        if w.confidence_gap() > THRESHOLD {
            // Clear winner: commit to best
            parse_with(w.best().expect("best entry"));
        } else {
            // Near-tie: invoke NFA spillover for exact disambiguation
            nfa_disambiguate(w.iter());
        }
    }
    _ => unreachable!("N=2 bounds this"),
}
```

The `THRESHOLD` is grammar-dependent. For grammars where rule priorities are
well-separated (e.g., rhocalc where priority gaps are >= 1.0), a threshold of
0.5 is sufficient. For grammars with fine-grained priorities, a lower threshold
may be needed.

### 11c. Tested Behavior

The `test_nbest_n2_confidence` test (`semiring.rs:2844-2855`) verifies that
`NbestWeight<2>` correctly:

- Retains only the top 2 entries when given 3 alternatives
- Reports `confidence_gap() = 0.5` for entries at weights 0.5 and 1.0
- Identifies the correct best path (`path_id = 1`, weight 0.5)

---

## 12. Test Coverage

Fifteen tests in `semiring.rs:2641-2864` cover NbestWeight:

| Test                             | Lines     | What It Verifies                                                                                                       |
|----------------------------------|-----------|------------------------------------------------------------------------------------------------------------------------|
| `test_nbest_semiring_laws`       | 2645-2668 | Zero identity (0̄ ⊕  a = a), plus commutativity, one identity (1̄ ⊗  a preserves weight), zero annihilation (0̄ ⊗  a = 0̄) |
| `test_nbest_merge_keeps_top_n`   | 2672-2688 | Merging 4 entries with N=3 retains only the 3 lowest-weight entries; verifies best is path 4 (w=0.5)                   |
| `test_nbest_merge_deduplicates`  | 2692-2703 | Same `path_id` with different weights: keeps the lower weight (2.0), discards the higher (5.0)                         |
| `test_nbest_cross_product`       | 2707-2717 | Single x single: weight addition (1.0 + 3.0 = 4.0), single result entry                                                |
| `test_nbest_cross_product_multi` | 2721-2737 | 2x2 cross-product: up to 4 candidates, best is the pair with minimum combined weight (1.0 + 0.5 = 1.5)                 |
| `test_nbest_empty_operations`    | 2741-2747 | Zero element: `is_zero()`, `is_empty()`, `len() == 0`, `best().is_none()`                                              |
| `test_nbest_one`                 | 2751-2760 | One element: `is_one()`, `len() == 1`, `path_id == 0`, `weight == TropicalWeight::one()`                               |
| `test_nbest_confidence_gap`      | 2764-2777 | Gap = 4.0 for entries at 1.0 and 5.0; gap = infinity for single entry; gap = infinity for empty                        |
| `test_nbest_ordering`            | 2781-2788 | `(w=1.0) < (w=5.0) < empty`; lower best weight is better; empty is worst                                               |
| `test_nbest_display`             | 2792-2802 | `"[]"` for zero, `"[(0:0.0)]"` for one, `"[(1:2.5), (3:4.0)]"` for two entries                                         |
| `test_nbest_hash`                | 2806-2812 | `HashSet` insertion and lookup: same (path_id, weight) matches; different path_id does not                             |
| `test_nbest_from_entries`        | 2816-2828 | 4 unsorted entries with N=3: sorts by weight, truncates to 3, correct best/2nd/3rd ordering                            |
| `test_nbest_iter`                | 2832-2840 | `iter()` returns entries in weight-ascending order; correct count and first element                                    |
| `test_nbest_n2_confidence`       | 2844-2854 | `NbestWeight<2>` with 3 inputs: retains top 2, correct best path_id and confidence gap (0.5)                           |
| `test_nbest_approx_eq`           | 2858-2863 | `approx_eq` with epsilon: matches within 1e-10 tolerance, does not match within 1e-15                                  |

---

## 13. Source Reference & See Also

- **NbestEntry struct**: `semiring.rs:1373-1391`
- **NbestWeight struct**: `semiring.rs:1417-1424`
- **Constructors (empty, singleton, from_entries)**: `semiring.rs:1426-1453`
- **Accessors (len, is_empty, get, best, confidence_gap, iter)**: `semiring.rs:1455-1497`
- **merge_nbest (plus)**: `semiring.rs:1501-1543`
- **concat_nbest (times)**: `semiring.rs:1547-1566`
- **Semiring impl**: `semiring.rs:1569-1622`
- **PartialEq / Eq impl**: `semiring.rs:1624-1638`
- **Ord impl**: `semiring.rs:1640-1658`
- **Hash impl**: `semiring.rs:1661-1668`
- **Display impl**: `semiring.rs:1670-1682`
- **Default impl**: `semiring.rs:1685-1689`
- **Tests (15 NbestWeight)**: `semiring.rs:2641-2864`
- **Semiring trait definition**: `semiring.rs:28-51`
- **TropicalWeight (base weight type)**: `semiring.rs:57-69`
- **Tropical semiring doc**: `tropical-weight.md`
- **Product semiring doc**: `product-weight.md` -- generic composition framework
- **Context semiring doc**: `context-weight.md` -- bitset-based rule tracking (complementary approach)
- **Counting semiring doc**: `counting-weight.md` -- cardinality-only alternative counting
- **Theory**: `prattail/docs/theory/wfst/semirings.md`
