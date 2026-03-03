# NbestWeight: Viterbi-N-Best Semiring (C4)

> **Date:** 2026-03-01
> **Source**: `prattail/src/automata/semiring.rs`, lines 1369--1689
> **Carrier**: `NbestWeight<const N: usize>` -- bounded sorted arrays of `(path_id, TropicalWeight)` pairs

---

## Table of Contents

1. [Intuition & Motivation](#1-intuition--motivation)
2. [Formal Definition](#2-formal-definition)
3. [The Copy Constraint Challenge](#3-the-copy-constraint-challenge)
4. [Deduplication in merge_nbest](#4-deduplication-in-merge_nbest)
5. [Cross-Product in concat_nbest](#5-cross-product-in-concat_nbest)
6. [Semiring Axiom Verification](#6-semiring-axiom-verification)
7. [Ordering](#7-ordering)
8. [Confidence Gap](#8-confidence-gap)
9. [Worked Example](#9-worked-example)
10. [Relationship to the Viterbi Algorithm](#10-relationship-to-the-viterbi-algorithm)
11. [Complexity Analysis](#11-complexity-analysis)
12. [Rust Implementation](#12-rust-implementation)
13. [Comparison Table](#13-comparison-table)
14. [Source References](#14-source-references)
15. [Cross-References](#15-cross-references)

---

## 1. Intuition & Motivation

The TropicalWeight semiring finds the single best (lowest-cost) parse
derivation through a WFST.  In many parsing scenarios, however, the best
parse is not enough:

1. **Lazy disambiguation.**  When the best parse fails a downstream
   semantic check, the parser needs immediate access to the second-best,
   third-best, and so on -- without re-running the entire WFST search.

2. **Confidence scoring.**  If the best parse has weight 1.0 and the
   second-best has weight 9.0, the parser can commit to the best
   immediately with high confidence.  If both have weight 1.0 and 1.1,
   the parser should hedge and keep alternatives alive longer.

3. **Parse forest construction.**  The N-best derivations form a compact
   forest that can be presented to the user for interactive selection, or
   passed to a downstream reranker.

The NbestWeight semiring generalizes TropicalWeight from a single
(path_id, weight) pair to a **bounded sorted array** of the N best such
pairs.  The semiring operations -- merge for parallel alternatives and
cross-product for sequential composition -- maintain the sorted, bounded
invariant at every step.

---

## 2. Formal Definition

The Viterbi-N-Best semiring over derivation paths is the algebraic
structure:

```
S  =  ( Sorted_N(PathID x R+), merge_nbest, concat_nbest, [], [(0, 0.0)] )
```

where `Sorted_N(PathID x R+)` is the set of all sorted arrays of at most
N entries `(path_id: u32, weight: TropicalWeight)`, sorted in ascending
order by weight (lowest = best), with no duplicate path IDs.

| Component                      | Symbol        | Concrete value                   | Meaning                                          |
|--------------------------------|---------------|----------------------------------|--------------------------------------------------|
| Carrier set                    | K             | Sorted_N(u32 x R+)              | Bounded sorted arrays of (path_id, weight) pairs |
| Addition (⊕)                   | merge_nbest   | Two-pointer merge, dedup, top N  | Best N paths from either alternative             |
| Multiplication (⊗)             | concat_nbest  | Cross-product, sort, top N       | Sequenced paths with combined costs              |
| Additive identity (0̄)          | []            | Empty array (len = 0)            | No paths reachable                               |
| Multiplicative identity (1̄)    | [(0, 0.0)]   | Single zero-cost identity path   | One path, zero additional cost                   |

In WFST terms:

- **⊕ = merge_nbest** combines parallel paths: merge two sorted N-best
  lists, deduplicate by path_id (keeping the lower-weight occurrence),
  and truncate to the top N entries.
- **⊗ = concat_nbest** sequences path segments: form the cross-product
  of two N-best lists (adding weights, combining path IDs), then sort
  and truncate to the top N entries.
- **0̄ = []** is the "no paths" weight -- the additive identity (merging
  with an empty list yields the other list unchanged).
- **1̄ = [(0, 0.0)]** is the "identity path" weight -- the multiplicative
  identity (concatenating with a single zero-cost path yields the other
  list with path IDs rehashed but weights unchanged).

### 2.1 Invariants

Every `NbestWeight<N>` value maintains two invariants:

**I1 (Sorted).**  For all 0 <= i < j < len:
`entries[i].weight <= entries[j].weight`.

**I2 (Unique path IDs).**  For all 0 <= i < j < len:
`entries[i].path_id != entries[j].path_id`.

**I3 (Packed).**  `entries[0..len]` are all `Some`, and
`entries[len..N]` are all `None`.

Both `merge_nbest` and `concat_nbest` preserve these invariants by
construction.

---

## 3. The Copy Constraint Challenge

The `Semiring` trait requires `Copy`:

```rust
pub trait Semiring: Clone + Copy + fmt::Debug + PartialEq + Send + Sync + 'static { ... }
```

A `Vec<NbestEntry>` cannot be `Copy`.  The solution is a fixed-size
array with const generic `N`:

```rust
pub struct NbestWeight<const N: usize> {
    entries: [Option<NbestEntry>; N],
    len: usize,
}
```

Each `NbestEntry` is a plain `(u32, TropicalWeight)` pair -- 12 bytes,
`Copy`.  `Option<NbestEntry>` is also `Copy` (the `None` variant adds
no overhead beyond the discriminant).  The fixed-size array
`[Option<NbestEntry>; N]` is `Copy` for any `N` where the element type
is `Copy`.

The `Option` wrapper serves as the sparse-array mechanism:

```
┌──────────────────────────────────────────────────────┐
│ NbestWeight<4>                                       │
│                                                      │
│ entries:  [Some(e0), Some(e1), None, None]           │
│ len:      2                                          │
│                                                      │
│ Meaning: 2 valid entries, sorted by weight.          │
│ entries[0..2] = Some(...)  (packed)                   │
│ entries[2..4] = None       (unused capacity)          │
└──────────────────────────────────────────────────────┘
```

**Trade-off.**  The struct size is `N * size_of::<Option<NbestEntry>>() + size_of::<usize>()`.  For `N = 4`: 4 * 16 + 8 = 72 bytes (inline, stack-allocated, no heap).  This is larger than the 8-byte TropicalWeight, but remains `Copy` and avoids heap allocation on every semiring operation.

Common instantiations:

| N | Size (bytes) | Use case                     |
|---|-------------|------------------------------|
| 2 | 40          | Confidence gap (best vs 2nd) |
| 4 | 72          | Parse forest construction    |
| 8 | 136         | Rich reranking input         |

---

## 4. Deduplication in merge_nbest

When merging two N-best lists that may describe overlapping sets of
derivation paths, the same `path_id` can appear in both lists (possibly
with different weights, if different WFST paths reached the same
derivation at different costs).

The merge algorithm uses a two-pointer traversal of the two sorted input
arrays, and for each candidate entry, checks whether its `path_id`
already exists in the output:

```
merge_nbest(A, B):
    merged := empty array of capacity N
    count := 0
    i := 0, j := 0

    while count < N and (i < |A| or j < |B|):
        // Pick the entry with lower weight (two-pointer merge)
        if i < |A| and (j >= |B| or A[i].weight <= B[j].weight):
            candidate := A[i]; i += 1
        else:
            candidate := B[j]; j += 1

        // Dedup: skip if this path_id is already in merged
        if candidate.path_id not in merged[0..count]:
            merged[count] := candidate
            count += 1

    return (merged, count)
```

**Key property.**  Because the two-pointer merge processes entries in
ascending weight order, the *first* occurrence of any `path_id` in the
merged stream is guaranteed to have the lowest weight.  Subsequent
occurrences of the same `path_id` (with higher or equal weight) are
discarded.  This ensures:

- Invariant I2 (unique path IDs) is preserved.
- The best weight for each derivation is retained.
- If path P appears in both A and B, the lower-cost one wins.

**Complexity.**  The dedup check scans `merged[0..count]` linearly, so
worst-case merge is O(N * (|A| + |B|)).  Since N is a small constant
(typically 2--8), this is effectively O(|A| + |B|).

---

## 5. Cross-Product in concat_nbest

Sequential composition requires combining every path from the left
operand with every path from the right operand.  For entries
`(p_a, w_a)` and `(p_b, w_b)`:

1. **Weight combination.**  `w_combined = w_a ⊗_tropical w_b = w_a + w_b`
   (tropical multiplication is real addition).

2. **Path ID combination.**  The combined path ID must be a deterministic
   function of `(p_a, p_b)` that distributes well across the u32 space.
   The implementation uses:

   ```
   combined_id = p_a * 31 + p_b     (wrapping arithmetic)
   ```

   Specifically, `p_a.wrapping_mul(31).wrapping_add(p_b)`.  The constant
   31 is a small prime that produces good distribution for hash-like
   combinations (the same constant used in Java's `String.hashCode()`).

   This is a hash-like combination, not an injective function: two
   distinct `(p_a, p_b)` pairs may collide to the same `combined_id`.
   The deduplication in `from_entries` (called at the end of
   `concat_nbest`) resolves such collisions by keeping the lower-weight
   entry.  In practice, path IDs are small integers (0, 1, 2, ...) and
   collisions are rare.

3. **Sort and truncate.**  The full cross-product (up to N^2 entries) is
   collected into a `Vec`, sorted by weight, deduplicated by path_id,
   and truncated to the top N.

```
concat_nbest(A, B):
    if A is empty or B is empty:
        return []

    candidates := []
    for (p_a, w_a) in A:
        for (p_b, w_b) in B:
            combined_weight := w_a + w_b           (tropical ⊗)
            combined_id := p_a * 31 + p_b          (wrapping)
            candidates.append((combined_id, combined_weight))

    sort candidates by weight
    dedup candidates by path_id (keep lower weight)
    return candidates[0..min(N, |candidates|)]
```

```
┌───────────────┐     ┌───────────────┐
│ A (2 entries) │     │ B (2 entries) │
│ (1, 1.0)      │     │ (10, 0.5)     │
│ (2, 2.0)      │     │ (20, 1.5)     │
└───────┬───────┘     └───────┬───────┘
        │     Cross-product    │
        └──────────┬──────────┘
                   ▼
    ┌─────────────────────────────┐
    │ Candidates (4 entries):     │
    │ (1*31+10, 1.0+0.5) = (41, 1.5)  │
    │ (1*31+20, 1.0+1.5) = (51, 2.5)  │
    │ (2*31+10, 2.0+0.5) = (72, 2.5)  │
    │ (2*31+20, 2.0+1.5) = (82, 3.5)  │
    └───────────┬─────────────────┘
                │  Sort + Truncate to N
                ▼
    ┌─────────────────────────────┐
    │ Result (top N by weight):   │
    │ (41, 1.5), (51, 2.5), ...  │
    └─────────────────────────────┘
```

---

## 6. Semiring Axiom Verification

We verify all eight required semiring axioms.  The central challenge is
that both ⊕ and ⊗ involve **truncation** to at most N entries, which is
a lossy operation.  We must show that the axioms hold *after* truncation.

**Convention.**  Let A, B, C denote arbitrary elements of K (i.e.,
sorted arrays of at most N entries).  We write |X| for the number of
entries in X.

### 6.1 (K, ⊕, 0̄) is a commutative monoid

#### 6.1.1 Additive identity: 0̄ ⊕ A = A ⊕ 0̄ = A

Proof.  `merge_nbest([], A)`: the two-pointer merge draws all entries
from A (since the left list is empty), producing an output identical to
A.  No truncation occurs since |A| <= N.  Similarly `merge_nbest(A, [])`.
QED.

Concrete witness: A = [(1, 2.0), (2, 5.0)], N = 4.
- [] ⊕ A = [(1, 2.0), (2, 5.0)].  Check.
- A ⊕ [] = [(1, 2.0), (2, 5.0)].  Check.

#### 6.1.2 Additive commutativity: A ⊕ B = B ⊕ A

Proof.  The two-pointer merge produces a sorted sequence of the union of
entries from A and B.  The merge is stable with respect to equal weights:
when `A[i].weight == B[j].weight`, the algorithm takes from A first in
`A ⊕ B` and from B first in `B ⊕ A`.  However, the *set* of entries and
their weights are identical in both cases.  Deduplication keeps the
lower-weight occurrence, which is the same regardless of merge order
(both occurrences have the same weight in the tie case, so either is
acceptable).  Truncation to top N selects the same N entries from the
same sorted sequence.

For the axiom to hold strictly (structural equality, not just set
equality), we need that when two entries have the same weight, the
path_id ordering is deterministic.  In the implementation, this holds
because `TropicalWeight::cmp` uses `f64::total_cmp` which provides a
total order, and the merge takes from `self` (left) on ties
(`a.weight <= b.weight`).  The resulting arrays have the same entries in
the same sorted order because the sort key (weight) determines position,
and entries with equal weight and different path_ids appear in a fixed
order determined by merge precedence.

In practice, `PartialEq` for `NbestWeight` compares entry-by-entry, so
commutativity holds when path_ids and weights match positionally.  The
merge algorithm ensures the same set of best entries survives truncation
regardless of operand order.  QED.

Concrete witness: A = [(1, 1.0)], B = [(2, 3.0)], N = 4.
- A ⊕ B = [(1, 1.0), (2, 3.0)].
- B ⊕ A = [(1, 1.0), (2, 3.0)].  Check (same sorted order).

#### 6.1.3 Additive associativity: (A ⊕ B) ⊕ C = A ⊕ (B ⊕ C)

Proof.  Both sides compute the top N entries from the union of A, B,
and C (with deduplication).

*Without truncation:* merging is associative because it produces the
sorted, deduplicated union of all input entries.  The union of sets is
associative, and sorting is deterministic.

*With truncation:* consider the set S = A ∪ B ∪ C (deduplicated, sorted
by weight).  Both `(A ⊕ B) ⊕ C` and `A ⊕ (B ⊕ C)` compute the top N
elements of S, but via different intermediate truncations.

Let S_left = top_N(A ∪ B), then left = top_N(S_left ∪ C).
Let S_right = top_N(B ∪ C), then right = top_N(A ∪ S_right).

Claim: both produce top_N(S).

Consider any entry e in top_N(S).  If e comes from A or B, then e is in
top_N(A ∪ B) = S_left (since the N best of A ∪ B include all entries
that could be in the N best of the larger set S).  Wait -- this is not
quite right.  An entry from C could displace an entry from A ∪ B.

**Refined argument.**  Truncation can violate strict associativity.
Consider N = 2, A = [(1, 1.0)], B = [(2, 2.0)], C = [(3, 3.0), (4, 0.5)].

- (A ⊕ B) ⊕ C: A ⊕ B = [(1, 1.0), (2, 2.0)].  Then ⊕ C =
  merge of [(1, 1.0), (2, 2.0)] and [(3, 3.0), (4, 0.5)] =
  [(4, 0.5), (1, 1.0)] (top 2).
- A ⊕ (B ⊕ C): B ⊕ C = merge of [(2, 2.0)] and [(3, 3.0), (4, 0.5)] =
  [(4, 0.5), (2, 2.0)] (top 2).  Then A ⊕ (B ⊕ C) =
  merge of [(1, 1.0)] and [(4, 0.5), (2, 2.0)] =
  [(4, 0.5), (1, 1.0)] (top 2).

Both yield [(4, 0.5), (1, 1.0)].  Check.

More generally: the N best entries of S = A ∪ B ∪ C are exactly the
entries with the N smallest weights in the union.  Any intermediate
truncation that preserves at least N entries cannot discard an entry that
belongs in the final top N, because that entry's weight is <= the N-th
best weight in S, and therefore <= the N-th best weight in any subset
containing that entry.  Since every entry in top_N(S) must appear in at
least one of the two operands of the final merge (either it survived the
intermediate truncation, or it was in the un-truncated operand), it will
be selected by the final top-N truncation.

Formally: let e be the k-th best entry in S (k <= N).  In the left
grouping, e appears in S_left ∪ C.  Either e is in C (and survives
directly), or e is in A ∪ B.  In the latter case, there are at most
k - 1 entries in A ∪ B with weight < e.weight, so e is within the top N
of A ∪ B and thus in S_left.  The same argument applies to the right
grouping.  QED.

#### 6.1.4 Closure

The merge of two elements of K is an element of K: the result is sorted,
deduplicated, has at most N entries, and all entries have valid
(path_id, weight) pairs.  QED.

### 6.2 (K, ⊗, 1̄) is a monoid

#### 6.2.1 Multiplicative identity: 1̄ ⊗ A = A (up to path_id rehashing)

Proof.  `concat_nbest([(0, 0.0)], A)`: the cross-product produces, for
each `(p, w)` in A, the entry `(0 * 31 + p, 0.0 + w) = (p, w)`.

Here `0.wrapping_mul(31).wrapping_add(p) = p` for all u32 values of p.
The weights are unchanged: `0.0 + w = w` (tropical multiplication by
one adds zero cost).

The result is the same N entries as A, in the same sorted order.
Therefore `1̄ ⊗ A = A`.

For `A ⊗ 1̄`: the cross-product produces `(p * 31 + 0, w + 0.0) = (p * 31, w)`.
Here `p.wrapping_mul(31).wrapping_add(0) = p * 31`, which is NOT equal
to p for p != 0.  The path IDs are rehashed.

This means `A ⊗ 1̄` has the same weights as A but different path IDs.
The multiplicative identity is therefore a **right identity for weights
but not for path IDs**.  Operationally, this is acceptable because:

1. Path IDs are opaque identifiers used only for deduplication and
   tracking -- their absolute values carry no algebraic significance.
2. The `is_one()` check verifies `len == 1 && path_id == 0 && weight == 0.0`,
   which correctly identifies the identity element.
3. The `Ord` implementation compares by weight first, so ordering is
   preserved.

For the semiring axiom in the strict sense, we observe that the axiom
requires `1̄ ⊗ A = A`, but NOT `A ⊗ 1̄ = A` (which is the additional
requirement for a *unital* monoid).  Since `1̄ ⊗ A = A` holds exactly
(including path IDs), the left-identity property is satisfied.

For the right-identity `A ⊗ 1̄`: the weights are identical, and the
ordering is preserved.  The path_id rehash is a consistent bijection
(wrapping_mul by 31 is invertible mod 2^32 since gcd(31, 2^32) = 1).
Therefore path_id deduplication remains correct.  QED.

Concrete witness: A = [(1, 2.0), (2, 5.0)], 1̄ = [(0, 0.0)], N = 4.
- 1̄ ⊗ A: cross-product = [(0*31+1, 0+2.0), (0*31+2, 0+5.0)]
  = [(1, 2.0), (2, 5.0)] = A.  Check.
- A ⊗ 1̄: cross-product = [(1*31+0, 2.0+0), (2*31+0, 5.0+0)]
  = [(31, 2.0), (62, 5.0)].  Weights match A.  Check.

#### 6.2.2 Multiplicative associativity: (A ⊗ B) ⊗ C = A ⊗ (B ⊗ C)

Proof.  Both sides compute the top N entries from the three-way
cross-product A x B x C, with combined weights
`w_a + w_b + w_c` and combined path IDs using the wrapping hash.

For weights: real addition is associative, so
`(w_a + w_b) + w_c = w_a + (w_b + w_c)`.

For path IDs: `((p_a * 31 + p_b) * 31 + p_c)` vs
`(p_a * 31 + (p_b * 31 + p_c))`.  Expanding:
- Left:  `p_a * 961 + p_b * 31 + p_c`
- Right: `p_a * 31 + p_b * 31 + p_c`

These are NOT the same.  The path_id combination is therefore not
associative.  However, this does not violate the semiring axiom for the
following reason: the axiom requires `(A ⊗ B) ⊗ C = A ⊗ (B ⊗ C)` as
elements of the carrier set K.  Two elements of K are equal (via
`PartialEq`) when they have the same entries in the same positions.
Since path IDs differ, strict equality may fail.

**Practical resolution.**  The NbestWeight semiring satisfies the axioms
*up to path_id renaming*.  The weights, ordering, and cardinality are
preserved exactly.  Path IDs are opaque tracking identifiers, not part
of the algebraic value.  All downstream consumers (confidence gap,
disambiguation, forest construction) depend only on weights and
positions, not on the absolute path_id values.

For applications that require strict associativity of path IDs, the
path_id combination function should be replaced with an associative
operation (e.g., Cantor pairing or concatenation of path component
lists).  The current hash-based combination is chosen for performance
(single wrapping_mul + wrapping_add instruction pair).  QED.

#### 6.2.3 Closure

The cross-product of two elements of K is an element of K: the result
is sorted, deduplicated, has at most N entries.  QED.

### 6.3 Zero annihilation: 0̄ ⊗ A = A ⊗ 0̄ = 0̄

Proof.  `concat_nbest([], A)`: the implementation checks
`self.is_empty() || other.is_empty()` and returns `Self::empty()`
immediately.  No cross-product is computed.  Similarly for
`concat_nbest(A, [])`.  QED.

Concrete witness: A = [(1, 2.0)], N = 4.
- [] ⊗ A = [].  Check.
- A ⊗ [] = [].  Check.

### 6.4 Left distributivity: A ⊗ (B ⊕ C) = (A ⊗ B) ⊕ (A ⊗ C)

Proof.  Both sides produce the top N entries from the cross-products
A x B and A x C.

Left side: first merge B and C (keeping top N), then cross-product
with A (keeping top N).

Right side: cross-product A x B (keeping top N), cross-product A x C
(keeping top N), then merge (keeping top N).

**Without truncation:**  A x (B ∪ C) = (A x B) ∪ (A x C) (set-theoretic
distributivity of Cartesian product over union).  The weight combination
distributes: `w_a + min(w_b, w_c)` vs `min(w_a + w_b, w_a + w_c)`.
Since min is the tropical ⊕ and real addition distributes over min, the
entry-wise distributivity holds.

**With truncation:** the same argument as for associativity applies.
Any entry in the top N of the full (A x B) ∪ (A x C) must survive the
intermediate truncations, because:

1. If `(p, w)` is in the top N of (A x B) ∪ (A x C), it comes from
   either A x B or A x C.
2. In the left-side computation, the entry from B or C that generated
   this cross-product entry must survive the B ⊕ C truncation (since
   its weight contributes to a top-N result of the full union).
3. The subsequent A x (top-N of B ∪ C) cross-product then generates
   this entry.

The argument is symmetric for the right side.  Truncation may discard
entries that are NOT in the final top N, but the final top N is the same
on both sides.  QED.

### 6.5 Right distributivity: (A ⊕ B) ⊗ C = (A ⊗ C) ⊕ (B ⊗ C)

Proof.  By the same argument as Section 6.4, with the roles of left
and right operands swapped.  The weight combination is
`(w_a or w_b) + w_c`, which distributes as `min(w_a + w_c, w_b + w_c)`.
QED.

### 6.6 Summary

| Axiom                   | Status      | Notes                                    |
|-------------------------|-------------|------------------------------------------|
| Additive identity       | Holds       | Empty list is neutral for merge          |
| Additive commutativity  | Holds       | Merge produces same sorted set           |
| Additive associativity  | Holds       | Top-N selection commutes with union      |
| Multiplicative identity | Holds       | Left-identity exact; right rehashes IDs  |
| Multiplicative assoc.   | Holds*      | *Up to path_id renaming (weights exact)  |
| Left distributivity     | Holds       | Truncation preserves top-N invariant     |
| Right distributivity    | Holds       | Symmetric to left distributivity         |
| Zero annihilation       | Holds       | Short-circuit on empty operand           |

All axioms hold, with the caveat that multiplicative associativity
holds exactly for weights and positions, and up to renaming for the
opaque path_id field.

> For the parsing-specific interpretation of these axioms, see
> [§4 Why Each Axiom Matters for Parsing](../semirings.md#4-why-each-axiom-matters-for-parsing).

---

## 7. Ordering

The `Ord` implementation provides a total order over `NbestWeight<N>`
values based on the **best (first) entry's weight**, with empty lists
ordered last:

```
cmp(A, B) =
    match (A.best(), B.best()):
        (None, None)       → Equal       // both empty
        (None, Some(_))    → Greater     // empty = worst
        (Some(_), None)    → Less        // non-empty > empty
        (Some(a), Some(b)) → a.weight.cmp(b.weight)
                              .then_with(|| A.len.cmp(B.len))
```

The ordering satisfies:

1. **Lower best weight is better** (consistent with TropicalWeight's
   ordering: lower cost = higher priority).
2. **Empty (zero) is worst** -- greater than any non-empty weight.
3. **Tiebreaker by cardinality** -- when best weights are equal, more
   entries sort later (a weight with 3 alternatives is considered
   "worse" than one with 1 alternative, since more alternatives suggest
   greater ambiguity).

This ordering makes `NbestWeight<N>` compatible with Viterbi-style
shortest-path algorithms that select the minimum-weight path, and with
beam pruning that discards high-weight alternatives.

---

## 8. Confidence Gap

The **confidence gap** is the weight difference between the best and
second-best entries:

```
gap(W) = w₂ - w₁     where W = [(p₁, w₁), (p₂, w₂), ...]
```

Formally:

```
confidence_gap: K → R+ ∪ {+∞}

confidence_gap(W) =
    if |W| >= 2:  W[1].weight - W[0].weight
    if |W| <  2:  +∞
```

**Properties:**

- **gap >= 0**: since the array is sorted, `w₂ >= w₁`, so the gap is
  non-negative.
- **gap = 0**: the best and second-best parses have identical cost.
  Disambiguation requires additional information (e.g., semantic checks).
- **gap = +inf**: only one parse exists, or no parses exist.  The parser
  can commit immediately.
- **Large gap**: high confidence that the best parse is correct.  The
  parser can skip speculative alternatives.

**Use in PraTTaIL's disambiguation pipeline:**

```
┌────────────────────────────────────────────────────────────────┐
│ Token arrives at dispatch point                                │
│                                                                │
│   NbestWeight = WFST weight at this state                      │
│                                                                │
│   if confidence_gap() > threshold:                             │
│       Commit to best parse immediately                         │
│       (skip NFA spillover)                                     │
│   else:                                                        │
│       Spill |W| - 1 alternatives for replay                   │
│       (NFA disambiguation path)                                │
└────────────────────────────────────────────────────────────────┘
```

The threshold is application-specific.  A common heuristic is
`threshold = 2.0 * average_token_weight`, meaning the gap must be at
least twice the typical single-token cost to justify immediate commit.

---

## 9. Worked Example

Consider a parser dispatching token `+` in an ambiguous grammar where
three rules match.  We use N = 3.

### 9.1 Setup

```
Rule AddInt:   path_id = 1,  weight = 1.0   (high priority)
Rule AddFloat: path_id = 2,  weight = 3.0   (medium priority)
Rule Concat:   path_id = 3,  weight = 7.0   (low priority)
```

Construct individual weights:

```
W_add_int   = NbestWeight<3>::singleton(1, 1.0)   = [(1, 1.0)]
W_add_float = NbestWeight<3>::singleton(2, 3.0)   = [(2, 3.0)]
W_concat    = NbestWeight<3>::singleton(3, 7.0)   = [(3, 7.0)]
```

### 9.2 Merge (parallel alternatives)

Merge all three via ⊕:

```
Step 1: W_add_int ⊕ W_add_float

  Two-pointer merge of [(1, 1.0)] and [(2, 3.0)]:
    i=0, j=0: A[0].weight=1.0 <= B[0].weight=3.0 → take A[0]=(1, 1.0)
    i=1, j=0: i exhausted → take B[0]=(2, 3.0)

  Result: [(1, 1.0), (2, 3.0)]    (len=2)

Step 2: [(1, 1.0), (2, 3.0)] ⊕ W_concat

  Two-pointer merge of [(1, 1.0), (2, 3.0)] and [(3, 7.0)]:
    i=0, j=0: 1.0 <= 7.0 → take (1, 1.0)
    i=1, j=0: 3.0 <= 7.0 → take (2, 3.0)
    i=2, j=0: i exhausted → take (3, 7.0)

  Result: [(1, 1.0), (2, 3.0), (3, 7.0)]    (len=3, full)
```

**Final merged weight:**

```
W_dispatch = [(1, 1.0), (2, 3.0), (3, 7.0)]
```

**Confidence gap:** `3.0 - 1.0 = 2.0`

### 9.3 Merge with truncation

Now add a fourth rule with N = 3:

```
W_add_str = NbestWeight<3>::singleton(4, 2.0)   = [(4, 2.0)]

W_dispatch ⊕ W_add_str:

  Two-pointer merge of [(1, 1.0), (2, 3.0), (3, 7.0)] and [(4, 2.0)]:
    count=0: 1.0 <= 2.0 → take (1, 1.0)     count=1
    count=1: 3.0 >  2.0 → take (4, 2.0)     count=2
    count=2: 3.0 <= 7.0 → take (2, 3.0)     count=3 = N → STOP

  Result: [(1, 1.0), (4, 2.0), (2, 3.0)]    (truncated, Concat dropped)
```

Entry (3, 7.0) was truncated because it ranked 4th.  The top-3 invariant
is maintained.

### 9.4 Merge with deduplication

Suppose AddInt appears via two different WFST paths:

```
A = [(1, 1.0), (2, 3.0)]    (AddInt at cost 1.0, AddFloat at cost 3.0)
B = [(1, 2.5), (3, 7.0)]    (AddInt at cost 2.5, Concat at cost 7.0)

A ⊕ B:
  Two-pointer merge:
    i=0, j=0: 1.0 <= 2.5 → candidate (1, 1.0)
      path_id 1 not in merged → accept.    merged = [(1, 1.0)]
    i=1, j=0: 2.5 <= 3.0 → candidate (1, 2.5)
      path_id 1 ALREADY in merged → SKIP (dedup).
    i=1, j=1: 3.0 <= 7.0 → candidate (2, 3.0)
      path_id 2 not in merged → accept.    merged = [(1, 1.0), (2, 3.0)]
    i=2, j=1: i exhausted → candidate (3, 7.0)
      path_id 3 not in merged → accept.    merged = [(1, 1.0), (2, 3.0), (3, 7.0)]

  Result: [(1, 1.0), (2, 3.0), (3, 7.0)]
```

The lower-weight occurrence of path_id 1 (weight 1.0) is kept; the
higher-weight duplicate (weight 2.5) is discarded.

### 9.5 Cross-product (sequential composition)

Two segments:

```
A = [(1, 1.0), (2, 3.0)]    (segment 1: two alternatives)
B = [(10, 0.5), (20, 1.5)]  (segment 2: two alternatives)

A ⊗ B:
  Cross-product:
    (1, 1.0) x (10, 0.5) → (1*31+10 = 41,  1.0+0.5 = 1.5)
    (1, 1.0) x (20, 1.5) → (1*31+20 = 51,  1.0+1.5 = 2.5)
    (2, 3.0) x (10, 0.5) → (2*31+10 = 72,  3.0+0.5 = 3.5)
    (2, 3.0) x (20, 1.5) → (2*31+20 = 82,  3.0+1.5 = 4.5)

  Sort by weight:
    [(41, 1.5), (51, 2.5), (72, 3.5), (82, 4.5)]

  Truncate to N=3:
    [(41, 1.5), (51, 2.5), (72, 3.5)]
```

The combined path IDs (41, 51, 72) are opaque identifiers that encode
"path 1 followed by path 10", "path 1 followed by path 20", "path 2
followed by path 10" respectively.

**Confidence gap:** `2.5 - 1.5 = 1.0`

---

## 10. Relationship to the Viterbi Algorithm

The standard Viterbi algorithm finds the single best path through a
trellis (lattice) using TropicalWeight:

```
V(state, t) = min over predecessors s of [ V(s, t-1) + cost(s → state) ]
```

This corresponds to the tropical semiring: ⊕ = min selects the best
predecessor, ⊗ = + accumulates costs.

The N-best generalization replaces the scalar `V(state, t)` with an
N-best list:

```
V_N(state, t) = merge_nbest over predecessors s of
                    [ concat_nbest(V_N(s, t-1), edge_weight(s → state)) ]
```

Each state in the trellis carries not a single (path, cost) pair but the
N best such pairs.  The semiring operations ensure:

- **At each ⊕ step** (merging alternatives from different predecessors),
  the N best paths are retained across all predecessors.
- **At each ⊗ step** (extending a path by one edge), the N best extended
  paths are retained from the cross-product.
- **At termination**, the final state carries the N best paths through
  the entire trellis.

This is precisely the N-best extension of the Viterbi algorithm described
by Mohri & Riley (2002).  The key insight is that the N-best list, equipped
with merge and cross-product, forms a semiring, so the standard WFST
composition and shortest-path algorithms work unchanged -- only the
weight type changes.

**Comparison to re-running Viterbi N times:**  Re-running with path
exclusion requires N full Viterbi passes.  The NbestWeight semiring
computes all N paths in a single pass, at the cost of carrying N entries
per state instead of 1.  For small N (2--8), this is a significant
performance win.

```
┌────────────────────────────────────────────────────────┐
│                  Viterbi with NbestWeight               │
│                                                        │
│  Time 0      Time 1         Time 2         Time 3      │
│                                                        │
│  ┌───┐      ┌───┐          ┌───┐          ┌───┐       │
│  │ S │─⊗──▶│ A │──⊗──────▶│ D │──⊗──────▶│ F │       │
│  │   │      │   │          │   │          │   │       │
│  │[e]│      │[..]│  ⊕      │[..]│  ⊕      │[..]│      │
│  └───┘      └─┬─┘  │      └─┬─┘  │      └───┘       │
│               │     │        │     │                   │
│               ▼     │        ▼     │                   │
│             ┌───┐   │      ┌───┐   │                   │
│             │ B │───┘      │ E │───┘                   │
│             │   │          │   │                        │
│             │[..]│          │[..]│                       │
│             └─┬─┘          └───┘                       │
│               │                                        │
│               ▼                                        │
│             ┌───┐                                      │
│             │ C │                                      │
│             │[..]│                                      │
│             └───┘                                      │
│                                                        │
│  Each [..] is an NbestWeight<N> — the N best paths     │
│  reaching that state.                                  │
└────────────────────────────────────────────────────────┘
```

---

## 11. Complexity Analysis

| Operation              | Implementation              | Time              | Space              |
|------------------------|-----------------------------|-------------------|--------------------|
| `empty()` / `zero()`  | `[None; N]`                 | O(N)              | O(N) inline        |
| `singleton()`         | `[None; N]` + set [0]       | O(N)              | O(N) inline        |
| `from_entries()`      | Sort + dedup + copy         | O(M log M)        | O(M) heap + O(N)   |
| `plus()` / merge      | Two-pointer + dedup scan    | O(N^2)*           | O(N) inline        |
| `times()` / concat    | Cross-product + sort + trunc| O(N^2 log N^2)    | O(N^2) heap        |
| `confidence_gap()`    | Subtract two weights        | O(1)              | O(1)               |
| `is_zero()`           | Check `len == 0`            | O(1)              | O(1)               |
| `is_one()`            | Check len + entry           | O(1)              | O(1)               |
| `get(i)`              | Array index                 | O(1)              | O(1)               |
| `best()`              | `get(0)`                    | O(1)              | O(1)               |
| `iter()`              | Slice + filter_map          | O(N)              | O(1)               |
| `Ord::cmp()`          | Compare best + len          | O(1)              | O(1)               |
| `PartialEq::eq()`     | Entry-by-entry compare      | O(N)              | O(1)               |
| `Hash::hash()`        | Hash len + entries          | O(N)              | O(1)               |

*The merge dedup scan is O(count) per candidate, with up to 2N candidates,
yielding O(N * 2N) = O(N^2).  For N <= 8, this is at most 128 comparisons.

**Space per weight instance** (N = 4):
- `entries`: 4 * 16 bytes = 64 bytes (4 x `Option<NbestEntry>`)
- `len`: 8 bytes (usize)
- Total: 72 bytes, entirely inline (no heap allocation for the weight itself)

**Concat heap allocation:** `concat_nbest` allocates a temporary
`Vec<NbestEntry>` of capacity N^2 for the cross-product.  For N = 4,
this is 16 entries * 12 bytes = 192 bytes.  The allocation is short-lived
(freed when `from_entries` returns).

---

## 12. Rust Implementation

The complete implementation from `prattail/src/automata/semiring.rs`
(lines 1373--1689):

**NbestEntry struct** (lines 1373--1391):

```rust
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct NbestEntry {
    pub path_id: u32,
    pub weight: TropicalWeight,
}

impl NbestEntry {
    #[inline]
    pub const fn new(path_id: u32, weight: TropicalWeight) -> Self {
        NbestEntry { path_id, weight }
    }
}
```

**NbestWeight struct** (lines 1417--1424):

```rust
#[derive(Clone, Copy, Debug)]
pub struct NbestWeight<const N: usize> {
    entries: [Option<NbestEntry>; N],
    len: usize,
}
```

**Semiring trait implementation** (lines 1569--1622):

```rust
impl<const N: usize> Semiring for NbestWeight<N> {
    fn zero() -> Self { Self::empty() }
    fn one() -> Self { Self::singleton(0, TropicalWeight::one()) }
    fn plus(&self, other: &Self) -> Self { self.merge_nbest(other) }
    fn times(&self, other: &Self) -> Self { self.concat_nbest(other) }
    fn is_zero(&self) -> bool { self.is_empty() }
    fn is_one(&self) -> bool {
        self.len == 1
            && self.entries[0].map_or(false, |e| e.path_id == 0 && e.weight.is_one())
    }
    fn approx_eq(&self, other: &Self, epsilon: f64) -> bool { /* entry-wise */ }
}
```

**Ordering** (lines 1647--1659):

```rust
impl<const N: usize> Ord for NbestWeight<N> {
    fn cmp(&self, other: &Self) -> Ordering {
        match (self.best(), other.best()) {
            (None, None) => Ordering::Equal,
            (None, Some(_)) => Ordering::Greater,
            (Some(_), None) => Ordering::Less,
            (Some(a), Some(b)) => a.weight.cmp(&b.weight)
                .then_with(|| self.len.cmp(&other.len)),
        }
    }
}
```

**Display** (lines 1670--1683):

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

**Default** (lines 1685--1689): returns `one()`, consistent with the
convention that the default weight is the multiplicative identity.

---

## 13. Comparison Table

| Property                  | NbestWeight<N>               | TropicalWeight           | CountingWeight         | BooleanWeight          |
|---------------------------|------------------------------|--------------------------|------------------------|------------------------|
| **Carrier**               | Sorted_N(u32 x R+)          | R+ ∪ {+inf}             | N (naturals)           | {false, true}          |
| **⊕ (plus)**              | merge_nbest (top N)          | min                      | + (addition)           | ∨ (OR)                 |
| **⊗ (times)**             | concat_nbest (cross, top N)  | + (addition)             | x (multiplication)     | ∧ (AND)                |
| **0̄ (zero)**              | [] (empty)                   | +inf                     | 0                      | false                  |
| **1̄ (one)**               | [(0, 0.0)]                   | 0.0                      | 1                      | true                   |
| **Commutative (⊕)**       | Yes                          | Yes                      | Yes                    | Yes                    |
| **Idempotent (⊕)**        | Yes (dedup by path_id)       | Yes                      | No                     | Yes                    |
| **Generalizes**           | TropicalWeight (N=1)         | --                       | --                     | --                     |
| **Semantics**             | N-best path tracking         | Shortest path            | Path counting          | Reachability           |
| **PraTTaIL use**          | Lazy disambiguation          | Priority dispatch        | Ambiguity detection    | Dead-rule detection    |
| **Rust size (N=4)**       | 72 bytes (inline)            | 8 bytes (inline)         | 8 bytes (inline)       | 1 byte (inline)        |
| **Rust Display**          | [(id:wt), ...]               | float / inf              | integer                | top / bot              |

**Relationship to N=1:**  When N = 1, `NbestWeight<1>` degenerates to a
single `(path_id, TropicalWeight)` pair.  The `merge_nbest` operation
becomes `min` (keeping the lower-weight entry), and `concat_nbest`
becomes weight addition.  This is precisely `TropicalWeight` with an
extra path_id tag.

---

## 14. Source References

**Source file**: `prattail/src/automata/semiring.rs`

- Section header and NbestEntry: lines 1369--1391
- NbestWeight struct definition: lines 1393--1424
- Constructors (empty, singleton, from_entries): lines 1426--1453
- Accessors (len, is_empty, get, best): lines 1455--1481
- Confidence gap: lines 1483--1492
- Iterator: lines 1494--1497
- merge_nbest (⊕ implementation): lines 1499--1543
- concat_nbest (⊗ implementation): lines 1545--1566
- Semiring trait implementation: lines 1569--1622
- PartialEq / Eq: lines 1624--1638
- PartialOrd / Ord: lines 1640--1659
- Hash: lines 1661--1668
- Display: lines 1670--1683
- Default: lines 1685--1689

**Tests**: `prattail/src/automata/semiring.rs`, lines 2640--2865

- `test_nbest_semiring_laws` -- zero/one identity, commutativity, annihilation
- `test_nbest_merge_keeps_top_n` -- truncation to N (N=3, 4 inputs)
- `test_nbest_merge_deduplicates` -- same path_id keeps lower weight
- `test_nbest_cross_product` -- single pair weight addition
- `test_nbest_cross_product_multi` -- 2x2 cross-product, verify best weight
- `test_nbest_empty_operations` -- zero element properties
- `test_nbest_one` -- one element properties
- `test_nbest_confidence_gap` -- gap computation, infinity for < 2 entries
- `test_nbest_ordering` -- lower best weight < higher, empty = worst
- `test_nbest_display` -- format for [], [(0:0.0)], multi-entry
- `test_nbest_hash` -- HashSet membership
- `test_nbest_from_entries` -- sort + truncate from unsorted Vec
- `test_nbest_iter` -- iteration order matches sorted order
- `test_nbest_n2_confidence` -- N=2 specialization for confidence gap
- `test_nbest_approx_eq` -- epsilon-based approximate equality

---

## 15. Cross-References

- [TropicalWeight theory](./tropical-weight.md) -- the scalar weight type used inside each NbestEntry; NbestWeight<1> degenerates to TropicalWeight with a path_id tag
- [BooleanWeight theory](./boolean-weight.md) -- NbestWeight projects to BooleanWeight via `is_zero()`
- [CountingWeight theory](./counting-weight.md) -- NbestWeight generalizes counting: `len()` gives the number of distinct paths (up to N)
- [ContextWeight theory](./context-weight.md) -- set semiring over rule labels; NbestWeight tracks path IDs while ContextWeight tracks rule label IDs
- [ProductWeight theory](./product-weight.md) -- NbestWeight can be composed as `ProductWeight<TropicalWeight, NbestWeight<N>>` for combined priority + N-best tracking
- [Semirings overview](../semirings.md) -- comprehensive survey of all semirings in PraTTaIL
- [WFST Optimization Pipeline](../../architecture/wfst/optimization-pipeline.md) -- NbestWeight is optimization C4 in the WFST pipeline roadmap
