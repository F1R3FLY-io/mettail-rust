# TensorWeight -- Design & Pipeline Integration

> **Date:** 2026-03-08

ProductWeight runs two analyses independently: each component ignores the
other. TensorWeight goes further -- it models **interactions** between
analyses. A single TensorWeight element is a sum of elementary tensors,
each pairing a weight from analysis 1 with a weight from analysis 2. The
multiplication rule (bilinearity) generates all cross-products, capturing
how combinations in one analysis dimension correlate with combinations
in the other. This makes TensorWeight the right tool when two metrics
are **not** independent.

---

## Table of Contents

1. [Intuition: Why Not ProductWeight?](#1-intuition-why-not-productweight)
2. [Mathematical Definition](#2-mathematical-definition)
3. [Data Structure](#3-data-structure)
4. [Semiring Operations](#4-semiring-operations)
5. [Simplification](#5-simplification)
6. [Projections and Conditional Marginals](#6-projections-and-conditional-marginals)
7. [StarSemiring Implementation](#7-starsemiring-implementation)
8. [Comparison with ProductWeight](#8-comparison-with-productweight)
9. [Pipeline Integration](#9-pipeline-integration)
10. [Rust API](#10-rust-api)
11. [Test Coverage](#11-test-coverage)
12. [Source References](#12-source-references)
13. [Cross-References](#13-cross-references)

---

## 1. Intuition: Why Not ProductWeight?

Consider tracking both **cost** (TropicalWeight) and **derivation count**
(CountingWeight) for a parse. ProductWeight gives you:

```
ProductWeight<TropicalWeight, CountingWeight> = (best_cost, total_count)
```

This tells you the best cost across all paths, and the total count across
all paths -- independently. It **does not** tell you "how many derivations
achieve cost 2.0 specifically?" or "what is the best cost among the
3-derivation paths?"

TensorWeight preserves this correlation:

```
TensorWeight<TropicalWeight, CountingWeight> =
    TW(1.0) tensor CW(2)  +  TW(3.0) tensor CW(5)
```

This says: "there are 2 derivations with cost 1.0, and 5 derivations
with cost 3.0." You can ask conditional questions:

- "How many derivations have cost 1.0?"  -->  `right_given_left(TW(1.0))` = CW(2)
- "What is the best cost among all derivations?"  -->  `project_left()` = TW(1.0)

ProductWeight collapses this to `(1.0, 7)` -- losing the per-cost breakdown.

---

## 2. Mathematical Definition

Given semirings `(S₁, ⊕₁, ⊗₁, 0₁, 1₁)` and `(S₂, ⊕₂, ⊗₂, 0₂, 1₂)`,
the tensor product semiring `S₁ ⊗_SR S₂` has:

- **Carrier set**: Formal sums of elementary tensors:
  ```
  Sigma_i  a_i tensor b_i     where a_i in S₁, b_i in S₂
  ```
  Each element is a **list** of pairs, not a single pair.

- **Plus** (⊕): Concatenation of term lists, then simplification:
  ```
  (Sigma_i  a_i tensor b_i) ⊕ (Sigma_j  c_j tensor d_j)
    = Sigma_i  a_i tensor b_i  +  Sigma_j  c_j tensor d_j
  ```
  After concatenation, terms with equal first components are merged
  by summing their second components via `⊕₂`.

- **Times** (⊗): Bilinear expansion over all pairwise products:
  ```
  (Sigma_i  a_i tensor b_i) ⊗ (Sigma_j  c_j tensor d_j)
    = Sigma_{i,j}  (a_i ⊗₁ c_j) tensor (b_i ⊗₂ d_j)
  ```
  This is the defining property of a tensor product: multiplication
  distributes over both components independently.

- **Zero**: The empty sum (no terms). `0 tensor w = w tensor 0 = 0` by
  bilinearity.

- **One**: The elementary tensor `1₁ tensor 1₂`.

### Key property: bilinearity

The bilinear multiplication law distinguishes TensorWeight from
ProductWeight. In a product semiring, `(a, b) * (c, d) = (a*c, b*d)` --
each component is independent. In a tensor product:

```
(a₁ tensor b₁ + a₂ tensor b₂) * (c tensor d)
  = (a₁*c tensor b₁*d) + (a₂*c tensor b₂*d)
```

The result has **two** terms, one for each term in the left operand.
This preserves the correlation structure that ProductWeight discards.

### Semiring axioms

| Axiom                  | Status     | Verified By               |
|------------------------|------------|---------------------------|
| Additive identity      | Holds      | `zero_is_additive_identity` |
| Additive commutativity | Holds      | `plus_commutativity`       |
| Additive associativity | Holds      | `plus_associativity`       |
| Multiplicative identity| Holds      | `one_is_multiplicative_identity` |
| Multiplicative assoc.  | Holds      | `times_associativity`      |
| Left distributivity    | Holds      | `left_distributivity`      |
| Right distributivity   | Holds      | `right_distributivity`     |
| Zero annihilation      | Holds      | `zero_annihilates_times`   |

---

## 3. Data Structure

```rust
pub struct TensorWeight<W1: Semiring, W2: Semiring> {
    /// Elementary tensor terms stored inline.
    terms: [(W1, W2); MAX_TENSOR_TERMS],
    /// Number of active terms. Invariant: len <= MAX_TENSOR_TERMS.
    len: usize,
}
```

### Fixed-capacity inline storage

**MAX_TENSOR_TERMS = 8**. Terms are stored in a fixed-size array to
satisfy the `Copy` bound required by the `Semiring` trait. This avoids
heap allocation and enables TensorWeight to participate in Viterbi,
forward-backward, and all other algorithms that require `Copy` semantics.

**Trade-off**: The fixed capacity means that operations generating more
than 8 terms must either simplify (merge terms with equal first
components) or truncate (discard excess terms). Truncation is a sound
over-approximation: it loses precision but never produces incorrect
results.

### Memory layout

For `TensorWeight<TropicalWeight, CountingWeight>`:

```
┌──────────────────────────────────────────────────────┐
│ terms[0]: (f64, u64)  = 16 bytes                     │
│ terms[1]: (f64, u64)  = 16 bytes                     │
│ ...                                                  │
│ terms[7]: (f64, u64)  = 16 bytes                     │
│ len: usize            =  8 bytes                     │
│                                                      │
│ Total: 8 * 16 + 8 = 136 bytes (stack-allocated)      │
└──────────────────────────────────────────────────────┘
```

Unused slots (indices `len..MAX_TENSOR_TERMS`) are padded with
`(W1::zero(), W2::zero())` and ignored by all operations.

---

## 4. Semiring Operations

### 4a. Plus (term list concatenation + simplification)

```rust
fn plus(&self, other: &Self) -> Self {
    // 1. Copy self's terms.
    // 2. Append other's terms (up to remaining capacity).
    // 3. Simplify: merge terms with equal first components.
}
```

**Complexity**: O(n^2) where n = MAX_TENSOR_TERMS = 8. The simplification
pass scans for matching first components, which is quadratic in the number
of active terms. Since n is bounded by 8, this is effectively O(1).

**Example**:

```
A = TW(1.0) tensor CW(3)  +  TW(2.0) tensor CW(5)
B = TW(1.0) tensor CW(7)  +  TW(4.0) tensor CW(1)

A ⊕ B (before simplification):
  TW(1.0) tensor CW(3) + TW(2.0) tensor CW(5) + TW(1.0) tensor CW(7) + TW(4.0) tensor CW(1)

A ⊕ B (after simplification, merging TW(1.0) terms):
  TW(1.0) tensor CW(10) + TW(2.0) tensor CW(5) + TW(4.0) tensor CW(1)
```

The two terms with `TW(1.0)` are merged: `CW(3) ⊕ CW(7) = CW(10)`.

### 4b. Times (bilinear expansion)

```rust
fn times(&self, other: &Self) -> Self {
    // For each pair (i, j) of terms from self and other:
    //   w1_new = self.terms[i].0.times(&other.terms[j].0)
    //   w2_new = self.terms[i].1.times(&other.terms[j].1)
    //   if neither is zero, add (w1_new, w2_new) to result
    // Simplify at end.
}
```

**Complexity**: O(m * n) where m, n are the active term counts of the
operands. In the worst case (both operands have 8 terms), this generates
up to 64 products, of which at most 8 survive into the result. The
rest are either zero-filtered or truncated.

**Zero optimization**: If either `w1_new` or `w2_new` is zero, the
elementary tensor is zero by bilinearity and is skipped immediately.
This saves capacity for non-trivial terms.

**Capacity exhaustion**: When the result reaches MAX_TENSOR_TERMS during
the inner loop, an intermediate simplification is attempted. If
simplification frees capacity, the new term is added; otherwise it is
lost (truncation).

**Example**:

```
X = TW(1.0) tensor CW(2)  +  TW(2.0) tensor CW(3)
Y = TW(0.0) tensor CW(1)  +  TW(1.0) tensor CW(2)

X ⊗ Y (bilinear expansion):
  (1.0+0.0) tensor (2*1) = TW(1.0) tensor CW(2)
  (1.0+1.0) tensor (2*2) = TW(2.0) tensor CW(4)
  (2.0+0.0) tensor (3*1) = TW(2.0) tensor CW(3)
  (2.0+1.0) tensor (3*2) = TW(3.0) tensor CW(6)

After simplification (merge TW(2.0) terms: CW(4) + CW(3) = CW(7)):
  TW(1.0) tensor CW(2)  +  TW(2.0) tensor CW(7)  +  TW(3.0) tensor CW(6)
```

### 4c. is_zero and is_one

```
is_zero():  len == 0, or all active terms have a zero component
is_one():   len == 1 and terms[0] == (W1::one(), W2::one())
```

The `is_zero` check is conservative: it scans all active terms because
simplification may not have removed all zero-component terms.

---

## 5. Simplification

Simplification is a two-pass O(n^2) algorithm over the active terms:

```
┌─────────────────────────────────────────────────────────────────┐
│ Pass 1: Remove zero terms                                       │
│                                                                 │
│   For each term (w1, w2):                                       │
│     if w1.is_zero() or w2.is_zero():                            │
│       drop the term (shift remaining terms down)                │
│                                                                 │
│ Pass 2: Merge terms with equal first components                 │
│                                                                 │
│   For each unmerged term i:                                     │
│     For each later term j:                                      │
│       if terms[i].0 == terms[j].0:                              │
│         terms[i].1 = terms[i].1.plus(&terms[j].1)              │
│         mark j as merged                                        │
│     if combined w2 is not zero:                                 │
│       emit (terms[i].0, combined_w2)                            │
└─────────────────────────────────────────────────────────────────┘
```

**Soundness**: Simplification preserves the algebraic value of the tensor
weight. Removing zero terms is exact (they contribute nothing). Merging
terms with equal first components uses the associativity and commutativity
of `W2::plus`:

```
a tensor b₁  +  a tensor b₂  =  a tensor (b₁ ⊕ b₂)
```

This identity follows from the bilinearity of the tensor product.

**When simplification runs**:
- After every `plus` operation (when term count exceeds 1 or capacity)
- After every `times` operation
- On demand via `simplify()` / `simplify_in_place()`
- During `from_pairs()` construction when input exceeds capacity

---

## 6. Projections and Conditional Marginals

TensorWeight provides four projection methods that extract information
from the correlated term structure:

### 6a. Marginal projections

| Method           | Return | Formula                                 | Semantics                           |
|------------------|--------|-----------------------------------------|-------------------------------------|
| `project_left()` | `W1`   | `⊕₁_i  w1_i`                           | Marginalize out W2; aggregate W1    |
| `project_right()`| `W2`   | `⊕₂_i  w2_i`                           | Marginalize out W1; aggregate W2    |

**Example**: For `TW(1.0) tensor CW(3) + TW(5.0) tensor CW(7)`:

```
project_left()  = TW::plus(1.0, 5.0) = min(1.0, 5.0) = TW(1.0)
project_right() = CW::plus(3, 7) = 3 + 7 = CW(10)
```

### 6b. Conditional marginals

| Method                    | Return | Formula                                        | Semantics                                  |
|---------------------------|--------|-------------------------------------------------|--------------------------------------------|
| `left_given_right(w2)`    | `W1`   | `⊕₁ { w1_i | w2_i == w2 }`                     | Aggregate W1 for terms matching given W2   |
| `right_given_left(w1)`    | `W2`   | `⊕₂ { w2_i | w1_i == w1 }`                     | Aggregate W2 for terms matching given W1   |

**Example**: For `TW(1.0) tensor CW(5) + TW(2.0) tensor CW(5) + TW(3.0) tensor CW(7)`:

```
left_given_right(CW(5))  = TW::plus(1.0, 2.0) = min(1.0, 2.0) = TW(1.0)
left_given_right(CW(7))  = TW(3.0)
left_given_right(CW(99)) = TW::zero()  (no match)

right_given_left(TW(1.0)) = CW(5)
right_given_left(TW(3.0)) = CW(7)
```

These conditional projections are the key advantage of TensorWeight over
ProductWeight. They answer questions like "what is the best cost among
derivations with exactly 5 alternatives?" -- questions that ProductWeight
cannot answer because it discards the correlation.

---

## 7. StarSemiring Implementation

When both component semirings implement `StarSemiring`, TensorWeight
provides a bounded power-series approximation of the Kleene star:

```rust
fn star(&self) -> Self {
    if self.is_zero() {
        return Self::one();  // star(0) = 1
    }

    let mut sum = Self::one();       // x^0
    let mut x_power = *self;         // x^1

    for _ in 0..STAR_ITERATION_LIMIT {
        let next_sum = sum.plus(&x_power);
        if next_sum.approx_eq(&sum, 1e-10) {
            return next_sum;         // converged
        }
        sum = next_sum;
        x_power = x_power.times(self);
    }

    sum  // truncated after STAR_ITERATION_LIMIT iterations
}
```

**STAR_ITERATION_LIMIT = 32**. The series `star(x) = Sigma_{k=0}^{limit} x^k`
is truncated when either:

1. **Convergence**: `sum_{k+1} approx_eq sum_k` (the added term x^k
   changed the sum by less than epsilon = 10^{-10}).
2. **Iteration limit**: 32 iterations without convergence.

**Kleene plus**: `plus_star(x) = x tensor star(x)`.

**Convergence guarantee**: For idempotent semirings (where `a ⊕ a = a`),
the series converges in at most |G| steps where G is the state space.
For non-idempotent semirings (e.g., CountingWeight), the series may not
converge within the limit, yielding an approximation.

---

## 8. Comparison with ProductWeight

```
┌───────────────────────────────────────────────────────────────────────┐
│                   ProductWeight<S1, S2>                               │
│                                                                       │
│  Element: single pair (s1, s2)                                        │
│  Plus:    (min(a,c), min(b,d))           component-wise              │
│  Times:   (a+c, b+d)                     component-wise              │
│                                                                       │
│  + Independent analyses                                               │
│  + Constant size (1 pair)                                             │
│  + No simplification needed                                          │
│  + Exact (no truncation)                                              │
│  - Loses correlation between components                               │
│                                                                       │
│  Use when: the two metrics are independent (e.g., priority + edit     │
│  count, where knowing the priority tells you nothing about edits)     │
├───────────────────────────────────────────────────────────────────────┤
│                   TensorWeight<S1, S2>                                │
│                                                                       │
│  Element: sum of up to 8 pairs Sigma (s1_i, s2_i)                    │
│  Plus:    concatenate + simplify (merge equal first components)       │
│  Times:   bilinear (all pairwise products)                            │
│                                                                       │
│  + Preserves correlation between components                           │
│  + Conditional projections answer "given W1, what W2?"                │
│  - Fixed capacity (8 terms max); truncation possible                  │
│  - Larger memory footprint (136 bytes vs 16 bytes for TW x CW)       │
│  - Simplification overhead on every operation                         │
│                                                                       │
│  Use when: the two metrics are correlated (e.g., "how many            │
│  derivations achieve each cost level?")                               │
└───────────────────────────────────────────────────────────────────────┘
```

### Decision diagram

```
Do the two analyses interact?
    │
    ├── No  --> ProductWeight<S1, S2>
    │          (independent, exact, efficient)
    │
    └── Yes --> TensorWeight<S1, S2>
               (correlated, approximate if >8 terms, richer queries)
```

---

## 9. Pipeline Integration

### 9a. Feature gating

TensorWeight is available unconditionally (no feature gate). It requires
only the base `Semiring` trait from its component types.

### 9b. Use cases

| Use Case                        | Instantiation                                    | What It Captures                              |
|---------------------------------|--------------------------------------------------|-----------------------------------------------|
| **Cost-count correlation**      | `TensorWeight<TropicalWeight, CountingWeight>`   | How many derivations achieve each cost level  |
| **Reachability-cost correlation**| `TensorWeight<BooleanWeight, TropicalWeight>`   | Which cost levels are reachable               |
| **Multi-pass fusion**           | `TensorWeight<W_disambiguation, W_recovery>`    | Joint disambiguation + recovery scoring       |
| **Provenance-cost interaction** | `TensorWeight<TropicalWeight, TropicalWeight>`   | Correlated cost analysis across two dimensions|

### 9c. Integration with Viterbi and forward-backward

TensorWeight implements `Semiring` (with `Copy`), so it can be used
directly with `viterbi_generic()` and `forward_scores()`:

```rust
type CostCount = TensorWeight<TropicalWeight, CountingWeight>;

// Build a lattice with tensor weights
let mut lattice: TokenLattice<Token, Span, CostCount> = TokenLattice::new();
// ... add edges with TensorWeight ...

// Run Viterbi (requires Semiring + Ord on CostCount)
let path = viterbi_generic(&lattice, final_node);
```

**Ordering caveat**: TensorWeight does not implement `Ord` by default
because there is no natural total ordering on sums of pairs. To use
TensorWeight with Viterbi, the component types must provide a meaningful
ordering, and a custom `Ord` implementation must be provided. In
practice, most uses project to a scalar before path comparison.

---

## 10. Rust API

### Construction

```rust
use prattail::tensor::{TensorWeight, MAX_TENSOR_TERMS};
use prattail::automata::semiring::{TropicalWeight as TW, CountingWeight as CW, Semiring};

type TC = TensorWeight<TW, CW>;

// Elementary tensor: single term
let t = TC::elementary(TW::new(3.0), CW::new(5));
assert_eq!(t.len(), 1);

// From pairs: multi-term tensor
let t2 = TC::from_pairs(&[
    (TW::new(1.0), CW::new(2)),
    (TW::new(3.0), CW::new(4)),
]);
assert_eq!(t2.len(), 2);

// Identity elements
let zero = TC::zero();   // empty sum
let one = TC::one();     // 1_TW tensor 1_CW = TW(0.0) tensor CW(1)
```

### Operations

```rust
let a = TC::elementary(TW::new(1.0), CW::new(2));
let b = TC::elementary(TW::new(3.0), CW::new(4));

// Plus: concatenate terms
let sum = a.plus(&b);
assert_eq!(sum.len(), 2);

// Times: bilinear product
let product = a.times(&b);
// (1.0+3.0) tensor (2*4) = TW(4.0) tensor CW(8)
assert_eq!(product.len(), 1);

// Simplification
let t = TC::from_pairs(&[
    (TW::new(1.0), CW::new(3)),
    (TW::new(1.0), CW::new(5)),
    (TW::new(2.0), CW::new(7)),
]);
let s = t.simplify();
// TW(1.0) terms merged: CW(3+5) = CW(8)
assert_eq!(s.len(), 2);
```

### Projections

```rust
let t = TC::from_pairs(&[
    (TW::new(2.0), CW::new(3)),
    (TW::new(5.0), CW::new(7)),
]);

// Marginal projections
let left = t.project_left();    // min(2.0, 5.0) = TW(2.0)
let right = t.project_right();  // 3 + 7 = CW(10)

// Conditional projections
let count_at_2 = t.right_given_left(&TW::new(2.0));   // CW(3)
let cost_for_7 = t.left_given_right(&CW::new(7));     // TW(5.0)
```

### StarSemiring

```rust
use prattail::automata::semiring::StarSemiring;

let t = TC::elementary(TW::new(2.0), CW::new(1));
let s = t.star();
// star(t) = 1 + t + t^2 + t^3 + ... (bounded)
assert!(!s.is_zero());
assert!(s.len() >= 1);
```

---

## 11. Test Coverage

Twenty-six tests in `tensor.rs` cover the full API:

| Category                | Tests                                                             | Count |
|-------------------------|-------------------------------------------------------------------|-------|
| **Construction**        | elementary, from_pairs, from_pairs_oversized, zero, one           | 5     |
| **Semiring laws**       | plus assoc/comm, times assoc, zero identity, one identity, zero annihilation, left/right distributivity | 8     |
| **Bilinear expansion**  | times_bilinear_expansion, times_two_multi_term_tensors            | 2     |
| **Projections**         | project_left/right, project_of_zero, project_of_one (6 tests)    | 6     |
| **Conditional marginals** | left_given_right, right_given_left                              | 2     |
| **Simplification**      | merge_equal_first, remove_zero_second, remove_zero_first          | 3     |
| **Display/Debug**       | display_format, debug_format                                      | (inline in other tests) |

Additional tests cover StarSemiring convergence, approx_eq for simplified
forms, and cross-type composition with BooleanWeight.

---

## 12. Source References

| Component                      | File         | Lines     |
|--------------------------------|--------------|-----------|
| Module documentation           | `tensor.rs`  | 1-54      |
| `MAX_TENSOR_TERMS` constant    | `tensor.rs`  | 69        |
| `STAR_ITERATION_LIMIT` constant| `tensor.rs`  | 75        |
| `TensorWeight` struct          | `tensor.rs`  | 81-92     |
| Constructors (elementary, from_pairs, len, is_empty, iter, as_slice) | `tensor.rs` | 96-150 |
| Simplification (simplify, simplify_in_place) | `tensor.rs` | 154-220 |
| Projections (project_left/right, left_given_right, right_given_left) | `tensor.rs` | 224-274 |
| `Semiring` impl (zero, one, plus, times, is_zero, is_one, approx_eq) | `tensor.rs` | 278-437 |
| `StarSemiring` impl (star, plus_star) | `tensor.rs` | 441-478 |
| `PartialEq` impl              | `tensor.rs`  | 482-509   |
| `Debug` / `Display` impls     | `tensor.rs`  | 511-542   |
| `Default` impl                | `tensor.rs`  | 544-548   |
| Tests (26+)                   | `tensor.rs`  | 554-900+  |

---

## 13. Cross-References

- **ProductWeight**: `product-weight.md` -- independent component-wise composition; use when analyses do not interact
- **ProvenanceWeight**: `provenance-weight.md` -- polynomial provenance; can be projected through TensorWeight for correlated provenance tracking
- **TropicalWeight**: `tropical-weight.md` -- common left component for cost analysis
- **CountingWeight**: `counting-weight.md` -- common right component for derivation counting
- **BooleanWeight**: `boolean-weight.md` -- common left component for reachability analysis
- **Semiring trait**: `semiring.rs` -- the Copy-bounded trait that TensorWeight implements
- **StarSemiring trait**: `semiring.rs` -- Kleene closure; TensorWeight provides bounded approximation
- **Lattice/Viterbi**: `lattice.rs` -- generic Viterbi works with any `Semiring + Ord`; TensorWeight requires custom Ord for Viterbi use
