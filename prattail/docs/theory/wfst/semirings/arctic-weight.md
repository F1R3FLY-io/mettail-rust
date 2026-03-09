# Arctic Semiring: ArcticWeight

## 1. Intuition & Motivation

The arctic semiring provides a *longest-path algebra* (maximum-benefit
computation) that is the algebraic dual of the tropical semiring.
Where the tropical semiring finds the minimum-cost path via `(min, +)`,
the arctic semiring finds the maximum-benefit path via `(max, +)`.

The two fundamental operations map to optimization decisions:

- **Selecting among alternatives** (parallel paths) uses `max` -- the
  best alternative is the one with the highest accumulated benefit.
- **Chaining sequential segments** (a path through multiple arcs) uses
  ordinary addition -- benefits accumulate along a derivation.

Within PraTTaIL, the arctic semiring answers the dual question to
tropical:

```
higher benefit  =  better outcome  =  tried first
```

While the tropical semiring answers "what is the cheapest path?", the
arctic semiring answers "what is the most beneficial path?".  This
duality makes it natural for:

- **Speedup analysis** in `cost_benefit.rs` -- higher speedup = better
  optimization to apply first
- **Worst-case propagation** in `lint.rs` -- longest error chain through
  an inter-category dependency graph
- **Critical path analysis** in `decision_tree.rs` -- identifying the
  parsing path with highest total cost

---

## 2. Formal Definition

The arctic semiring is the algebraic structure

```
A  =  ( R ∪ {-∞},  max,  +,  -∞,  0.0 )
```

where:

| Component                   | Symbol | Concrete value       | Meaning                             |
|-----------------------------|--------|----------------------|-------------------------------------|
| Carrier set                 | K      | R ∪ {-∞}             | All reals plus negative infinity    |
| Addition (⊕)                | max    | max(a, b)            | Select highest-benefit alternative  |
| Multiplication (⊗)          | +      | a + b                | Accumulate benefits along a path    |
| Additive identity (0-bar)   | -∞     | `f64::NEG_INFINITY`  | No benefit (unreachable)            |
| Multiplicative identity (1-bar) | 0.0| `0.0_f64`            | Zero benefit (neutral transition)   |

The name "arctic" contrasts with "tropical": both replace one of the
standard arithmetic operations with an extremum (min or max), but
they are duals.  In the max-plus literature (Cuninghame-Green, 1979),
the arctic semiring is also called the *max-plus algebra* or
*schedule algebra*.

---

## 3. Semiring Axiom Verification

We verify all eight semiring axioms with concrete numerical examples.
Let a = 3.0, b = -1.0, c = 2.0.

### (A1) Associativity of ⊕

```
(a ⊕  b) ⊕  c  =  max(max(3.0, -1.0), 2.0)  =  max(3.0, 2.0)  =  3.0
a ⊕  (b ⊕  c)  =  max(3.0, max(-1.0, 2.0))  =  max(3.0, 2.0)  =  3.0   ✓
```

Holds in general because `max` is associative over totally ordered sets.

### (A2) Commutativity of ⊕

```
a ⊕  b  =  max(3.0, -1.0)  =  3.0
b ⊕  a  =  max(-1.0, 3.0)  =  3.0   ✓
```

Holds because `max` is symmetric: `max(x, y) = max(y, x)` for all x, y.

### (A3) ⊕  Identity

```
0-bar ⊕  a  =  max(-∞, 3.0)  =  3.0  =  a   ✓
a ⊕  0-bar  =  max(3.0, -∞)  =  3.0  =  a   ✓
```

Negative infinity is the identity for `max` because every real number
is greater than `-∞`.

### (M1) Associativity of ⊗

```
(a ⊗  b) ⊗  c  =  (3.0 + (-1.0)) + 2.0  =  2.0 + 2.0  =  4.0
a ⊗  (b ⊗  c)  =  3.0 + ((-1.0) + 2.0)  =  3.0 + 1.0   =  4.0   ✓
```

Holds because real addition is associative.

### (M2) ⊗  Identity

```
1-bar ⊗  a  =  0.0 + 3.0  =  3.0  =  a   ✓
a ⊗  1-bar  =  3.0 + 0.0  =  3.0  =  a   ✓
```

Zero is the identity for real addition.

### (D1) Left Distributivity: ⊗  distributes over ⊕  from the left

```
a ⊗  (b ⊕  c)  =  3.0 + max(-1.0, 2.0)  =  3.0 + 2.0  =  5.0
(a ⊗  b) ⊕  (a ⊗  c)  =  max(3.0 + (-1.0), 3.0 + 2.0)  =  max(2.0, 5.0)  =  5.0   ✓
```

In general: `x + max(y, z) = max(x + y, x + z)` because addition by
a constant preserves the ordering of the operands.

### (D2) Right Distributivity: ⊗  distributes over ⊕  from the right

```
(a ⊕  b) ⊗  c  =  max(3.0, -1.0) + 2.0  =  3.0 + 2.0  =  5.0
(a ⊗  c) ⊕  (b ⊗  c)  =  max(3.0 + 2.0, (-1.0) + 2.0)  =  max(5.0, 1.0)  =  5.0   ✓
```

Symmetric argument to (D1).

### (Z) Zero Annihilation

```
0-bar ⊗  a  =  -∞ + 3.0  =  -∞  =  0-bar   ✓
a ⊗  0-bar  =  3.0 + (-∞) =  -∞  =  0-bar   ✓
```

Any finite value added to `-∞` yields `-∞`.  An unreachable state
remains unreachable regardless of what benefits follow.

All eight axioms are satisfied. A is a valid semiring.

> For the parsing-specific interpretation of these axioms, see
> [4. Why Each Axiom Matters for Parsing](../semirings.md#4-why-each-axiom-matters-for-parsing).

---

## 4. Key Properties

### 4.1 Commutativity

**Claim**: The arctic semiring is commutative (⊗  is commutative).

**Proof**: For all a, b in R ∪ {-∞}:

```
a ⊗  b  =  a + b  =  b + a  =  b ⊗  a
```

Real addition is commutative, and `-∞ + x = x + (-∞) = -∞` for all x.   ∎

Commutativity means path benefits are independent of traversal
direction -- the benefit of path A -> B -> C equals the benefit of
C -> B -> A.

### 4.2 Idempotency

**Claim**: The arctic semiring is idempotent (⊕  is idempotent).

**Proof**: For all a in R ∪ {-∞}:

```
a ⊕  a  =  max(a, a)  =  a
```

The maximum of any value with itself is that value.   ∎

Idempotency means that merging a path with itself does not change the
result -- precisely the semantics needed for longest-path algorithms
where we want the single best path, not a benefit sum.

### 4.3 Star Closure (Conditional)

**Claim**: `star(a)` converges for non-positive values.

**Proof**: For a <= 0:

```
star(a) = ⊕_{n=0}^{∞} a^n = sup{0, a, 2a, 3a, ...}
```

When a <= 0, the sequence `n*a` is non-increasing:
`0 >= a >= 2a >= 3a >= ...`, so `sup{0, a, 2a, ...} = 0 = one()`.

When a > 0, the sequence `n*a` diverges to `+∞`, so the infinite
sum does not converge in the arctic semiring.  The implementation
returns `zero()` (`-∞`) to signal divergence.   ∎

```rust
fn star(&self) -> Self {
    if self.0 <= 0.0 {
        Self::one()     // Converges: sup{0, a, 2a, ...} = 0
    } else {
        Self::zero()    // Diverges: positive benefits accumulate unboundedly
    }
}
```

### 4.4 Total Ordering (Reversed)

ArcticWeight implements `Ord` with **reversed** comparison: higher
value compares as "less than" lower value:

```
Ordering logic:  other.0.total_cmp(&self.0)
```

This reversal means that `min(ArcticWeight(3.0), ArcticWeight(-1.0))`
returns `ArcticWeight(3.0)` -- selecting the *highest-benefit*
alternative, which is the correct semantics for maximum-benefit path
selection in generic min-based algorithms.

---

## 5. Benefit Weight Table

PraTTaIL uses ArcticWeight in cost-benefit analysis to quantify the
*benefit* of applying an optimization.  Higher benefit = tried first.

### Optimization-Benefit Table

| Optimization                      | ArcticWeight | Meaning                                          |
|-----------------------------------|--------------|--------------------------------------------------|
| Backtracking elimination          | 5.0          | Highest benefit: removes save/restore overhead   |
| Rule fusion (BCG02)               | 4.0          | High benefit: reduces rule count                 |
| Congruence pruning (BCG03)        | 3.0          | Moderate: fewer equality checks                  |
| Depth bounding (ART05)            | 2.0          | Modest: bounds recursion depth                   |
| Hash consing (ART01)              | 1.0          | Small: deduplicates terms                        |
| No optimization                   | 0.0          | Neutral: identity (1-bar)                        |
| Dead rule (unreachable)           | -∞           | No benefit: optimization not applicable          |

### Code

```rust
impl ArcticWeight {
    /// Create a new arctic weight.
    #[inline]
    pub const fn new(value: f64) -> Self {
        ArcticWeight(value)
    }
}
```

The mapping preserves the ordering (via reversal):

```
min_ord(ArcticWeight(5.0), ArcticWeight(1.0)) = ArcticWeight(5.0)
```

so generic min-based algorithms correctly select the most beneficial
optimization.

---

## 6. Zero Annihilation

The zero element `-∞` represents an *unreachable* state or
*inapplicable* optimization.  Its annihilation property guarantees
that unreachable paths remain unreachable regardless of concatenation:

```
0-bar ⊗  x  =  -∞ + x  =  -∞  =  0-bar     for all x ∈ R ∪ {-∞}
x ⊗  0-bar  =  x + (-∞) =  -∞  =  0-bar     for all x ∈ R ∪ {-∞}
```

This is the correct semantic for benefit analysis: if any stage in an
optimization pipeline is inapplicable (benefit `-∞`), the entire
pipeline is inapplicable.  No positive-benefit suffix can rescue an
impossible prefix.

In the implementation, `is_zero()` checks both `is_infinite()` and
`is_sign_negative()` to distinguish `-∞` (zero element) from `+∞`
(which is not in the carrier set but could appear from IEEE
arithmetic):

```rust
fn is_zero(&self) -> bool {
    self.0.is_infinite() && self.0.is_sign_negative()
}
```

---

## 7. Path Benefit Computation

### Worked Example

Consider a 4-node optimization pipeline graph with two alternative
optimization strategies for a grammar category:

```
                        ┌─────────────────────────────────┐
                        │      Optimization Graph         │
                        │     (category: Expr)            │
                        └─────────────────────────────────┘

  Path 1 (fuse+prune):    q₀ ──4.0──▶ q₁ ──3.0──▶ q₃
  Path 2 (hash+bound):    q₀ ──1.0──▶ q₂ ──2.0──▶ q₃


         ┌──────┐    4.0     ┌──────┐
         │      │───────────▶│      │
         │  q₀  │            │  q₁  │──┐
         │      │            │      │  │  3.0
         └──────┘            └──────┘  │
            │                          │
            │                   ┌──────▼──────┐
            │  1.0              │             │
            │                   │     q₃      │
            │                   │   (accept)  │
            │                   └──────▲──────┘
            │                          │
            ▼                          │  2.0
         ┌──────┐                      │
         │      │──────────────────────┘
         │  q₂  │
         │      │
         └──────┘
```

**Path 1** (fuse+prune: apply rule fusion then congruence pruning):

```
b₁  =  4.0 ⊗  3.0  =  4.0 + 3.0  =  7.0
```

**Path 2** (hash+bound: apply hash consing then depth bounding):

```
b₂  =  1.0 ⊗  2.0  =  1.0 + 2.0  =  3.0
```

**Selecting the best alternative** (⊕):

```
b*  =  b₁ ⊕  b₂  =  max(7.0, 3.0)  =  7.0
```

The optimizer selects Path 1 (fuse+prune) because its accumulated
benefit is higher.

---

## 8. Dispatch Weight Table

The following benefit weights are used in PraTTaIL's cost-benefit
framework (`cost_benefit.rs`).  They quantify the "speedup" dimension
of `ProductWeight<ArcticWeight, TropicalWeight>`:

| Analysis Layer                | Benefit (arctic) | Rationale                                          |
|-------------------------------|------------------|----------------------------------------------------|
| Critical-path reduction       | 8.0              | Directly shortens longest parse path               |
| Backtracking elimination      | 5.0              | Removes save/restore -- major perf win             |
| Dead-rule elimination         | 4.0              | Reduces match arm count                            |
| Rule fusion                   | 3.5              | Merges multiple rules into one                     |
| Congruence pruning            | 3.0              | Fewer equality checks in Ascent evaluation         |
| Demand filtering              | 2.5              | Skips non-demanded categories                      |
| Depth bounding                | 2.0              | Bounds recursion, prevents blowup                  |
| Hash consing                  | 1.0              | Deduplication, constant-time equality               |
| No benefit                    | 0.0 (one)        | Identity -- no optimization effect                 |
| Inapplicable                  | -∞  (zero)       | Optimization does not apply to this grammar        |

**Design principle**: Benefits are on a logarithmic-like scale where
each unit of benefit represents a roughly multiplicative improvement.
The framework ranks optimizations by total benefit (arctic ⊕) and
applies the most beneficial first.

---

## 9. Comparison with TropicalWeight

The arctic and tropical semirings are *duals*: they share the same
multiplicative operation (real addition) but use opposite extrema for
their additive operation.

| Property            | ArcticWeight                       | TropicalWeight                     |
|---------------------|------------------------------------|------------------------------------|
| Carrier set         | R ∪ {-∞}                           | R+ ∪ {+∞}                          |
| ⊕  (addition)       | max(a, b)                          | min(a, b)                          |
| ⊗  (multiplication) | a + b                              | a + b                              |
| 0-bar (zero)        | -∞                                 | +∞                                 |
| 1-bar (one)         | 0.0                                | 0.0                                |
| Ord direction       | Reversed (higher = better)         | Natural (lower = better)           |
| Idempotent?         | Yes: max(a, a) = a                 | Yes: min(a, a) = a                 |
| Star(a)?            | one() if a <= 0, zero() if a > 0   | one() if a >= 0                    |
| Interpretation      | Best (highest benefit) path        | Best (lowest cost) path            |
| Use case            | Speedup analysis, critical path    | Dispatch ordering, Viterbi         |
| Feature gate        | Always available                   | Always available                   |

### Duality

The two semirings are related by negation `φ(x) = -x`:

```
φ(a ⊕_A b) = φ(max(a, b)) = -max(a, b) = min(-a, -b) = φ(a) ⊕_T φ(b)
φ(a ⊗_A b) = φ(a + b) = -(a + b) = (-a) + (-b) = φ(a) ⊗_T φ(b)
φ(0_A)     = φ(-∞) = +∞ = 0_T
φ(1_A)     = φ(0.0) = 0.0 = 1_T
```

This negation isomorphism means that any algorithm expressed over the
tropical semiring can be applied to the arctic semiring by negating
all weights, running the tropical algorithm, and negating the result.

### When to Use Which

- **ArcticWeight**: When maximizing a benefit or finding the longest
  (most expensive) path -- e.g., speedup ranking, worst-case error
  propagation depth, critical-path analysis.

- **TropicalWeight**: When minimizing a cost or finding the shortest
  (cheapest) path -- e.g., dispatch ordering, Viterbi parsing,
  minimum-cost error recovery.

---

## 10. Pseudocode: Critical Path Analysis

The critical-path algorithm finds the maximum-benefit (longest) path
through a directed acyclic graph (DAG), using arctic semiring
operations throughout.  This is used in `decision_tree.rs` to identify
the parsing path with the highest total cost.

```
ALGORITHM CriticalPathAnalysis(G, start, final)
────────────────────────────────────────────────────
  Input:  DAG G = (V, E, b) with nodes V, edges E, benefit function b : E → R
          start node s ∈ V, final node f ∈ V
  Output: Maximum-benefit path from s to f, or UNREACHABLE

  1.  for each v ∈ V do
  2.      benefit[v] ← -∞                    // arctic zero: unreachable
  3.      pred[v] ← NIL
  4.  benefit[s] ← 0.0                       // arctic one: zero benefit

  5.  for each node u ∈ V in topological order do
  6.      if benefit[u] = -∞ then continue   // skip unreachable nodes
  7.      for each edge (u, v, b_uv) ∈ E do
  8.          candidate ← benefit[u] ⊗  b_uv  // = benefit[u] + b_uv
  9.          if candidate ⊕  benefit[v] ≠ benefit[v] then  // max improves
 10.              benefit[v] ← candidate ⊕  benefit[v]      // = max(candidate, benefit[v])
 11.              pred[v] ← u

 12.  if benefit[f] = -∞ then return UNREACHABLE

       // Backtrack to reconstruct path
 13.  path ← empty list
 14.  v ← f
 15.  while v ≠ s do
 16.      path.prepend(v)
 17.      v ← pred[v]
 18.  path.prepend(s)
 19.  return (path, benefit[f])
```

**Complexity**: O(|V| + |E|) -- each node and edge is visited exactly
once, leveraging the DAG property (no positive cycles, topological
order suffices).

**Relationship to tropical Viterbi**: This is structurally identical
to the tropical Viterbi algorithm.  The only difference is the
replacement of `min` with `max` and `+∞` with `-∞` -- precisely the
negation duality between arctic and tropical semirings.

**Application**: In `decision_tree.rs`, critical-path analysis
identifies the parsing category chain with the highest total dispatch
cost, enabling the lint layer to emit warnings about expensive parse
paths.

---

## 11. Rust Implementation

The following is the complete `ArcticWeight` implementation from
`prattail/src/automata/semiring.rs`.

```rust
/// Arctic (max-plus) semiring `(R ∪ {-∞}, max, +, -∞, 0)`.
///
/// The dual of `TropicalWeight`: finds the **longest/heaviest** path rather
/// than the shortest. Where tropical computes minimum-cost, arctic computes
/// maximum-benefit.
///
/// - `plus = max`: selects the highest-benefit alternative
/// - `times = +`: accumulates benefits along a path
/// - `zero = -∞`: no benefit (identity for max)
/// - `one = 0.0`: zero benefit (identity for addition)
///
/// **Applications:**
/// - `cost_benefit.rs`: "speedup" dimension in ProductWeight
/// - `lint.rs`: worst-case error propagation depth
/// - `decision_tree.rs`: critical-path analysis
#[derive(Clone, Copy)]
pub struct ArcticWeight(pub f64);

impl ArcticWeight {
    /// Create a new arctic weight.
    #[inline]
    pub const fn new(value: f64) -> Self {
        ArcticWeight(value)
    }

    /// Get the underlying `f64` value.
    #[inline]
    pub const fn value(self) -> f64 {
        self.0
    }

    /// Negative infinity (unreachable / zero element).
    #[inline]
    pub const fn neg_infinity() -> Self {
        ArcticWeight(f64::NEG_INFINITY)
    }

    /// Whether this weight is negative-infinite (unreachable).
    #[inline]
    pub fn is_neg_infinite(self) -> bool {
        self.0.is_infinite() && self.0.is_sign_negative()
    }
}

impl Semiring for ArcticWeight {
    #[inline]
    fn zero() -> Self {
        ArcticWeight(f64::NEG_INFINITY)
    }

    #[inline]
    fn one() -> Self {
        ArcticWeight(0.0)
    }

    #[inline]
    fn plus(&self, other: &Self) -> Self {
        ArcticWeight(self.0.max(other.0))
    }

    #[inline]
    fn times(&self, other: &Self) -> Self {
        ArcticWeight(self.0 + other.0)
    }

    #[inline]
    fn is_zero(&self) -> bool {
        self.0.is_infinite() && self.0.is_sign_negative()
    }

    #[inline]
    fn is_one(&self) -> bool {
        self.0 == 0.0
    }

    fn approx_eq(&self, other: &Self, epsilon: f64) -> bool {
        if self.is_zero() && other.is_zero() {
            true
        } else if self.is_zero() || other.is_zero() {
            false
        } else {
            (self.0 - other.0).abs() <= epsilon
        }
    }
}

/// Higher value = better. Ordering is *reversed* from natural so that
/// generic shortest-path algorithms select the heaviest (best) alternative.
impl Ord for ArcticWeight {
    fn cmp(&self, other: &Self) -> Ordering {
        // Reverse: higher value = "lower" (better)
        other.0.total_cmp(&self.0)
    }
}

impl Hash for ArcticWeight {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.0.to_bits().hash(state);
    }
}

impl Default for ArcticWeight {
    fn default() -> Self {
        Self::one()
    }
}

impl DetectableZero for ArcticWeight {}
impl IdempotentSemiring for ArcticWeight {}
impl CompleteSemiring for ArcticWeight {}

impl StarSemiring for ArcticWeight {
    /// `star(a) = 0.0` (one) if `a <= 0`, else diverges (returns zero).
    ///
    /// Symmetric to tropical: `max(0, a, 2a, ...)` converges to `0` when
    /// `a <= 0` (non-positive benefits cannot grow unboundedly).
    #[inline]
    fn star(&self) -> Self {
        if self.0 <= 0.0 {
            Self::one()
        } else {
            Self::zero() // diverges for positive values
        }
    }
}
```

### Implementation Notes

- **`is_zero` checks sign**: `f64::NEG_INFINITY` is the zero element,
  but IEEE 754 also has `+∞`.  Only `-∞` is the semiring zero; `+∞`
  would violate the carrier set convention.

- **Reversed `Ord`**: `other.0.total_cmp(&self.0)` reverses the
  natural ordering so that higher benefit = "lower" in the ordering.
  This allows generic min-based shortest-path algorithms to work
  unchanged, selecting the highest-benefit path.

- **`total_cmp` for `Ord`**: Standard `f64::partial_cmp` returns `None`
  for NaN comparisons.  Using `total_cmp` provides a total order,
  enabling use in `BTreeMap` keys and `sort_by_key`.

- **`to_bits` for `Hash`**: Ensures `Hash` consistency with `Eq`.

- **`Default = one()`**: A newly created weight represents "zero
  benefit" (0.0, the multiplicative identity), not "unreachable"
  (`-∞`, the additive identity).

- **Display**: Prints `-inf` for the zero element, otherwise the
  float value with one decimal place.

---

## 12. Integration into PraTTaIL

ArcticWeight integrates with PraTTaIL's pipeline through three
primary subsystems.

### 12.1 Cost-Benefit Analysis (cost_benefit.rs)

The cost-benefit framework uses `ProductWeight<ArcticWeight,
TropicalWeight>` to jointly track *benefit* (arctic -- higher is
better) and *cost* (tropical -- lower is better):

```rust
// ProductWeight: (speedup_benefit, compile_time_cost)
let opt_weight = ProductWeight(
    ArcticWeight::new(5.0),     // 5.0 units of speedup benefit
    TropicalWeight::new(2.0),   // 2.0 units of compile-time cost
);
```

The product semiring orders by benefit first, then by cost as
tiebreaker.  This ensures high-benefit optimizations are applied
first, with compile-time cost used only to break ties.

### 12.2 Worst-Case Error Propagation (lint.rs)

The lint layer uses ArcticWeight for longest-path analysis through the
inter-category dependency graph.  A long error propagation chain
indicates that a parse error in one category could cascade through
many dependent categories:

```rust
// Longest path from error source to affected categories
// Higher arctic weight = more categories potentially affected
propagation_depth = arctic_longest_path(&inter_category_graph, error_source);
```

### 12.3 Critical Path Analysis (decision_tree.rs)

The decision tree module uses ArcticWeight to identify the parsing
path with the highest total dispatch cost.  This critical path
determines the worst-case parse time and is the primary target for
optimization:

```rust
// Critical path: parsing sequence with highest total cost
let critical = arctic_critical_path(&decision_tree, root_category);
// critical.weight = total cost of worst-case parse path
```

---

## 13. Source Reference & See Also

### Source Location

- **File**: `prattail/src/automata/semiring.rs`, lines 2079--2243
- **Struct**: `ArcticWeight(pub f64)`
- **Trait impl**: `impl Semiring for ArcticWeight` (lines 2129--2169)
- **Ordering**: `impl Ord for ArcticWeight` via reversed `total_cmp` (lines 2207--2212)
- **Star**: `impl StarSemiring for ArcticWeight` -- conditional on sign (lines 2230--2243)
- **Hashing**: `impl Hash for ArcticWeight` via `f64::to_bits()` (lines 2214--2218)
- **Tests**: lines 4019--4088

### Cross-References

- [Semiring Algebra Overview](../semirings.md) -- Axiom
  definitions, classification, and comparison of all semirings
- [Tropical Weight Theory](tropical-weight.md) -- The dual min-plus
  semiring (minimum-cost path)
- [Viterbi Weight Theory](viterbi-weight.md) -- Probability-domain
  most-likely-path semiring
- [Product Weight Theory](product-weight.md) -- Multi-dimensional
  weight combining arctic and tropical
- [Counting Weight Theory](counting-weight.md) -- Ambiguity counting

### References

- Cuninghame-Green, R. A. (1979). *Minimax Algebra*. Lecture Notes in
  Economics and Mathematical Systems, vol. 166. Springer-Verlag.
- Baccelli, F., Cohen, G., Olsder, G. J., & Quadrat, J.-P. (1992).
  *Synchronization and Linearity: An Algebra for Discrete Event
  Systems*. Wiley.
- Mohri, M. (2002). "Semiring frameworks and algorithms for
  shortest-distance problems." *Journal of Automata, Languages and
  Combinatorics*, 7(3), 321--350.
- Butkovič, P. (2010). *Max-linear Systems: Theory and Algorithms*.
  Springer Monographs in Mathematics.
