# Tropical Semiring: TropicalWeight

## 1. Intuition & Motivation

The tropical semiring provides a *shortest-path algebra* for weighted
parse dispatch. Its carrier set consists of non-negative real numbers
augmented with positive infinity, and its two operations correspond
directly to parsing decisions:

- **Selecting among alternatives** (parallel paths) uses `min` -- the
  best alternative is the one with the lowest cost.
- **Chaining sequential segments** (a path through multiple arcs) uses
  ordinary addition -- costs accumulate along a derivation.

Within PraTTaIL, every parse dispatch decision is weighted:

```
lower cost  =  higher priority  =  tried first
```

A direct rule match (weight 0.0) is tried before a cross-category
cast (weight 0.5), which is tried before identifier lookahead
(weight 2.0). By encoding these priorities into a semiring,
PraTTaIL's dispatch, prediction WFST, beam pruning, and Viterbi
recovery all share the same algebraic framework -- the algorithms are
semiring-generic, while the weight type determines the semantics.

---

## 2. Formal Definition

The tropical semiring is the algebraic structure

```
T  =  ( R+ ∪ {+∞},  min,  +,  +∞,  0.0 )
```

where:

| Component                   | Symbol | Concrete value  | Meaning                          |
|-----------------------------|--------|-----------------|----------------------------------|
| Carrier set                 | K      | R+ ∪ {+∞}       | Non-negative reals plus infinity |
| Addition (⊕)                | min    | min(a, b)       | Select best alternative          |
| Multiplication (⊗)          | +      | a + b           | Accumulate cost along a path     |
| Additive identity (0̄)       | +∞     | `f64::INFINITY` | Unreachable path                 |
| Multiplicative identity (1̄) | 0.0    | `0.0_f64`       | Zero-cost transition             |

The name "tropical" comes from the replacement of ordinary addition
with `min` (or `max` in the max-plus variant). In the parsing
literature this is the standard semiring for Viterbi shortest-path
algorithms.

---

## 3. Semiring Axiom Verification

We verify all eight semiring axioms with concrete numerical examples.
Let a = 2.0, b = 5.0, c = 3.0.

### (A1) Associativity of ⊕

```
(a ⊕  b) ⊕  c  =  min(min(2.0, 5.0), 3.0)  =  min(2.0, 3.0)  =  2.0
a ⊕  (b ⊕  c)  =  min(2.0, min(5.0, 3.0))  =  min(2.0, 3.0)  =  2.0   ✓
```

Holds in general because `min` is associative over totally ordered sets.

### (A2) Commutativity of ⊕

```
a ⊕  b  =  min(2.0, 5.0)  =  2.0
b ⊕  a  =  min(5.0, 2.0)  =  2.0   ✓
```

Holds because `min` is symmetric: `min(x, y) = min(y, x)` for all x, y.

### (A3) ⊕  Identity

```
0̄ ⊕  a  =  min(+∞, 2.0)  =  2.0  =  a   ✓
a ⊕  0̄  =  min(2.0, +∞)  =  2.0  =  a   ✓
```

Positive infinity is the identity for `min` because every real number
is less than `+∞`.

### (M1) Associativity of ⊗

```
(a ⊗  b) ⊗  c  =  (2.0 + 5.0) + 3.0  =  7.0 + 3.0  =  10.0
a ⊗  (b ⊗  c)  =  2.0 + (5.0 + 3.0)  =  2.0 + 8.0  =  10.0   ✓
```

Holds because real addition is associative.

### (M2) ⊗  Identity

```
1̄ ⊗  a  =  0.0 + 2.0  =  2.0  =  a   ✓
a ⊗  1̄  =  2.0 + 0.0  =  2.0  =  a   ✓
```

Zero is the identity for real addition.

### (D1) Left Distributivity: ⊗  distributes over ⊕  from the left

```
a ⊗  (b ⊕  c)  =  2.0 + min(5.0, 3.0)  =  2.0 + 3.0  =  5.0
(a ⊗  b) ⊕  (a ⊗  c)  =  min(2.0 + 5.0, 2.0 + 3.0)  =  min(7.0, 5.0)  =  5.0   ✓
```

In general: `x + min(y, z) = min(x + y, x + z)` because addition by
a constant preserves the ordering of the operands.

### (D2) Right Distributivity: ⊗  distributes over ⊕  from the right

```
(a ⊕  b) ⊗  c  =  min(2.0, 5.0) + 3.0  =  2.0 + 3.0  =  5.0
(a ⊗  c) ⊕  (b ⊗  c)  =  min(2.0 + 3.0, 5.0 + 3.0)  =  min(5.0, 8.0)  =  5.0   ✓
```

Symmetric argument to (D1).

### (Z) Zero Annihilation

```
0̄ ⊗  a  =  +∞ + 2.0  =  +∞  =  0̄   ✓
a ⊗  0̄  =  2.0 + ∞   =  +∞  =  0̄   ✓
```

Any finite value added to `+∞` yields `+∞`. An unreachable state
remains unreachable regardless of what transitions follow.

All eight axioms are satisfied. T is a valid semiring.

> For the parsing-specific interpretation of these axioms, see
> [§4 Why Each Axiom Matters for Parsing](../semirings.md#4-why-each-axiom-matters-for-parsing).

---

## 4. Key Properties

### 4.1 Commutativity

**Claim**: The tropical semiring is commutative (⊗  is commutative).

**Proof**: For all a, b in R+ ∪ {+∞}:

```
a ⊗  b  =  a + b  =  b + a  =  b ⊗  a
```

Real addition is commutative, and `+∞ + x = x + +∞ = +∞` for all x.   ∎

Commutativity means path weights are independent of traversal
direction -- the weight of a path A → B → C equals the weight of
C → B → A.

### 4.2 Idempotency

**Claim**: The tropical semiring is idempotent (⊕  is idempotent).

**Proof**: For all a in R+ ∪ {+∞}:

```
a ⊕  a  =  min(a, a)  =  a
```

The minimum of any value with itself is that value.   ∎

Idempotency is the property that separates the tropical semiring from
the log semiring. It means that merging a path with itself does not
change the result -- precisely the semantics needed for shortest-path
algorithms where we want the single best path, not a probability sum.

### 4.3 Total Ordering

TropicalWeight implements `Ord` via `f64::total_cmp`, which defines a
total order on all IEEE 754 floats including NaN, -0.0, and +∞:

```
-NaN < -∞ < -finite < -0.0 < +0.0 < +finite < +∞ < +NaN
```

This total ordering is required for:
- Deterministic comparison in `BTreeMap` keys
- Consistent `Hash` semantics (via `f64::to_bits()`)
- Well-defined `min` behavior on all inputs

---

## 5. Priority Mapping

PraTTaIL's token kinds carry an integer priority in [0, 10] where
higher values denote higher priority. The conversion to tropical
weights *inverts* this convention so that lower weight = higher
priority:

```
weight  =  10.0  −  priority
```

### Priority-to-Weight Table

| Priority | Weight | Meaning                                         |
|----------|--------|-------------------------------------------------|
| 10       | 0.0    | Fixed keyword tokens (exact match, highest)     |
| 9        | 1.0    | Structural delimiters: `(`, `)`, `{`, `}`, etc. |
| 8        | 2.0    | Operators: `+`, `-`, `*`, `/`, `==`, etc.       |
| 7        | 3.0    | Multi-character operators: `<=`, `>=`, `!=`     |
| 5        | 5.0    | String literals                                 |
| 3        | 7.0    | Numeric literals (Integer, Float)               |
| 1        | 9.0    | Identifiers (lowest priority, most ambiguous)   |
| 0        | 10.0   | Fallback / unknown                              |

### Code

```rust
impl TropicalWeight {
    /// Convert a `TokenKind::priority()` value to a tropical weight.
    ///
    /// Higher priority (larger u8) maps to lower weight (better).
    /// Uses `MAX_PRIORITY - priority` where `MAX_PRIORITY = 10`.
    #[inline]
    pub fn from_priority(priority: u8) -> Self {
        TropicalWeight((10.0_f64) - priority as f64)
    }
}
```

This mapping preserves the ordering:

```
from_priority(10) = 0.0  <  from_priority(1) = 9.0
```

so `min(from_priority(10), from_priority(1)) = from_priority(10)`,
correctly selecting the higher-priority token.

---

## 6. Zero Annihilation

The zero element `+∞` represents an *unreachable* state or
*impossible* transition. Its annihilation property guarantees that
unreachable paths remain unreachable regardless of concatenation:

```
+∞ ⊗  x  =  +∞ + x  =  +∞     for all x ∈ R+ ∪ {+∞}
x ⊗  +∞  =  x + +∞  =  +∞     for all x ∈ R+ ∪ {+∞}
```

This is the correct semantic for dispatch: if any transition along a
derivation path is unreachable (weight `+∞`), the entire derivation
is unreachable. No finite-cost suffix can rescue an infinite-cost
prefix.

In the implementation, `is_zero()` checks both `is_infinite()` and
`is_sign_positive()` to distinguish `+∞` (zero element) from `-∞`
(which is not used but could appear from IEEE arithmetic):

```rust
fn is_zero(&self) -> bool {
    self.0.is_infinite() && self.0.is_sign_positive()
}
```

---

## 7. Path Weight Computation

### Worked Example

Consider a 4-node dispatch graph for parsing category `Bool` with two
alternative paths upon seeing token `Ident`:

```
                        ┌─────────────────────────────────┐
                        │          Dispatch Graph         │
                        │        (category: Bool)         │
                        └─────────────────────────────────┘

  Path 1 (cross-category):   q₀ ──0.5──▶ q₁ ──0.5──▶ q₃
  Path 2 (own-category):     q₀ ──2.0──▶ q₂ ──0.0──▶ q₃


         ┌──────┐    0.5     ┌──────┐
         │      │───────────▶│      │
         │  q₀  │            │  q₁  │──┐
         │      │            │      │  │  0.5
         └──────┘            └──────┘  │
            │                          │
            │                   ┌──────▼──────┐
            │  2.0              │             │
            │                   │     q₃      │
            │                   │   (accept)  │
            │                   └──────▲──────┘
            │                          │
            ▼                          │  0.0
         ┌──────┐                      │
         │      │──────────────────────┘
         │  q₂  │
         │      │
         └──────┘
```

**Path 1** (cross-category: parse `Int`, expect `==`, parse `Int`):

```
w₁  =  0.5 ⊗  0.5  =  0.5 + 0.5  =  1.0
```

**Path 2** (own-category: parse `Bool` directly via identifier):

```
w₂  =  2.0 ⊗  0.0  =  2.0 + 0.0  =  2.0
```

**Selecting the best alternative** (⊕):

```
w*  =  w₁ ⊕  w₂  =  min(1.0, 2.0)  =  1.0
```

The parser tries Path 1 (cross-category comparison) first, because
its accumulated tropical weight is lower.

---

## 8. Dispatch Weight Table

The following weights are assigned to dispatch actions during
PraTTaIL pipeline codegen. They determine the order of match arms
in generated `parse_<Cat>()` functions:

| Dispatch Type  | Weight | Rationale                                                |
|----------------|--------|----------------------------------------------------------|
| Direct         | 0.0    | Unique token in FIRST set -- deterministic, no ambiguity |
| Grouping (`(`) | 0.0    | Parenthesized expressions are unambiguous                |
| CrossCategory  | 0.0    | Unique to source category -- deterministic dispatch      |
| CrossCategory  | 0.5    | Shared token -- source tried first, fallback to own      |
| Cast           | 0.5    | Embedding rule -- lower than own-category fallback       |
| Lookahead      | 1.0+n  | Nth lookahead alternative (1.0, 1.1, 1.2, ...)           |
| Variable/Ident | 2.0    | Identifier -- most ambiguous, highest weight             |
| Fallback       | +∞     | Always-last catch-all `_ => parse_Cat_own()`             |

**Design principle**: More specific matches (fewer ambiguous
continuations) get lower weight. The fallback arm at `+∞` ensures it
is always placed last after sorting, regardless of other weights.

Weight-ordered dispatch improves CPU branch prediction because the
most likely alternative (lowest weight) is tested first in the
generated `match` statement.

---

## 9. Comparison with LogWeight

The tropical and log semirings share the same multiplicative operation
(real addition) but differ in how they combine alternatives:

| Property            | TropicalWeight             | LogWeight                          |
|---------------------|----------------------------|------------------------------------|
| Carrier set         | R+ ∪ {+∞}                  | R+ ∪ {+∞}                          |
| ⊕  (addition)       | min(a, b)                  | −ln(e⁻ᵃ + e⁻ᵇ) (log-sum-exp)       |
| ⊗  (multiplication) | a + b                      | a + b                              |
| 0̄ (zero)            | +∞                         | +∞                                 |
| 1̄ (one)             | 0.0                        | 0.0                                |
| Idempotent?         | Yes: min(a, a) = a         | No: lse(a, a) = a − ln 2 ≠ a       |
| Interpretation      | Best single path           | Sum over all paths (probabilities) |
| Use case            | Dispatch ordering, Viterbi | Forward-backward, training         |
| Feature gate        | Always available           | `wfst-log`                         |

The key distinction is **idempotency**. Because tropical ⊕  is
idempotent, merging duplicate paths is a no-op -- exactly what is
needed for shortest-path selection. The log semiring's non-idempotent
⊕  sums probabilities, which is needed for forward-backward scoring
and expectation-maximization training.

The tropical semiring can be viewed as the *zero-temperature limit* of
the log semiring:

```
lim      −T · ln( e^(−a/T) + e^(−b/T) )  =  min(a, b)
T → 0⁺
```

---

## 10. Pseudocode: Viterbi Shortest Path

The Viterbi algorithm finds the minimum-weight (shortest) path through
a directed acyclic graph (DAG), using tropical semiring operations
throughout. PraTTaIL uses this for both token lattice disambiguation
and error recovery.

```
ALGORITHM ViterbiShortestPath(G, start, final)
────────────────────────────────────────────────
  Input:  DAG G = (V, E, w) with nodes V, edges E, weight function w : E → R⁺
          start node s ∈ V, final node f ∈ V
  Output: Minimum-weight path from s to f, or UNREACHABLE

  1.  for each v ∈ V do
  2.      dist[v] ← +∞                    // tropical zero: unreachable
  3.      pred[v] ← NIL
  4.  dist[s] ← 0.0                       // tropical one: zero cost

  5.  for each node u ∈ V in topological order do
  6.      if dist[u] = +∞ then continue   // skip unreachable nodes
  7.      for each edge (u, v, w_uv) ∈ E do
  8.          candidate ← dist[u] ⊗  w_uv  // = dist[u] + w_uv
  9.          if candidate ⊕  dist[v] ≠ dist[v] then  // min improves
 10.              dist[v] ← candidate ⊕  dist[v]      // = min(candidate, dist[v])
 11.              pred[v] ← u

 12.  if dist[f] = +∞ then return UNREACHABLE

       // Backtrack to reconstruct path
 13.  path ← empty list
 14.  v ← f
 15.  while v ≠ s do
 16.      path.prepend(v)
 17.      v ← pred[v]
 18.  path.prepend(s)
 19.  return (path, dist[f])
```

**Complexity**: O(|V| + |E|) -- each node and edge is visited exactly
once, leveraging the DAG property (no negative cycles, topological
order suffices).

**Beam extension**: An optional beam width B prunes nodes where
`dist[u] > dist_best_final + B`, tightening the search space
progressively. This is implemented in `viterbi_best_path_beam()`.

---

## 11. Rust Implementation

The following is the complete `TropicalWeight` implementation from
`prattail/src/automata/semiring.rs`.

```rust
/// Tropical semiring weight: (R+ ∪ {+∞}, min, +, +∞, 0.0).
///
/// - plus = min: selects the best (lowest-cost) alternative
/// - times = +: accumulates costs along a path
/// - zero = +∞: unreachable (identity for min)
/// - one = 0.0: zero cost (identity for addition)
///
/// Lower weight = higher priority.
/// Implements total ordering via f64::total_cmp (NaN-safe).
#[derive(Clone, Copy)]
pub struct TropicalWeight(pub f64);

impl TropicalWeight {
    /// Create a new tropical weight.
    #[inline]
    pub const fn new(value: f64) -> Self {
        TropicalWeight(value)
    }

    /// Get the underlying f64 value.
    #[inline]
    pub const fn value(self) -> f64 {
        self.0
    }

    /// Positive infinity (unreachable / zero element).
    #[inline]
    pub const fn infinity() -> Self {
        TropicalWeight(f64::INFINITY)
    }

    /// Whether this weight is infinite (unreachable).
    #[inline]
    pub fn is_infinite(self) -> bool {
        self.0.is_infinite()
    }

    /// Convert a TokenKind::priority() value to a tropical weight.
    /// Higher priority (larger u8) maps to lower weight (better).
    /// weight = 10.0 - priority
    #[inline]
    pub fn from_priority(priority: u8) -> Self {
        TropicalWeight((10.0_f64) - priority as f64)
    }
}

impl Semiring for TropicalWeight {
    #[inline]
    fn zero() -> Self {
        TropicalWeight::infinity()          // +∞
    }

    #[inline]
    fn one() -> Self {
        TropicalWeight(0.0)                 // 0.0
    }

    #[inline]
    fn plus(&self, other: &Self) -> Self {
        TropicalWeight(self.0.min(other.0)) // min(a, b)
    }

    #[inline]
    fn times(&self, other: &Self) -> Self {
        TropicalWeight(self.0 + other.0)    // a + b
    }

    #[inline]
    fn is_zero(&self) -> bool {
        self.0.is_infinite() && self.0.is_sign_positive()
    }

    #[inline]
    fn is_one(&self) -> bool {
        self.0 == 0.0
    }

    fn approx_eq(&self, other: &Self, epsilon: f64) -> bool {
        if self.is_zero() && other.is_zero() {
            true                            // +∞ ≈ +∞
        } else if self.is_zero() || other.is_zero() {
            false                           // +∞ ≉ finite
        } else {
            (self.0 - other.0).abs() <= epsilon
        }
    }
}

// Total ordering via f64::total_cmp (NaN-safe, deterministic).
impl Ord for TropicalWeight {
    fn cmp(&self, other: &Self) -> Ordering {
        self.0.total_cmp(&other.0)
    }
}

// Hash via f64::to_bits (bitwise equality, safe for HashMap/BTreeMap).
impl Hash for TropicalWeight {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.0.to_bits().hash(state);
    }
}

// Default = one() = 0.0 (zero cost, not unreachable).
impl Default for TropicalWeight {
    fn default() -> Self {
        Self::one()
    }
}
```

### Implementation Notes

- **`is_zero` checks sign**: `f64::INFINITY` is positive infinity, but
  IEEE 754 also has `-∞`. Only `+∞` is the semiring zero; `-∞` would
  violate the carrier set constraint (R+ ∪ {+∞}).

- **`total_cmp` for `Ord`**: Standard `f64::partial_cmp` returns `None`
  for NaN comparisons. Using `total_cmp` provides a total order,
  enabling use in `BTreeMap` keys and `sort_by_key`.

- **`to_bits` for `Hash`**: Two equal-valued `f64` values always have
  the same bit representation (except +-0.0, but both map to weight
  0.0 in practice). This ensures `Hash` consistency with `Eq`.

- **`Default = one()`**: A newly created weight represents "zero cost"
  (the multiplicative identity), not "unreachable" (the additive
  identity). This is the natural default for weight initialization
  before accumulating path costs.

---

## 12. Integration into PraTTaIL

TropicalWeight is the default weight type throughout PraTTaIL's
weighted parsing pipeline. The following subsystems use it:

### 12.1 PredictionWfst (wfst.rs)

The `PredictionWfst` stores `WeightedAction` entries where each
action carries a `TropicalWeight`. Given a token, `predict()` returns
actions sorted by weight (lowest first):

```rust
pub fn predict(&self, token_name: &str) -> Vec<&WeightedAction> {
    // ... look up transitions from start state ...
    results.sort_by_key(|a| a.weight);  // TropicalWeight: Ord
    results
}
```

The beam-pruning variant `predict_pruned()` filters actions whose
weight exceeds `best_weight + beam_width`:

```rust
pub fn predict_pruned(&self, token_name: &str) -> Vec<&WeightedAction> {
    let actions = self.predict(token_name);
    match (self.beam_width, actions.first()) {
        (Some(beam), Some(best)) => {
            let threshold = best.weight.value() + beam.value();
            actions.into_iter()
                .filter(|a| a.weight.value() <= threshold)
                .collect()
        },
        _ => actions,
    }
}
```

### 12.2 Dispatch Arm Ordering (dispatch.rs, prediction.rs)

Generated `parse_<Cat>()` match arms are sorted by tropical weight
before emission:

```rust
// Sort by weight: lowest (most likely) first -- improves CPU branch prediction.
dispatch_arms.sort_by(|(_, wa), (_, wb)|
    wa.partial_cmp(wb).unwrap_or(Ordering::Equal));
```

The `build_complete_weight_map()` function in `prediction.rs`
assigns weights to all (category, token) pairs -- both ambiguous
(from composed dispatch) and deterministic (from rule specificity) --
ensuring every match arm has a tropical weight for sorting.

### 12.3 Viterbi Recovery (lattice.rs, recovery.rs)

When a parse error occurs, the recovery subsystem builds a repair
lattice with weighted edges:

| Repair Action | Tropical Weight |
|---------------|-----------------|
| Skip          | 0.5 per token   |
| Delete        | 1.0             |
| Substitute    | 1.5             |
| Insert        | 2.0             |

The `viterbi_best_path_beam()` function in `lattice.rs` finds the
minimum-cost repair sequence through this lattice. Edge weights are
accumulated via ⊗  (addition); alternative repair strategies are
compared via ⊕  (min).

### 12.4 Token Lattice (lattice.rs)

The generic `TokenLattice<T, S, W = TropicalWeight>` represents
lexical ambiguity as a weighted DAG. Each `LatticeEdge` carries a
weight of type W (defaulting to `TropicalWeight`), and `ViterbiPath`
extracts the lowest-cost tokenization.

---

## 13. Source Reference & See Also

### Source Location

- **File**: `prattail/src/automata/semiring.rs`, lines 57--198
- **Struct**: `TropicalWeight(pub f64)`
- **Trait impl**: `impl Semiring for TropicalWeight` (lines 106--146)
- **Ordering**: `impl Ord for TropicalWeight` via `f64::total_cmp` (lines 182--186)
- **Hashing**: `impl Hash for TropicalWeight` via `f64::to_bits()` (lines 188--192)
- **Tests**: `mod tests` (lines 820--923)

### Cross-References

- [Semiring Algebra Overview](../semirings.md) -- Axiom
  definitions, classification, and comparison of all five semirings
- [Counting Weight Theory](counting-weight.md) -- The counting semiring
  for ambiguity detection
- [WFST Prediction](../../../src/wfst.rs) -- PredictionWfst using
  TropicalWeight for dispatch ranking
- [Error Recovery](../../../src/recovery.rs) -- Repair cost constants
  and Viterbi recovery
- [Token Lattice](../../../src/lattice.rs) -- Lattice DAG with
  TropicalWeight edges and Viterbi extraction
- [Dispatch Codegen](../../../src/dispatch.rs) -- Weight-ordered match
  arm emission
- [Composed Dispatch](../../../docs/design/composed-dispatch.md) --
  How composed dispatch tables use tropical weights to resolve
  ambiguity at compile time
