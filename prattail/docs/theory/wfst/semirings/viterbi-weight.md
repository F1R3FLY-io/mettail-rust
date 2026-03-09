# Viterbi Semiring: ViterbiWeight

## 1. Intuition & Motivation

The Viterbi semiring provides a *most-likely-path algebra* operating
directly in the probability domain `[0, 1]`.  Where the tropical
semiring encodes costs as negative log-probabilities and finds the
minimum-cost path, the Viterbi semiring works with raw probabilities
and finds the maximum-probability path.

The two fundamental operations map directly onto parsing decisions:

- **Selecting among alternatives** (parallel paths) uses `max` -- the
  best alternative is the one with the highest probability.
- **Chaining sequential segments** (a path through multiple arcs) uses
  ordinary multiplication -- probabilities compose multiplicatively
  along a derivation.

Within PraTTaIL, the Viterbi semiring serves contexts where
probability values are the natural currency:

```
higher probability  =  more confident  =  tried first
```

A recovery strategy with confidence 0.95 is preferred over one with
confidence 0.60.  By encoding confidences into a semiring, recovery
scoring, direct probability I/O, and small-model training all share
the same algebraic framework as PraTTaIL's dispatch pipeline -- the
algorithms are semiring-generic, while the weight type determines the
semantics.

---

## 2. Formal Definition

The Viterbi semiring is the algebraic structure

```
V  =  ( [0, 1],  max,  *,  0,  1 )
```

where:

| Component                   | Symbol | Concrete value | Meaning                                 |
|-----------------------------|--------|----------------|-----------------------------------------|
| Carrier set                 | K      | [0, 1]         | Probabilities from impossible to certain|
| Addition (⊕)                | max    | max(a, b)      | Select most probable alternative        |
| Multiplication (⊗)          | *      | a * b          | Compose probabilities along a path      |
| Additive identity (0-bar)   | 0      | `0.0_f64`      | Impossible event                        |
| Multiplicative identity (1-bar) | 1  | `1.0_f64`      | Certain event (no probability loss)     |

The name "Viterbi" comes from the Viterbi algorithm (1967) for
finding the most probable state sequence in a hidden Markov model.
The semiring captures the algebraic backbone of that algorithm:
`max` selects among hypotheses, multiplication chains transition
probabilities.

---

## 3. Semiring Axiom Verification

We verify all eight semiring axioms with concrete numerical examples.
Let a = 0.8, b = 0.3, c = 0.5.

### (A1) Associativity of ⊕

```
(a ⊕  b) ⊕  c  =  max(max(0.8, 0.3), 0.5)  =  max(0.8, 0.5)  =  0.8
a ⊕  (b ⊕  c)  =  max(0.8, max(0.3, 0.5))  =  max(0.8, 0.5)  =  0.8   ✓
```

Holds in general because `max` is associative over totally ordered sets.

### (A2) Commutativity of ⊕

```
a ⊕  b  =  max(0.8, 0.3)  =  0.8
b ⊕  a  =  max(0.3, 0.8)  =  0.8   ✓
```

Holds because `max` is symmetric: `max(x, y) = max(y, x)` for all x, y.

### (A3) ⊕  Identity

```
0-bar ⊕  a  =  max(0.0, 0.8)  =  0.8  =  a   ✓
a ⊕  0-bar  =  max(0.8, 0.0)  =  0.8  =  a   ✓
```

Zero is the identity for `max` because every probability in `[0, 1]`
is at least 0.

### (M1) Associativity of ⊗

```
(a ⊗  b) ⊗  c  =  (0.8 * 0.3) * 0.5  =  0.24 * 0.5  =  0.12
a ⊗  (b ⊗  c)  =  0.8 * (0.3 * 0.5)  =  0.8 * 0.15   =  0.12   ✓
```

Holds because real multiplication is associative.

### (M2) ⊗  Identity

```
1-bar ⊗  a  =  1.0 * 0.8  =  0.8  =  a   ✓
a ⊗  1-bar  =  0.8 * 1.0  =  0.8  =  a   ✓
```

One is the identity for real multiplication.

### (D1) Left Distributivity: ⊗  distributes over ⊕  from the left

```
a ⊗  (b ⊕  c)  =  0.8 * max(0.3, 0.5)  =  0.8 * 0.5  =  0.4
(a ⊗  b) ⊕  (a ⊗  c)  =  max(0.8 * 0.3, 0.8 * 0.5)  =  max(0.24, 0.4)  =  0.4   ✓
```

In general: `x * max(y, z) = max(x * y, x * z)` for non-negative x,
because multiplication by a non-negative constant preserves ordering.

### (D2) Right Distributivity: ⊗  distributes over ⊕  from the right

```
(a ⊕  b) ⊗  c  =  max(0.8, 0.3) * 0.5  =  0.8 * 0.5  =  0.4
(a ⊗  c) ⊕  (b ⊗  c)  =  max(0.8 * 0.5, 0.3 * 0.5)  =  max(0.4, 0.15)  =  0.4   ✓
```

Symmetric argument to (D1).

### (Z) Zero Annihilation

```
0-bar ⊗  a  =  0.0 * 0.8  =  0.0  =  0-bar   ✓
a ⊗  0-bar  =  0.8 * 0.0  =  0.0  =  0-bar   ✓
```

Any probability multiplied by zero yields zero.  An impossible event
remains impossible regardless of what transitions follow.

All eight axioms are satisfied. V is a valid semiring.

> For the parsing-specific interpretation of these axioms, see
> [4. Why Each Axiom Matters for Parsing](../semirings.md#4-why-each-axiom-matters-for-parsing).

---

## 4. Key Properties

### 4.1 Commutativity

**Claim**: The Viterbi semiring is commutative (⊗  is commutative).

**Proof**: For all a, b in [0, 1]:

```
a ⊗  b  =  a * b  =  b * a  =  b ⊗  a
```

Real multiplication is commutative.   ∎

Commutativity means path probabilities are independent of traversal
direction -- the probability of path A -> B -> C equals the probability
of C -> B -> A.

### 4.2 Idempotency

**Claim**: The Viterbi semiring is idempotent (⊕  is idempotent).

**Proof**: For all a in [0, 1]:

```
a ⊕  a  =  max(a, a)  =  a
```

The maximum of any value with itself is that value.   ∎

Idempotency means that merging a path with itself does not change the
result.  This is the property that separates the Viterbi semiring from
the counting semiring (which sums) -- precisely the semantics needed for
most-likely-path algorithms where we want the single best path, not a
probability sum.

### 4.3 Completeness and Star

**Claim**: ViterbiWeight is a complete star semiring.

**Proof of star closure**: For any a in [0, 1]:

```
star(a) = ⊕_{n=0}^{∞} a^n = sup{1, a, a², a³, ...}
```

Since a in [0, 1], the sequence `a^n` is non-increasing, so
`sup{1, a, a², ...} = 1 = one()`.

For a = 0: `sup{1, 0, 0, ...} = 1`.
For a = 0.5: `sup{1, 0.5, 0.25, 0.125, ...} = 1`.
For a = 1: `sup{1, 1, 1, ...} = 1`.   ∎

The implementation returns `ViterbiWeight(1.0)` unconditionally,
which is correct for all probabilities in `[0, 1]`.

### 4.4 Total Ordering (Reversed)

ViterbiWeight implements `Ord` with **reversed** comparison: higher
probability compares as "less than" lower probability.  This is
critical for compatibility with generic min-based algorithms:

```
Ordering logic:  other.0.total_cmp(&self.0)
```

This reversal means that `min(ViterbiWeight(0.8), ViterbiWeight(0.3))`
returns `ViterbiWeight(0.8)` -- selecting the *most probable*
alternative, which is the correct semantics for Viterbi path selection.

The total ordering is required for:
- Deterministic comparison in `BTreeMap` keys
- Consistent `Hash` semantics (via `f64::to_bits()`)
- Well-defined `max`-like behavior through generic `min` operations

---

## 5. Priority Mapping

ViterbiWeight maps directly to *dispatch confidence* rather than
to integer priority levels.  While TropicalWeight converts priority
levels via `weight = 10 - priority`, ViterbiWeight expresses the
probability that a dispatch decision is correct.

### Confidence-to-Probability Table

| Dispatch Confidence   | ViterbiWeight | Meaning                                          |
|-----------------------|---------------|--------------------------------------------------|
| Certain               | 1.0           | Unique token in FIRST set -- deterministic       |
| Very high             | 0.95          | Cross-category cast, very low ambiguity          |
| High                  | 0.8           | Composed dispatch, resolved with lookahead       |
| Moderate              | 0.5           | Binary ambiguity requiring backtrack             |
| Low                   | 0.2           | Multiple ambiguous alternatives                  |
| Impossible            | 0.0           | Dead rule, unreachable dispatch                  |

### Code

```rust
impl ViterbiWeight {
    /// Create a Viterbi weight from a probability in `[0, 1]`.
    #[inline]
    pub fn new(probability: f64) -> Self {
        debug_assert!(
            (0.0..=1.0).contains(&probability),
            "ViterbiWeight: probability must be in [0, 1], got {probability}"
        );
        ViterbiWeight(probability)
    }
}
```

This mapping preserves the ordering (via reversal):

```
min_ord(ViterbiWeight(1.0), ViterbiWeight(0.2)) = ViterbiWeight(1.0)
```

so generic min-based algorithms correctly select the most confident
dispatch target.

---

## 6. Zero Annihilation

The zero element `0.0` represents an *impossible* event.  Its
annihilation property guarantees that impossible paths remain
impossible regardless of concatenation:

```
0-bar ⊗  x  =  0.0 * x  =  0.0  =  0-bar     for all x ∈ [0, 1]
x ⊗  0-bar  =  x * 0.0  =  0.0  =  0-bar     for all x ∈ [0, 1]
```

This is the correct semantic for dispatch: if any transition along a
derivation path is impossible (probability 0.0), the entire derivation
is impossible.  No positive-probability suffix can rescue a
zero-probability prefix.

In the implementation, `is_zero()` checks exact equality with `0.0`:

```rust
fn is_zero(&self) -> bool {
    self.0 == 0.0
}
```

Unlike TropicalWeight (which must distinguish `+∞` from `-∞`), there
is no sign ambiguity -- zero probability is simply `0.0`.

---

## 7. Path Probability Computation

### Worked Example

Consider a 4-node recovery graph for error correction with two
alternative repair strategies upon encountering a parse error:

```
                        ┌─────────────────────────────────┐
                        │        Recovery Graph           │
                        │     (category: Expr)            │
                        └─────────────────────────────────┘

  Path 1 (substitute):    q₀ ──0.9──▶ q₁ ──0.8──▶ q₃
  Path 2 (insert+skip):   q₀ ──0.7──▶ q₂ ──0.6──▶ q₃


         ┌──────┐    0.9     ┌──────┐
         │      │───────────▶│      │
         │  q₀  │            │  q₁  │──┐
         │      │            │      │  │  0.8
         └──────┘            └──────┘  │
            │                          │
            │                   ┌──────▼──────┐
            │  0.7              │             │
            │                   │     q₃      │
            │                   │   (accept)  │
            │                   └──────▲──────┘
            │                          │
            ▼                          │  0.6
         ┌──────┐                      │
         │      │──────────────────────┘
         │  q₂  │
         │      │
         └──────┘
```

**Path 1** (substitute: replace erroneous token with expected):

```
p₁  =  0.9 ⊗  0.8  =  0.9 * 0.8  =  0.72
```

**Path 2** (insert+skip: insert missing token, skip erroneous):

```
p₂  =  0.7 ⊗  0.6  =  0.7 * 0.6  =  0.42
```

**Selecting the best alternative** (⊕):

```
p*  =  p₁ ⊕  p₂  =  max(0.72, 0.42)  =  0.72
```

The recovery engine selects Path 1 (substitution) because its
accumulated probability is higher.

---

## 8. Dispatch Weight Table

The following probability assignments correspond to recovery
strategy confidence levels in PraTTaIL.  They determine the
order of recovery attempts:

| Recovery Type       | ViterbiWeight | Rationale                                                   |
|---------------------|---------------|-------------------------------------------------------------|
| No error            | 1.0           | Parse succeeded -- no recovery needed                       |
| Substitute          | 0.9           | Single-token substitution -- very likely correct            |
| Insert              | 0.8           | Missing token insertion -- high confidence                  |
| Skip                | 0.7           | Skip unexpected token -- moderate confidence                |
| Insert+Skip combo   | 0.56          | Two-step recovery: 0.8 * 0.7 = 0.56                        |
| Multi-skip          | 0.49          | Skip two tokens: 0.7 * 0.7 = 0.49                          |
| Impossible          | 0.0           | No viable recovery -- backtrack to earlier checkpoint       |

**Design principle**: More targeted repairs (fewer tokens affected)
get higher probability.  The zero-probability entry at `0.0` ensures
it is recognized as unreachable by `is_zero()`.

Probability-ordered recovery improves error correction quality because
the most likely correct repair is attempted first.

---

## 9. Comparison with TropicalWeight

The Viterbi and tropical semirings are *isomorphic* via the negative
logarithm transformation `w = -ln(p)`.  They encode the same
information but in different numerical domains:

| Property            | ViterbiWeight                      | TropicalWeight                     |
|---------------------|------------------------------------|------------------------------------|
| Carrier set         | [0, 1]                             | R+ ∪ {+∞}                          |
| ⊕  (addition)       | max(a, b)                          | min(a, b)                          |
| ⊗  (multiplication) | a * b                              | a + b                              |
| 0-bar (zero)        | 0.0                                | +∞                                 |
| 1-bar (one)         | 1.0                                | 0.0                                |
| Ord direction       | Reversed (higher = better)         | Natural (lower = better)           |
| Idempotent?         | Yes: max(a, a) = a                 | Yes: min(a, a) = a                 |
| Star?               | Yes: star(a) = 1.0                 | Yes: star(a) = 0.0 for a >= 0     |
| Domain              | Probability                        | Negative log-probability           |
| Precision           | Limited near 0 and 1               | Better dynamic range               |
| Use case            | Direct probability I/O, recovery   | Dispatch ordering, Viterbi         |

### Isomorphism

The bijective mapping `φ: V -> T` defined by `φ(p) = -ln(p)` is a
semiring homomorphism:

```
φ(a ⊕_V b) = φ(max(a, b)) = -ln(max(a, b)) = min(-ln(a), -ln(b)) = φ(a) ⊕_T φ(b)
φ(a ⊗_V b) = φ(a * b) = -ln(a * b) = -ln(a) + (-ln(b)) = φ(a) ⊗_T φ(b)
φ(0_V)     = φ(0.0) = -ln(0) = +∞ = 0_T
φ(1_V)     = φ(1.0) = -ln(1) = 0.0 = 1_T
```

### Bidirectional Conversion

```rust
impl ViterbiWeight {
    /// Convert from a TropicalWeight (negative log-probability).
    pub fn from_tropical(w: TropicalWeight) -> Self {
        if w.is_zero() {
            ViterbiWeight(0.0)         // +∞ -> probability 0
        } else {
            ViterbiWeight((-w.value()).exp())  // p = e^(-w)
        }
    }

    /// Convert to a TropicalWeight (negative log-probability).
    pub fn to_tropical(self) -> TropicalWeight {
        if self.0 == 0.0 {
            TropicalWeight::infinity()  // probability 0 -> +∞
        } else {
            TropicalWeight(-self.0.ln()) // w = -ln(p)
        }
    }
}
```

### Numerical Example

```
p = 0.5:  -ln(0.5) = 0.6931...  (TropicalWeight)
          exp(-0.6931...) = 0.5  (back to ViterbiWeight)   ✓
```

### When to Use Which

- **ViterbiWeight**: When probabilities are the natural input/output
  format -- e.g., recovery confidence scores, direct HMM probability
  tables, small models where `[0, 1]` precision suffices.

- **TropicalWeight**: When numerical stability matters (log domain
  avoids floating-point underflow for very small probabilities), or
  when integrating with the standard WFST dispatch pipeline.

---

## 10. Pseudocode: Viterbi Most-Probable Path

The Viterbi algorithm finds the maximum-probability path through a
directed acyclic graph (DAG), using Viterbi semiring operations
throughout.

```
ALGORITHM ViterbiMostProbablePath(G, start, final)
────────────────────────────────────────────────────
  Input:  DAG G = (V, E, p) with nodes V, edges E, probability function p : E → [0,1]
          start node s ∈ V, final node f ∈ V
  Output: Maximum-probability path from s to f, or IMPOSSIBLE

  1.  for each v ∈ V do
  2.      prob[v] ← 0.0                     // Viterbi zero: impossible
  3.      pred[v] ← NIL
  4.  prob[s] ← 1.0                         // Viterbi one: certain

  5.  for each node u ∈ V in topological order do
  6.      if prob[u] = 0.0 then continue    // skip impossible nodes
  7.      for each edge (u, v, p_uv) ∈ E do
  8.          candidate ← prob[u] ⊗  p_uv    // = prob[u] * p_uv
  9.          if candidate ⊕  prob[v] ≠ prob[v] then  // max improves
 10.              prob[v] ← candidate ⊕  prob[v]      // = max(candidate, prob[v])
 11.              pred[v] ← u

 12.  if prob[f] = 0.0 then return IMPOSSIBLE

       // Backtrack to reconstruct path
 13.  path ← empty list
 14.  v ← f
 15.  while v ≠ s do
 16.      path.prepend(v)
 17.      v ← pred[v]
 18.  path.prepend(s)
 19.  return (path, prob[f])
```

**Complexity**: O(|V| + |E|) -- each node and edge is visited exactly
once, leveraging the DAG property.

**Equivalence to tropical Viterbi**: This algorithm produces the same
path as the tropical Viterbi algorithm applied with
`TropicalWeight(-ln(p))` weights, because the semirings are
isomorphic via `-ln`.

---

## 11. Rust Implementation

The following is the complete `ViterbiWeight` implementation from
`prattail/src/automata/semiring.rs`.

```rust
/// Viterbi semiring `([0,1], max, *, 0, 1)`.
///
/// Direct probabilistic reasoning in the probability domain [0, 1].
/// While `TropicalWeight` is the log-domain equivalent (via `w = -ln(p)`),
/// `ViterbiWeight` operates directly on probabilities.
///
/// - plus = max: selects the most probable alternative
/// - times = *: multiplies probabilities along a path
/// - zero = 0.0: impossible (identity for max)
/// - one = 1.0: certain (identity for multiplication)
#[derive(Clone, Copy)]
pub struct ViterbiWeight(pub f64);

impl ViterbiWeight {
    /// Create a Viterbi weight from a probability in `[0, 1]`.
    #[inline]
    pub fn new(probability: f64) -> Self {
        debug_assert!(
            (0.0..=1.0).contains(&probability),
            "ViterbiWeight: probability must be in [0, 1], got {probability}"
        );
        ViterbiWeight(probability)
    }

    /// Get the probability value.
    #[inline]
    pub const fn probability(self) -> f64 {
        self.0
    }

    /// Convert from a `TropicalWeight` (negative log-probability).
    #[inline]
    pub fn from_tropical(w: TropicalWeight) -> Self {
        if w.is_zero() {
            ViterbiWeight(0.0)
        } else {
            ViterbiWeight((-w.value()).exp())
        }
    }

    /// Convert to a `TropicalWeight` (negative log-probability).
    #[inline]
    pub fn to_tropical(self) -> TropicalWeight {
        if self.0 == 0.0 {
            TropicalWeight::infinity()
        } else {
            TropicalWeight(-self.0.ln())
        }
    }
}

impl Semiring for ViterbiWeight {
    #[inline]
    fn zero() -> Self {
        ViterbiWeight(0.0)
    }

    #[inline]
    fn one() -> Self {
        ViterbiWeight(1.0)
    }

    #[inline]
    fn plus(&self, other: &Self) -> Self {
        ViterbiWeight(self.0.max(other.0))
    }

    #[inline]
    fn times(&self, other: &Self) -> Self {
        ViterbiWeight(self.0 * other.0)
    }

    #[inline]
    fn is_zero(&self) -> bool {
        self.0 == 0.0
    }

    #[inline]
    fn is_one(&self) -> bool {
        self.0 == 1.0
    }

    fn approx_eq(&self, other: &Self, epsilon: f64) -> bool {
        (self.0 - other.0).abs() <= epsilon
    }
}

/// Higher probability = better (lower in ordering for Viterbi path selection).
/// Reversed from tropical: `Ord` is by *descending* probability so that
/// the `min` in generic algorithms selects the most probable.
impl Ord for ViterbiWeight {
    fn cmp(&self, other: &Self) -> Ordering {
        // Reverse: higher probability = "lower" (better)
        other.0.total_cmp(&self.0)
    }
}

impl Hash for ViterbiWeight {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.0.to_bits().hash(state);
    }
}

impl Default for ViterbiWeight {
    fn default() -> Self {
        Self::one()
    }
}

impl DetectableZero for ViterbiWeight {}
impl IdempotentSemiring for ViterbiWeight {}
impl CompleteSemiring for ViterbiWeight {}

impl StarSemiring for ViterbiWeight {
    /// `star(a) = 1.0`. The most probable repeated application is "do nothing"
    /// (probability 1.0), since `max(1.0, p, p², ...) = 1.0` for any `p ∈ [0,1]`.
    #[inline]
    fn star(&self) -> Self {
        ViterbiWeight(1.0)
    }
}
```

### Implementation Notes

- **`is_zero` is exact equality**: Unlike TropicalWeight (which must
  check for positive infinity specifically), `is_zero()` simply checks
  `self.0 == 0.0`.  This is safe because zero probability maps to
  exactly `0.0` in IEEE 754.

- **Reversed `Ord`**: `other.0.total_cmp(&self.0)` reverses the
  natural ordering so that higher probability = "lower" in the
  ordering.  This allows generic min-based shortest-path algorithms
  (written for TropicalWeight) to work unchanged with ViterbiWeight,
  selecting the most probable path instead of the cheapest.

- **`debug_assert!` on construction**: `new()` verifies the probability
  is in `[0, 1]` in debug builds, catching domain violations early
  without release-build overhead.

- **`Default = one()`**: A newly created weight represents "certain"
  (probability 1.0, the multiplicative identity), not "impossible"
  (probability 0.0, the additive identity).  This is the natural
  default for probability initialization before multiplying along
  paths.

---

## 12. Integration into PraTTaIL

ViterbiWeight integrates with PraTTaIL's pipeline through three
primary channels.

### 12.1 Recovery Confidence Scoring (recovery.rs)

Recovery strategies carry a ViterbiWeight expressing the confidence
that the repair is correct.  Higher probability means the strategy is
more likely to produce the intended parse tree:

```rust
// Recovery attempts sorted by confidence (Ord is reversed: max first)
recovery_candidates.sort_by_key(|r| r.confidence);
// candidates[0] has the highest probability -- tried first
```

### 12.2 Direct Probability I/O

ViterbiWeight enables round-trip conversion with external systems
that express weights as probabilities rather than log-costs:

```rust
// Import probability from external HMM
let external_prob = 0.73;
let w = ViterbiWeight::new(external_prob);

// Export back to probability for reporting
println!("Confidence: {:.1}%", w.probability() * 100.0);  // "Confidence: 73.0%"
```

### 12.3 TropicalWeight Bridge

The bidirectional `from_tropical()` / `to_tropical()` conversions
allow ViterbiWeight to participate in PraTTaIL's tropical-native
pipeline without loss of information:

```rust
let tropical = TropicalWeight::new(0.693);  // -ln(0.5)
let viterbi = ViterbiWeight::from_tropical(tropical);
// viterbi.probability() ≈ 0.5

let back = viterbi.to_tropical();
// back.value() ≈ 0.693
```

### 12.4 Token Lattice (lattice.rs)

The generic `TokenLattice<T, S, W>` can be instantiated with
`W = ViterbiWeight` for applications where probabilities are the
natural weight domain.  The `viterbi_generic::<W>()` function then
extracts the most-probable tokenization.

---

## 13. Source Reference & See Also

### Source Location

- **File**: `prattail/src/automata/semiring.rs`, lines 1924--2077
- **Struct**: `ViterbiWeight(pub f64)`
- **Trait impl**: `impl Semiring for ViterbiWeight` (lines 1982--2016)
- **Ordering**: `impl Ord for ViterbiWeight` via reversed `total_cmp` (lines 2047--2052)
- **Star**: `impl StarSemiring for ViterbiWeight` -- always returns 1.0 (lines 2070--2077)
- **Hashing**: `impl Hash for ViterbiWeight` via `f64::to_bits()` (lines 2054--2058)
- **Tests**: lines 3938--4012

### Cross-References

- [Semiring Algebra Overview](../semirings.md) -- Axiom
  definitions, classification, and comparison of all semirings
- [Tropical Weight Theory](tropical-weight.md) -- The dual log-domain
  semiring, isomorphic via `-ln` transform
- [Arctic Weight Theory](arctic-weight.md) -- Max-plus longest-path
  semiring
- [Counting Weight Theory](counting-weight.md) -- The counting semiring
  for ambiguity detection
- [Boolean Weight Theory](boolean-weight.md) -- Binary reachability
  semiring

### References

- Viterbi, A. (1967). "Error bounds for convolutional codes and an
  asymptotically optimum decoding algorithm." *IEEE Transactions on
  Information Theory*, 13(2), 260--269.
- Mohri, M. (2002). "Semiring frameworks and algorithms for
  shortest-distance problems." *Journal of Automata, Languages and
  Combinatorics*, 7(3), 321--350.
- Kuich, W. & Salomaa, A. (1986). *Semirings, Automata, Languages*.
  Springer-Verlag. EATCS Monographs on Theoretical Computer Science.
