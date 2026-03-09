# Fuzzy Semiring: FuzzyWeight

## 1. Intuition & Motivation

The fuzzy semiring provides a *possibilistic reasoning algebra* with
bottleneck semantics.  Unlike probability theory (where alternatives
sum and paths multiply), possibility theory uses `max` for alternatives
and `min` for sequential composition.  The "bottleneck" interpretation
is the key insight: the plausibility of a multi-step operation is
limited by its *least plausible step*.

The two fundamental operations map to reasoning about possibilities:

- **Selecting among alternatives** (parallel paths) uses `max` -- the
  most possible alternative dominates.
- **Chaining sequential segments** (a path through multiple arcs) uses
  `min` -- the weakest link constrains the entire chain.

Within PraTTaIL, the fuzzy semiring answers the question:

```
how plausible is this dispatch decision?
```

A dispatch arm with confidence degree 0.9 is more plausible than one
with 0.3.  When chaining two arms (e.g., category dispatch followed by
lookahead resolution), the combined plausibility is the minimum of the
two -- limited by the least confident step.  This models situations
where confidence is not probabilistic but possibilistic: each step
contributes an independent "degree of possibility" rather than a
probability that compounds multiplicatively.

---

## 2. Formal Definition

The fuzzy semiring is the algebraic structure

```
F  =  ( [0, 1],  max,  min,  0,  1 )
```

where:

| Component                   | Symbol | Concrete value | Meaning                                |
|-----------------------------|--------|----------------|----------------------------------------|
| Carrier set                 | K      | [0, 1]         | Degrees of possibility from 0 to 1     |
| Addition (⊕)                | max    | max(a, b)      | Select most possible alternative       |
| Multiplication (⊗)          | min    | min(a, b)      | Bottleneck: weakest link in chain      |
| Additive identity (0-bar)   | 0      | `0.0_f64`      | Impossible (identity for max)          |
| Multiplicative identity (1-bar) | 1  | `1.0_f64`      | Fully possible (identity for min)      |

The name "fuzzy" comes from Zadeh's fuzzy set theory (1965), where
`max` and `min` serve as the fundamental lattice operations on
membership degrees.  The fuzzy semiring is also known as the
*possibilistic semiring* or *Godel t-norm semiring* in the
many-valued logic literature.

---

## 3. Semiring Axiom Verification

We verify all eight semiring axioms with concrete numerical examples.
Let a = 0.7, b = 0.4, c = 0.9.

### (A1) Associativity of ⊕

```
(a ⊕  b) ⊕  c  =  max(max(0.7, 0.4), 0.9)  =  max(0.7, 0.9)  =  0.9
a ⊕  (b ⊕  c)  =  max(0.7, max(0.4, 0.9))  =  max(0.7, 0.9)  =  0.9   ✓
```

Holds in general because `max` is associative over totally ordered sets.

### (A2) Commutativity of ⊕

```
a ⊕  b  =  max(0.7, 0.4)  =  0.7
b ⊕  a  =  max(0.4, 0.7)  =  0.7   ✓
```

Holds because `max` is symmetric: `max(x, y) = max(y, x)` for all x, y.

### (A3) ⊕  Identity

```
0-bar ⊕  a  =  max(0.0, 0.7)  =  0.7  =  a   ✓
a ⊕  0-bar  =  max(0.7, 0.0)  =  0.7  =  a   ✓
```

Zero is the identity for `max` because every degree in `[0, 1]`
is at least 0.

### (M1) Associativity of ⊗

```
(a ⊗  b) ⊗  c  =  min(min(0.7, 0.4), 0.9)  =  min(0.4, 0.9)  =  0.4
a ⊗  (b ⊗  c)  =  min(0.7, min(0.4, 0.9))  =  min(0.7, 0.4)  =  0.4   ✓
```

Holds because `min` is associative over totally ordered sets.

### (M2) ⊗  Identity

```
1-bar ⊗  a  =  min(1.0, 0.7)  =  0.7  =  a   ✓
a ⊗  1-bar  =  min(0.7, 1.0)  =  0.7  =  a   ✓
```

One is the identity for `min` because every degree in `[0, 1]`
is at most 1.

### (D1) Left Distributivity: ⊗  distributes over ⊕  from the left

```
a ⊗  (b ⊕  c)  =  min(0.7, max(0.4, 0.9))  =  min(0.7, 0.9)  =  0.7
(a ⊗  b) ⊕  (a ⊗  c)  =  max(min(0.7, 0.4), min(0.7, 0.9))  =  max(0.4, 0.7)  =  0.7   ✓
```

In general: `min(x, max(y, z)) = max(min(x, y), min(x, z))` because
`(max, min)` forms a distributive lattice on any totally ordered set.

### (D2) Right Distributivity: ⊗  distributes over ⊕  from the right

```
(a ⊕  b) ⊗  c  =  min(max(0.7, 0.4), 0.9)  =  min(0.7, 0.9)  =  0.7
(a ⊗  c) ⊕  (b ⊗  c)  =  max(min(0.7, 0.9), min(0.4, 0.9))  =  max(0.7, 0.4)  =  0.7   ✓
```

Symmetric argument to (D1).

### (Z) Zero Annihilation

```
0-bar ⊗  a  =  min(0.0, 0.7)  =  0.0  =  0-bar   ✓
a ⊗  0-bar  =  min(0.7, 0.0)  =  0.0  =  0-bar   ✓
```

The minimum of any value with 0 is 0.  An impossible step makes the
entire chain impossible.

All eight axioms are satisfied. F is a valid semiring.

> For the parsing-specific interpretation of these axioms, see
> [4. Why Each Axiom Matters for Parsing](../semirings.md#4-why-each-axiom-matters-for-parsing).

---

## 4. Key Properties

### 4.1 Commutativity

**Claim**: The fuzzy semiring is commutative (⊗  is commutative).

**Proof**: For all a, b in [0, 1]:

```
a ⊗  b  =  min(a, b)  =  min(b, a)  =  b ⊗  a
```

`min` is symmetric on totally ordered sets.   ∎

Commutativity means the bottleneck constraint is independent of
direction -- the weakest link in A -> B -> C is the same as in
C -> B -> A.

### 4.2 Idempotency

**Claim**: The fuzzy semiring is idempotent (⊕  is idempotent).

**Proof**: For all a in [0, 1]:

```
a ⊕  a  =  max(a, a)  =  a
```

The maximum of any value with itself is that value.   ∎

Idempotency means that merging a path with itself does not change the
result -- precisely the semantics needed when we want the single most
possible alternative, not a possibility sum.

### 4.3 Idempotency of ⊗

**Claim**: The fuzzy semiring is *also* idempotent on ⊗ .

**Proof**: For all a in [0, 1]:

```
a ⊗  a  =  min(a, a)  =  a
```

Both operations are idempotent.   ∎

This double idempotency makes the fuzzy semiring a *bounded
distributive lattice* -- the strongest algebraic structure among
the semirings in PraTTaIL.  It implies that self-composition along
any path has no effect: running through the same arc twice does not
change the bottleneck.

### 4.4 Completeness and Star

**Claim**: FuzzyWeight is a complete star semiring.

**Proof**: For any a in [0, 1]:

```
star(a) = ⊕_{n=0}^{∞} a^n = max{1, a, min(a,a), min(a,a,a), ...}
        = max{1, a, a, a, ...}    (by ⊗-idempotency)
        = 1                        (because 1 ∈ [0,1] and max includes 1)
```

The implementation returns `FuzzyWeight(1.0)` unconditionally.   ∎

### 4.5 Total Ordering (Reversed)

FuzzyWeight implements `Ord` with **reversed** comparison:

```
Ordering logic:  other.0.total_cmp(&self.0)
```

Higher degree = "lower" in the ordering, so that generic min-based
algorithms select the most possible alternative.

---

## 5. Confidence Table

PraTTaIL uses FuzzyWeight to express *dispatch confidence* -- the
degree of possibility that a given dispatch decision is correct.
Unlike ViterbiWeight (probabilistic), FuzzyWeight confidence degrees
are independent possibilistic assessments.

### Confidence-to-Degree Table

| Dispatch Situation                 | FuzzyWeight | Meaning                                       |
|------------------------------------|-------------|-----------------------------------------------|
| Unique FIRST-set token             | 1.0         | Fully possible -- deterministic dispatch      |
| Cross-category with resolved cast  | 0.9         | Very plausible -- strong evidence             |
| Composed dispatch, 2 alternatives  | 0.7         | Plausible -- moderate ambiguity               |
| Lookahead-dependent, 3+ options    | 0.5         | Moderately plausible -- needs lookahead       |
| Fallback variable/identifier       | 0.3         | Weakly plausible -- highly ambiguous          |
| Dead rule                          | 0.0         | Impossible -- rule never fires                |

### Bottleneck Semantics for Multi-Step Dispatch

When a dispatch decision involves two steps (e.g., category
dispatch at confidence 0.9, followed by lookahead at confidence 0.7),
the combined confidence is the *bottleneck*:

```
combined = 0.9 ⊗  0.7 = min(0.9, 0.7) = 0.7
```

The chain is only as confident as its weakest link.  This is the
correct model when each step's confidence is an independent
possibilistic assessment rather than a probability.

### When to Use FuzzyWeight vs. ViterbiWeight

- **FuzzyWeight**: When confidences are *independent possibilistic
  degrees* -- each step's confidence is assessed independently, and
  the chain is limited by the weakest step (bottleneck).

- **ViterbiWeight**: When confidences are *probabilities* that
  compose multiplicatively -- each step's probability compounds along
  the path (0.9 * 0.7 = 0.63).

---

## 6. Zero Annihilation

The zero element `0.0` represents an *impossible* event.  Its
annihilation property guarantees that impossible paths remain
impossible regardless of concatenation:

```
0-bar ⊗  x  =  min(0.0, x)  =  0.0  =  0-bar     for all x ∈ [0, 1]
x ⊗  0-bar  =  min(x, 0.0)  =  0.0  =  0-bar     for all x ∈ [0, 1]
```

This is the correct semantic: if any step in a dispatch chain is
impossible (possibility 0.0), the entire chain is impossible.  No
high-confidence suffix can rescue a zero-confidence prefix.

In the implementation, `is_zero()` checks exact equality:

```rust
fn is_zero(&self) -> bool {
    self.0 == 0.0
}
```

---

## 7. Path Plausibility Computation

### Worked Example

Consider a 4-node dispatch graph for parsing category `Stmt` with two
alternative dispatch strategies upon seeing token `Ident`:

```
                        ┌─────────────────────────────────┐
                        │       Confidence Graph          │
                        │      (category: Stmt)           │
                        └─────────────────────────────────┘

  Path 1 (cast+match):    q₀ ──0.9──▶ q₁ ──0.4──▶ q₃
  Path 2 (direct):        q₀ ──0.7──▶ q₂ ──0.7──▶ q₃


         ┌──────┐    0.9     ┌──────┐
         │      │───────────▶│      │
         │  q₀  │            │  q₁  │──┐
         │      │            │      │  │  0.4
         └──────┘            └──────┘  │
            │                          │
            │                   ┌──────▼──────┐
            │  0.7              │             │
            │                   │     q₃      │
            │                   │   (accept)  │
            │                   └──────▲──────┘
            │                          │
            ▼                          │  0.7
         ┌──────┐                      │
         │      │──────────────────────┘
         │  q₂  │
         │      │
         └──────┘
```

**Path 1** (cast+match: cast to Expr, then match operator):

```
d₁  =  0.9 ⊗  0.4  =  min(0.9, 0.4)  =  0.4
```

Despite the strong first step (0.9), the weak second step (0.4)
constrains the chain.

**Path 2** (direct: direct dispatch with moderate confidence):

```
d₂  =  0.7 ⊗  0.7  =  min(0.7, 0.7)  =  0.7
```

Both steps are equally confident, so the chain confidence equals each
step.

**Selecting the best alternative** (⊕):

```
d*  =  d₁ ⊕  d₂  =  max(0.4, 0.7)  =  0.7
```

The dispatcher selects Path 2 (direct) because its bottleneck
confidence is higher, even though Path 1 has a stronger first step.

This illustrates the bottleneck semantics: a chain with one weak link
(0.4) is less plausible than a chain with consistently moderate links
(0.7, 0.7).

---

## 8. Dispatch Weight Table

The following confidence degrees are used in PraTTaIL's possibilistic
dispatch framework:

| Dispatch Type          | FuzzyWeight | Rationale                                                    |
|------------------------|-------------|--------------------------------------------------------------|
| Keyword exact match    | 1.0         | Deterministic -- fully possible                              |
| Structural delimiter   | 0.95        | Nearly deterministic -- `(`, `)`, `{`, `}`                   |
| Single-operator        | 0.9         | High confidence -- specific operator token                   |
| Cross-category cast    | 0.8         | Good confidence -- type system resolves ambiguity            |
| Composed dispatch      | 0.7         | Moderate -- 2 candidates, resolved by priority               |
| Multi-alternative      | 0.5         | Moderate -- 3+ candidates, needs lookahead                   |
| Identifier fallback    | 0.3         | Low -- most ambiguous token kind                             |
| Dead rule              | 0.0         | Impossible -- never fires                                    |

**Design principle**: Degrees are independent assessments of how
plausible each dispatch action is.  They do not sum to 1 (unlike
probabilities) and are combined via `min` (bottleneck) along paths.

---

## 9. Comparison with BooleanWeight and ViterbiWeight

The fuzzy semiring sits between Boolean (binary) and Viterbi
(probabilistic) in expressiveness:

| Property            | BooleanWeight              | FuzzyWeight                    | ViterbiWeight                  |
|---------------------|----------------------------|--------------------------------|--------------------------------|
| Carrier set         | {false, true}              | [0, 1]                         | [0, 1]                         |
| ⊕  (addition)       | ∨ (or)                     | max(a, b)                      | max(a, b)                      |
| ⊗  (multiplication) | ∧ (and)                    | min(a, b)                      | a * b                          |
| 0-bar (zero)        | false                      | 0.0                            | 0.0                            |
| 1-bar (one)         | true                       | 1.0                            | 1.0                            |
| Idempotent ⊕?       | Yes: a ∨ a = a             | Yes: max(a, a) = a             | Yes: max(a, a) = a             |
| Idempotent ⊗?       | Yes: a ∧ a = a             | Yes: min(a, a) = a             | No: a * a ≠ a in general       |
| Star?               | Yes: star(a) = true        | Yes: star(a) = 1.0             | Yes: star(a) = 1.0             |
| Interpretation      | Reachable or not           | Degree of possibility          | Probability of best path       |
| Use case            | Reachability analysis      | Confidence/plausibility        | Most-likely-path selection     |

### Fuzzy as Generalized Boolean

BooleanWeight is the degenerate case of FuzzyWeight where only the
extreme values {0, 1} are used.  The embedding `true -> 1.0`,
`false -> 0.0` is a semiring homomorphism:

```
φ(a ∨ b) = max(φ(a), φ(b))
φ(a ∧ b) = min(φ(a), φ(b))
```

FuzzyWeight enriches this with intermediate degrees, enabling
graduated confidence assessment.

### Fuzzy vs. Viterbi: Bottleneck vs. Product

The critical difference is in ⊗ :

```
Fuzzy:   0.9 ⊗  0.7 = min(0.9, 0.7) = 0.7   (bottleneck)
Viterbi: 0.9 ⊗  0.7 = 0.9 * 0.7 = 0.63      (product)
```

Fuzzy confidence does not compound -- a chain of strong links is only
as strong as its weakest.  Probabilistic confidence compounds
multiplicatively -- each step erodes the total probability.

---

## 10. Pseudocode: Bottleneck Path (Widest Path)

The bottleneck path algorithm finds the path with the maximum minimum
edge weight through a graph -- the "widest" path in a capacity
network.  Using fuzzy semiring operations, this becomes a standard
shortest-path algorithm.

```
ALGORITHM BottleneckPath(G, start, final)
────────────────────────────────────────────────────
  Input:  Graph G = (V, E, d) with nodes V, edges E, degree function d : E → [0,1]
          start node s ∈ V, final node f ∈ V
  Output: Widest (max-bottleneck) path from s to f, or IMPOSSIBLE

  1.  for each v ∈ V do
  2.      degree[v] ← 0.0                     // fuzzy zero: impossible
  3.      pred[v] ← NIL
  4.  degree[s] ← 1.0                         // fuzzy one: fully possible

  5.  Q ← priority queue of V ordered by degree (reversed: max first)
  6.  while Q is not empty do
  7.      u ← Q.extract_max()
  8.      for each edge (u, v, d_uv) ∈ E do
  9.          candidate ← degree[u] ⊗  d_uv    // = min(degree[u], d_uv)
 10.          if candidate ⊕  degree[v] ≠ degree[v] then  // max improves
 11.              degree[v] ← candidate ⊕  degree[v]      // = max(candidate, degree[v])
 12.              pred[v] ← u
 13.              Q.update_priority(v, degree[v])

 14.  if degree[f] = 0.0 then return IMPOSSIBLE

       // Backtrack to reconstruct path
 15.  path ← empty list
 16.  v ← f
 17.  while v ≠ s do
 18.      path.prepend(v)
 19.      v ← pred[v]
 20.  path.prepend(s)
 21.  return (path, degree[f])
```

**Complexity**: O((|V| + |E|) log |V|) with a binary heap priority
queue.

**Note**: Unlike tropical Viterbi (which requires a DAG for
O(|V| + |E|) complexity), the bottleneck path algorithm works on
general graphs because the fuzzy semiring satisfies `a ⊗  b >= min(a, b)`
-- no negative cycles are possible (all weights are in `[0, 1]` and
`min` can only decrease or maintain the bottleneck).

---

## 11. Rust Implementation

The following is the complete `FuzzyWeight` implementation from
`prattail/src/automata/semiring.rs`.

```rust
/// Fuzzy/possibilistic semiring `([0,1], max, min, 0, 1)`.
///
/// Confidence/possibility-degree reasoning. Unlike probability (which sums
/// to 1), fuzzy weights express independent "degree of possibility" in [0, 1].
///
/// `times = min` means the plausibility of a multi-step operation is limited
/// by its least plausible step (bottleneck semantics in possibility space).
///
/// - `plus = max`: selects the most possible alternative
/// - `times = min`: bottleneck -- multi-step possibility = weakest link
/// - `zero = 0.0`: impossible (identity for max)
/// - `one = 1.0`: fully possible (identity for min)
///
/// **Applications:**
/// - `prediction.rs`: dispatch confidence independent of probability
/// - `recovery.rs`: fuzzy "plausibility" of a recovery strategy
/// - `lint.rs`: true-positive likelihood of a diagnostic
#[derive(Clone, Copy)]
pub struct FuzzyWeight(pub f64);

impl FuzzyWeight {
    /// Create a fuzzy weight from a possibility degree in `[0, 1]`.
    #[inline]
    pub fn new(degree: f64) -> Self {
        debug_assert!(
            (0.0..=1.0).contains(&degree),
            "FuzzyWeight: degree must be in [0, 1], got {degree}"
        );
        FuzzyWeight(degree)
    }

    /// Get the possibility degree.
    #[inline]
    pub const fn degree(self) -> f64 {
        self.0
    }
}

impl Semiring for FuzzyWeight {
    #[inline]
    fn zero() -> Self {
        FuzzyWeight(0.0)
    }

    #[inline]
    fn one() -> Self {
        FuzzyWeight(1.0)
    }

    #[inline]
    fn plus(&self, other: &Self) -> Self {
        FuzzyWeight(self.0.max(other.0))
    }

    #[inline]
    fn times(&self, other: &Self) -> Self {
        FuzzyWeight(self.0.min(other.0))
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

/// Higher degree = better. Reversed ordering so generic shortest-path
/// algorithms select the most possible alternative.
impl Ord for FuzzyWeight {
    fn cmp(&self, other: &Self) -> Ordering {
        other.0.total_cmp(&self.0)
    }
}

impl Hash for FuzzyWeight {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.0.to_bits().hash(state);
    }
}

impl Default for FuzzyWeight {
    fn default() -> Self {
        Self::one()
    }
}

impl DetectableZero for FuzzyWeight {}
impl IdempotentSemiring for FuzzyWeight {}
impl CompleteSemiring for FuzzyWeight {}

impl StarSemiring for FuzzyWeight {
    /// `star(a) = 1.0`. Max possibility is always 1 (the empty path has
    /// full possibility): `max(1, a, min(a,a), ...) = 1.0` for any `a`.
    #[inline]
    fn star(&self) -> Self {
        FuzzyWeight(1.0)
    }
}
```

### Implementation Notes

- **`is_zero` is exact equality**: Checks `self.0 == 0.0`, which is
  safe because the zero degree maps to exactly `0.0` in IEEE 754.

- **Reversed `Ord`**: `other.0.total_cmp(&self.0)` reverses the
  natural ordering so that higher degree = "lower" in the ordering.
  This allows generic min-based algorithms to select the most possible
  alternative.

- **`debug_assert!` on construction**: `new()` verifies the degree is
  in `[0, 1]` in debug builds, catching domain violations early.

- **`Default = one()`**: A newly created weight represents "fully
  possible" (1.0, the multiplicative identity), not "impossible" (0.0,
  the additive identity).

- **Double idempotency**: Both `plus` (`max`) and `times` (`min`) are
  idempotent, making FuzzyWeight a bounded distributive lattice.  This
  is the strongest algebraic structure among PraTTaIL's semirings.

---

## 12. Integration into PraTTaIL

FuzzyWeight integrates with PraTTaIL's pipeline through three
primary subsystems.

### 12.1 Dispatch Confidence (prediction.rs)

The prediction module uses FuzzyWeight to assess dispatch confidence
independent of probability.  Each dispatch arm receives a fuzzy degree
expressing how plausible the dispatch target is:

```rust
// Dispatch arms sorted by fuzzy confidence (reversed Ord: max first)
dispatch_arms.sort_by_key(|arm| arm.fuzzy_confidence);
// arms[0] has the highest plausibility -- tried first
```

### 12.2 Recovery Plausibility (recovery.rs)

Recovery strategies carry a FuzzyWeight expressing how plausible the
repair is.  The bottleneck semantics ensure that a multi-step recovery
is only as plausible as its weakest step:

```rust
// Two-step recovery: insert + substitute
let insert_confidence = FuzzyWeight::new(0.8);
let substitute_confidence = FuzzyWeight::new(0.6);
let combined = insert_confidence.times(&substitute_confidence);
// combined = min(0.8, 0.6) = 0.6 -- limited by substitute step
```

### 12.3 Diagnostic True-Positive Likelihood (lint.rs)

The lint layer uses FuzzyWeight to express how likely a diagnostic is
to be a true positive.  A lint with degree 0.9 is very likely correct;
one with degree 0.3 may be a false positive:

```rust
// Filter diagnostics by confidence threshold
let threshold = FuzzyWeight::new(0.5);
diagnostics.retain(|d| d.confidence.cmp(&threshold) != Ordering::Greater);
// Keep only diagnostics with confidence >= 0.5
```

### 12.4 Token Lattice (lattice.rs)

The generic `TokenLattice<T, S, W>` can be instantiated with
`W = FuzzyWeight` for possibilistic lattice disambiguation, where
the widest (max-bottleneck) path is extracted as the most plausible
tokenization.

---

## 13. Source Reference & See Also

### Source Location

- **File**: `prattail/src/automata/semiring.rs`, lines 2245--2380
- **Struct**: `FuzzyWeight(pub f64)`
- **Trait impl**: `impl Semiring for FuzzyWeight` (lines 2287--2321)
- **Ordering**: `impl Ord for FuzzyWeight` via reversed `total_cmp` (lines 2351--2355)
- **Star**: `impl StarSemiring for FuzzyWeight` -- always returns 1.0 (lines 2373--2380)
- **Hashing**: `impl Hash for FuzzyWeight` via `f64::to_bits()` (lines 2357--2361)
- **Tests**: lines 4095--4153

### Cross-References

- [Semiring Algebra Overview](../semirings.md) -- Axiom
  definitions, classification, and comparison of all semirings
- [Boolean Weight Theory](boolean-weight.md) -- Binary reachability
  (degenerate case of fuzzy with only {0, 1})
- [Viterbi Weight Theory](viterbi-weight.md) -- Probabilistic
  most-likely-path (multiplicative rather than bottleneck)
- [Tropical Weight Theory](tropical-weight.md) -- Cost-based
  shortest-path semiring
- [Counting Weight Theory](counting-weight.md) -- Ambiguity counting

### References

- Zadeh, L. A. (1965). "Fuzzy sets." *Information and Control*, 8(3),
  338--353.
- Dubois, D. & Prade, H. (1988). *Possibility Theory: An Approach to
  Computerized Processing of Uncertainty*. Plenum Press.
- Droste, M., Kuich, W., & Vogler, H. (2009). *Handbook of Weighted
  Automata*. Springer. Chapter 12: Fuzzy and possibilistic semirings.
- Mohri, M. (2002). "Semiring frameworks and algorithms for
  shortest-distance problems." *Journal of Automata, Languages and
  Combinatorics*, 7(3), 321--350.
