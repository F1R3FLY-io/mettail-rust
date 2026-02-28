# Log Semiring: Probabilistic Weighted Parsing

## 1. Intuition & Motivation

The tropical semiring answers the question *"what is the single best parse?"*
but discards all information about alternatives. For many applications, we need
to reason about the **distribution** over all possible parses:

- **Weight training** requires computing the gradient of the log-likelihood,
  which involves the partition function Z = sum of all path probabilities.
- **Posterior probabilities** require the ratio P(path) / Z, computed via the
  forward-backward algorithm.
- **N-best extraction** needs ranked alternatives, not just the single best.
- **Beam pruning** is only optimal when edge weights are locally normalized,
  which requires probability-preserving weight pushing.

All of these require a semiring where ⊕ **sums probabilities** rather than
selecting the minimum. The log semiring provides exactly this capability by
working in the negative-log-probability domain, where probability addition
becomes the numerically stable `log-sum-exp` operation.

```
  ┌──────────────────────────────────────────────────────────┐
  │  Tropical: "Which path is best?"   ⊕ = min              │
  │  Log:      "What is the total?"    ⊕ = log-sum-exp      │
  │                                                          │
  │  Same ⊗ = addition (probability multiplication)          │
  │  Same algorithms (Viterbi, forward-backward, beam)       │
  │  Different semantics from one algebraic swap             │
  └──────────────────────────────────────────────────────────┘
```

---

## 2. Formal Definition

### 2.1 The Semiring

The **log semiring** is the tuple:

```
S_log = (R+ u {+inf},  log-sum-exp,  +,  +inf,  0.0)
```

where:

| Component          | Symbol | Definition                                    | Interpretation                       |
|--------------------|--------|-----------------------------------------------|--------------------------------------|
| Carrier set        | K      | R+ u {+inf} = [0, +inf]                      | Negative log probabilities           |
| Addition (⊕)       | lse    | lse(a, b) = -ln(exp(-a) + exp(-b))           | Sum probabilities                    |
| Multiplication (⊗) | +      | a + b                                         | Multiply probabilities               |
| Additive identity  | 0      | +inf                                          | Probability 0 (impossible)           |
| Multiplicative id  | 1      | 0.0                                           | Probability 1 (certain)              |

### 2.2 Negative Log Probability Encoding

Each weight w in K encodes a probability p via:

```
w = -ln(p)       equivalently       p = exp(-w)
```

This encoding maps the probability interval (0, 1] to the weight interval
[0, +inf), with probability 0 mapped to weight +inf. Lower weight means
higher probability.

### 2.3 Why Negative Log?

Working in negative-log space converts:
- Probability multiplication (p1 * p2) into **addition** (w1 + w2)
- Probability addition (p1 + p2) into **log-sum-exp** (lse(w1, w2))

Addition is cheaper and more numerically stable than multiplication of small
floats. The log-sum-exp operation (Section 6) provides a numerically stable
implementation of the more expensive probability summation.

---

## 3. Semiring Axiom Verification

### 3.1 (A1) Associativity of ⊕

We must show: lse(lse(a, b), c) = lse(a, lse(b, c)).

In probability space, lse corresponds to addition:

```
lse(a, b)  maps to  exp(-a) + exp(-b)  =  p_a + p_b
```

Since real addition is associative:

```
(p_a + p_b) + p_c  =  p_a + (p_b + p_c)
```

Applying -ln to both sides preserves equality:

```
-ln((p_a + p_b) + p_c)  =  -ln(p_a + (p_b + p_c))
```

The left side is lse(lse(a, b), c) and the right is lse(a, lse(b, c)). QED

### 3.2 (A2) Commutativity of ⊕

```
lse(a, b) = -ln(exp(-a) + exp(-b)) = -ln(exp(-b) + exp(-a)) = lse(b, a)
```

This follows directly from commutativity of real addition. QED

### 3.3 (A3) Additive Identity

```
lse(+inf, a) = -ln(exp(-inf) + exp(-a)) = -ln(0 + exp(-a)) = -ln(exp(-a)) = a
```

Since exp(-inf) = 0, the zero element +inf acts as the identity for lse. QED

### 3.4 (M1) Associativity of ⊗

```
(a + b) + c = a + (b + c)
```

This is the associativity of real addition. QED

### 3.5 (M2) Multiplicative Identity

```
0.0 + a = a + 0.0 = a
```

Since 0.0 is the additive identity for real numbers. QED

### 3.6 (D1) Left Distributivity: a ⊗ (b ⊕ c) = (a ⊗ b) ⊕ (a ⊗ c)

In probability space:

```
Left side:   p_a * (p_b + p_c)
Right side:  (p_a * p_b) + (p_a * p_c) = p_a * (p_b + p_c)
```

This is the distributivity of real multiplication over real addition.
Converting back to log space preserves equality. QED

Right-distributivity (D2) follows symmetrically.

### 3.7 (Z) Zero Annihilation

```
+inf + a = +inf    and    a + +inf = +inf
```

In the extended reals with our convention, adding any finite value to +inf
yields +inf. In probability space: 0 * p = 0, which maps to -ln(0) = +inf. QED

---

## 4. Key Properties

### 4.1 Commutativity

The log semiring is **commutative**: a ⊗ b = a + b = b + a = b ⊗ a. QED

### 4.2 Non-Idempotency

The log semiring is **NOT idempotent**. This is the critical distinction from
the tropical semiring.

**Proof.** Let a be any finite weight in K. Then:

```
a ⊕ a = lse(a, a)
      = -ln(exp(-a) + exp(-a))
      = -ln(2 * exp(-a))
      = -ln(2) - ln(exp(-a))
      = -ln(2) + a
      = a - ln(2)
```

Since ln(2) ~ 0.6931 > 0, we have a - ln(2) < a, so a ⊕ a != a for any
finite a. QED

**Interpretation.** If two paths each carry probability p, combining them
yields probability 2p (not p). In log space, -ln(2p) = -ln(p) - ln(2),
which is strictly less than -ln(p). The combined weight is lower (better)
because more probability mass is concentrated.

This non-idempotency is precisely what makes the log semiring suitable for
computing partition functions and training: it correctly accounts for the
contribution of every path, not just the best one.

### 4.3 Probability Mass Preservation

The log semiring preserves the fundamental identity:

```
SUM over all paths pi:  exp(-weight(pi)) = Z
```

where Z is the partition function. This is guaranteed by the homomorphism
between (R+, +, *) and (R+ u {+inf}, lse, +).

---

## 5. Probability Correspondence

### 5.1 Conversion Functions

```rust
impl LogWeight {
    pub fn from_probability(p: f64) -> Self {
        assert!(p > 0.0);
        LogWeight(-p.ln())
    }

    pub fn to_probability(self) -> f64 {
        (-self.0).exp()
    }
}
```

### 5.2 Reference Table

| Weight w       | Probability p = exp(-w)  | Interpretation              |
|----------------|--------------------------|------------------------------|
| 0.0            | 1.0                      | Certain                      |
| 0.6931 (ln 2)  | 0.5                      | Fair coin flip               |
| 1.0            | 0.3679                   | Moderate                     |
| 2.3026 (ln 10) | 0.1                      | Unlikely                     |
| 4.6052 (ln 100)| 0.01                     | Very unlikely                |
| 6.9078 (ln 1000)| 0.001                   | Rare                         |
| +inf           | 0.0                      | Impossible                   |

### 5.3 Useful Identities

```
from_probability(p1 * p2)  =  from_probability(p1) ⊗ from_probability(p2)
                            =  -ln(p1) + (-ln(p2))

from_probability(p1 + p2)  =  from_probability(p1) ⊕ from_probability(p2)
                            =  lse(-ln(p1), -ln(p2))
```

These follow directly from the homomorphism between probability space and
log space.

---

## 6. Numerical Stability

### 6.1 The Naive Overflow Problem

A direct implementation of lse(a, b) = -ln(exp(-a) + exp(-b)) suffers from
overflow and underflow:

```
exp(-a) for a = -1000  =>  exp(1000)  =>  +inf   (overflow)
exp(-a) for a = 1000   =>  exp(-1000) =>  0.0    (underflow)
```

Even when neither term overflows individually, the sum exp(-a) + exp(-b)
can overflow when both a are large negative numbers.

### 6.2 The Stable Form

The standard stabilization technique factors out the dominant term:

```
lse(a, b) = min(a, b) - ln(1 + exp(-|a - b|))
```

**Derivation.** Without loss of generality, assume a <= b (so min(a,b) = a):

```
-ln(exp(-a) + exp(-b))
  = -ln(exp(-a) * (1 + exp(-b + a)))
  = -ln(exp(-a)) - ln(1 + exp(-(b - a)))
  = a - ln(1 + exp(-(b - a)))
  = min(a, b) - ln(1 + exp(-|a - b|))
```

In this form:
- The `min(a, b)` term never overflows (it is just a comparison).
- The exponent `-|a - b|` is always non-positive, so exp(-|a - b|) is in
  (0, 1], and 1 + exp(-|a - b|) is in (1, 2]. No overflow.
- ln(x) for x in (1, 2] is well-conditioned.

### 6.3 Fast Path: Threshold at |a - b| > 20

When |a - b| > 20:

```
exp(-20) = 2.061 x 10^-9
ln(1 + 2.061 x 10^-9) = 2.061 x 10^-9   (to first order)
```

The correction term is less than 2.1 x 10^-9, well below the precision of
f64 (approximately 1.1 x 10^-16 relative error at unit scale). PraTTaIL
drops the correction entirely in this case, returning `min(a, b)` directly.

This fast path avoids the exp() and ln() computations for well-separated
weights, which is the common case in parsing (most token alternatives have
very different probabilities).

### 6.4 Implementation

```rust
impl LogWeight {
    #[inline]
    fn log_sum_exp(a: f64, b: f64) -> f64 {
        // Handle infinities (zero elements)
        if a == f64::INFINITY { return b; }
        if b == f64::INFINITY { return a; }

        let min_val = a.min(b);
        let diff = (a - b).abs();

        if diff > 20.0 {
            min_val              // fast path: correction < 2e-9
        } else {
            min_val - (1.0 + (-diff).exp()).ln()
        }
    }
}
```

### 6.5 Error Analysis

For the slow path (|a - b| <= 20), the relative error is bounded by the
machine epsilon of f64 (~2.2 x 10^-16), since all intermediate computations
involve well-conditioned functions on bounded inputs.

For the fast path (|a - b| > 20), the absolute error is bounded by:

```
|error| = ln(1 + exp(-|a - b|)) < exp(-20) < 2.1 x 10^-9
```

This is acceptable for all parsing applications, where weight differences
below 10^-6 are treated as equal by `approx_eq`.

---

## 7. Worked Example: Tropical vs Log Semiring

### 7.1 Setup

Consider a 4-node DAG with two paths:

```
  ┌───┐  1.0   ┌───┐  1.5   ┌───┐
  │ 0 │───────>│ 1 │───────>│ 3 │   Path A: weight 1.0 + 1.5 = 2.5
  └───┘        └───┘        └───┘
    │                          ^
    │   2.0    ┌───┐   1.0    │
    └─────────>│ 2 │──────────┘     Path B: weight 2.0 + 1.0 = 3.0
               └───┘
```

### 7.2 Under TropicalWeight

```
forward[0] = 0.0    (one)
forward[1] = 0.0 + 1.0 = 1.0
forward[2] = 0.0 + 2.0 = 2.0
forward[3] = min(1.0 + 1.5, 2.0 + 1.0) = min(2.5, 3.0) = 2.5

Result: best path weight = 2.5 (Path A wins)
```

### 7.3 Under LogWeight

```
forward[0] = 0.0    (one)
forward[1] = 0.0 + 1.0 = 1.0
forward[2] = 0.0 + 2.0 = 2.0
forward[3] = lse(1.0 + 1.5, 2.0 + 1.0) = lse(2.5, 3.0)
```

Computing lse(2.5, 3.0):

```
min(2.5, 3.0) = 2.5
|2.5 - 3.0| = 0.5
correction = ln(1 + exp(-0.5)) = ln(1 + 0.6065) = ln(1.6065) = 0.4741

lse(2.5, 3.0) = 2.5 - 0.4741 = 2.026
```

Verification in probability space:

```
Path A probability: exp(-2.5) = 0.08209
Path B probability: exp(-3.0) = 0.04979
Total probability:  0.08209 + 0.04979 = 0.13188
-ln(0.13188) = 2.026   (matches)
```

### 7.4 Interpretation

| Semiring     | forward[3] | Probability Interpretation             |
|-------------|------------|----------------------------------------|
| Tropical    | 2.5        | Best path has probability exp(-2.5) = 0.082 |
| Log         | 2.026      | Total probability of all paths = exp(-2.026) = 0.132 |

The log-semiring result (2.026) is **lower** than the tropical result (2.5)
because both paths contribute probability mass. The total probability 0.132 >
0.082 because Path B adds its 0.050 contribution. This is precisely the
partition function Z = 0.132.

---

## 8. Forward-Backward Algorithm

### 8.1 Purpose

The forward-backward algorithm computes, for each edge in the lattice, the
**posterior probability** -- the fraction of total probability mass that flows
through that edge. These posteriors are used for:

- Expected rule counts in training
- Confidence scoring for individual parse decisions
- Identifying low-confidence regions for error messages

### 8.2 Forward Pass

Compute alpha[node] = total weight of all paths from start to node:

```
FUNCTION forward_scores(edges, num_nodes) -> Vec<LogWeight>
  alpha := [LogWeight::zero(); num_nodes]     // all +inf (probability 0)
  alpha[0] := LogWeight::one()                // 0.0 (probability 1)

  FOR node IN 0..num_nodes DO
    IF alpha[node].is_zero() THEN CONTINUE
    FOR (target, weight) IN edges[node] DO
      contribution := alpha[node] ⊗ weight    // log: alpha + w
      alpha[target] := alpha[target] ⊕ contribution  // log: lse
```

### 8.3 Backward Pass

Compute beta[node] = total weight of all paths from node to final:

```
FUNCTION backward_scores(edges, num_nodes, final_node) -> Vec<LogWeight>
  beta := [LogWeight::zero(); num_nodes]
  beta[final_node] := LogWeight::one()

  FOR node IN (0..num_nodes).rev() DO
    FOR (target, weight) IN edges[node] DO
      contribution := weight ⊗ beta[target]
      beta[node] := beta[node] ⊕ contribution
```

### 8.4 Edge Posteriors

The posterior probability of edge (u, v, w) is:

```
P(edge) = exp(-(alpha[u] + w + beta[v])) / Z

where Z = exp(-alpha[final_node]) = exp(-beta[0])
```

In log space:

```
-ln(P(edge)) = alpha[u] + w + beta[v] - alpha[final_node]
```

### 8.5 Consistency Check

For a correctly constructed DAG:

```
alpha[final_node] = beta[0]
```

Both represent the total weight (partition function) of all paths through the
lattice. This identity provides a useful sanity check.

### 8.6 Source Reference

See `prattail/src/forward_backward.rs` for the implementation. The module
provides `forward_scores()`, `backward_scores()`, and `total_weight()`,
all generic over `W: Semiring`.

---

## 9. Weight Training

### 9.1 Overview

PraTTaIL supports learning grammar rule weights from a corpus of parsed
examples via stochastic gradient descent (SGD). The training loop uses the
log semiring to compute gradients efficiently.

### 9.2 Loss Function

For each training example, the loss is:

```
L = -ln(P(correct parse) / P(all parses))
  = -ln(P(correct)) + ln(Z)
  = weight(correct) - total_weight

where:
  weight(correct) = sum of rule weights along the correct parse path
  total_weight = forward[final_node] (log-sum-exp of all path weights)
```

This is the **conditional log-likelihood**: we want to maximize the probability
of the correct parse relative to all possible parses.

### 9.3 Gradient

For each rule r, the gradient is:

```
dL/dw_r = expected_count(r, correct) - expected_count(r, all)
```

where:
- `expected_count(r, correct)` = number of times rule r appears in the correct parse
- `expected_count(r, all)` = expected number of times rule r appears across all
  parses, weighted by their posterior probabilities

The latter is computed via forward-backward: for each edge labeled with rule r,
sum its posterior probability.

### 9.4 SGD Update

```
w_r := w_r - lr * (expected_count(r, correct) - expected_count(r, all))
w_r := max(w_r, 0.0)       // clamp to non-negative (valid probability)
```

If rule r appears **more** in correct parses than expected under the current
model, the gradient is positive and the weight decreases (probability
increases). This pushes the model toward assigning higher probability to the
correct parse.

### 9.5 Pseudocode

```
FUNCTION train(rule_weights, examples, epochs) -> TrainingStats
  FOR epoch IN 1..epochs DO
    epoch_loss := 0.0
    FOR example IN examples DO
      correct_weight := SUM(rule_weights[r] for r in example.correct_rules)
      total_weight := forward_backward_total(lattice)
      loss := correct_weight - total_weight
      epoch_loss += loss

      expected_correct := count(example.correct_rules)
      expected_all := forward_backward_edge_posteriors(lattice)
      rule_weights.update(expected_correct, expected_all, learning_rate)

    record epoch_loss / |examples|

  RETURN TrainingStats { epoch_losses, converged }
```

### 9.6 Trained Model Serialization

After training, rule weights are exported as a `TrainedModel` and serialized
to postcard binary format. This model can be embedded in generated parsers via
the `log_semiring_model_path` DSL option.

### 9.7 Source Reference

See `prattail/src/training.rs` for `RuleWeights`, `TrainedModel`,
`TrainingStats`, and the `train()` method.

---

## 10. Log-Pushing (Weight Normalization)

### 10.1 Motivation

Beam pruning discards lattice paths whose weight exceeds the best weight by
more than a beam width threshold. But the meaning of "how far behind" depends
on the local weight distribution. An unnormalized WFST may have states where
all outgoing edges have large weights (shifting the baseline) and states where
weights are small. A fixed beam width cannot be optimal for both.

**Weight pushing** (Mohri et al., 2002) normalizes outgoing edge weights at
each state so that they sum to probability 1.0. After pushing, the beam
threshold has consistent meaning across all states.

### 10.2 Algorithm

```
FUNCTION log_push_weights(edges, num_nodes, final_node)
  // Step 1: Compute backward potentials
  beta := backward_scores(edges, num_nodes, final_node)

  // Step 2: Adjust each edge weight
  FOR p IN 0..num_nodes DO
    IF beta[p].is_zero() THEN CONTINUE     // unreachable
    FOR edge (p -> q, weight w) IN edges[p] DO
      IF beta[q].is_zero() THEN CONTINUE   // target unreachable
      w' := w + beta[q].value() - beta[p].value()
      edge.weight := LogWeight::new(w')
```

### 10.3 Correctness

After pushing, at each state p with outgoing edges {q1, ..., qk}:

```
SUM_i exp(-w'_i) = SUM_i exp(-(w_i + beta[q_i] - beta[p]))
                 = exp(beta[p]) * SUM_i exp(-w_i - beta[q_i])
                 = exp(beta[p]) * exp(-beta[p])    [by definition of beta]
                 = 1.0
```

The outgoing probabilities sum to 1.0 at every state.

### 10.4 Path Weight Preservation

Log-pushing does not change the total weight of any start-to-end path. For a
path p0 -> p1 -> ... -> pn:

```
SUM_i w'_i = SUM_i (w_i + beta[p_{i+1}] - beta[p_i])
           = SUM_i w_i + beta[pn] - beta[p0]
           = SUM_i w_i + 0.0 - beta[p0]       [beta[final] = one() = 0]
```

The constant offset beta[p0] is the same for all paths, so the relative
ordering is preserved. The best path remains the best path.

### 10.5 Source Reference

See `prattail/src/log_push.rs` for `log_push_weights()` and
`check_normalization()`.

---

## 11. Feature Gate

The log semiring and its associated modules are gated behind the `wfst-log`
Cargo feature:

```toml
[features]
wfst-log = ["serde", "postcard"]
```

### 11.1 What is Gated

| Module               | Feature Gate  | Purpose                          |
|----------------------|---------------|----------------------------------|
| `LogWeight`          | `wfst-log`    | Negative-log-probability weights |
| `forward_backward.rs`| `wfst-log`*  | Forward-backward scoring         |
| `log_push.rs`        | `wfst-log`    | Mohri weight normalization       |
| `training.rs`        | `wfst-log`    | SGD training loop + serialization|
| N-best paths         | `wfst-log`    | k-best path enumeration          |
| `with_trained_weights()`| `wfst-log` | Load trained weights at runtime  |

*Note: `forward_backward.rs` is generic over `W: Semiring` and compiles
without `wfst-log`, but its LogWeight-specific tests are gated. The
`log_push.rs` module imports `LogWeight` directly and requires the feature.

### 11.2 Why Feature-Gated

- **Dependency cost.** `training.rs` requires `serde` and `postcard` for
  model serialization. These are unnecessary for the majority of PraTTaIL
  users who only need TropicalWeight dispatch.
- **Compile time.** The training loop and serialization infrastructure add
  measurable compile time. Gating behind a feature keeps the default build
  fast (55s clean build target).
- **Experimental status.** The training pipeline is functional but
  experimental. Feature gating makes this clear to users.

---

## 12. Comparison with TropicalWeight

| Property             | TropicalWeight                | LogWeight                         |
|----------------------|-------------------------------|-----------------------------------|
| Carrier              | R+ u {+inf}                   | R+ u {+inf}                       |
| ⊕ (plus)             | min(a, b)                     | -ln(exp(-a) + exp(-b))            |
| ⊗ (times)            | a + b                         | a + b                             |
| 0 (zero)             | +inf                          | +inf                              |
| 1 (one)              | 0.0                           | 0.0                               |
| Idempotent?          | **Yes**: min(a,a) = a          | **No**: lse(a,a) = a - ln(2)     |
| Use case             | Best-path (Viterbi)           | Sum-over-paths (forward-backward) |
| Training?            | No (no gradients)             | Yes (expected counts via FB)      |
| Numerical complexity | Trivial (min, add)            | Moderate (exp, ln, stable form)   |
| Feature gate         | Always available               | `wfst-log`                        |

### 12.1 The Critical Distinction: Idempotency

The algebraic difference between the two semirings is exactly one axiom:

```
Tropical:  a ⊕ a = min(a, a) = a           (idempotent)
Log:       a ⊕ a = lse(a, a) = a - ln(2)   (NOT idempotent)
```

This single difference changes the semantics of every algorithm:

| Algorithm        | Tropical semantics               | Log semantics                    |
|------------------|----------------------------------|----------------------------------|
| Forward scores   | Min-cost path to each node       | Total probability to each node   |
| Backward scores  | Min-cost path from each node     | Total probability from each node |
| Forward[final]   | Viterbi best path weight         | Partition function Z             |
| Beam pruning     | Prune paths worse than best + B  | Prune paths below P * exp(-B)   |

### 12.2 Same ⊗, Different ⊕

Both semirings use real addition for ⊗. This means path weights are computed
identically -- a path that costs 2.5 under TropicalWeight also costs 2.5 under
LogWeight. The difference appears only when **combining alternatives** (⊕):
Tropical picks the winner, Log sums all contributions.

---

## 13. Rust Implementation

The full implementation from `prattail/src/automata/semiring.rs` (lines 626-814):

```rust
/// Log semiring weight: `(R+ union {+inf}, log-sum-exp, +, +inf, 0.0)`.
///
/// Represents negative log probabilities: `w = -ln(p)`.
#[cfg(feature = "wfst-log")]
#[derive(Clone, Copy)]
pub struct LogWeight(pub f64);

#[cfg(feature = "wfst-log")]
impl LogWeight {
    #[inline]
    pub const fn new(value: f64) -> Self {
        LogWeight(value)
    }

    #[inline]
    pub const fn value(self) -> f64 {
        self.0
    }

    /// Create from a probability p in (0, 1].
    /// w = -ln(p). Panics if p <= 0.
    #[inline]
    pub fn from_probability(p: f64) -> Self {
        assert!(p > 0.0, "LogWeight::from_probability: p must be > 0, got {p}");
        LogWeight(-p.ln())
    }

    /// Convert back to a probability: p = exp(-w).
    #[inline]
    pub fn to_probability(self) -> f64 {
        (-self.0).exp()
    }

    /// Numerically stable log-sum-exp: -ln(exp(-a) + exp(-b)).
    ///
    /// Uses: lse(a, b) = min(a, b) - ln(1 + exp(-|a-b|)).
    /// For |a-b| > 20, the correction term < 2e-9 and is dropped.
    #[inline]
    fn log_sum_exp(a: f64, b: f64) -> f64 {
        if a == f64::INFINITY { return b; }  // 0 ⊕ b = b
        if b == f64::INFINITY { return a; }  // a ⊕ 0 = a

        let min_val = a.min(b);
        let diff = (a - b).abs();

        if diff > 20.0 {
            min_val                              // fast path: correction < 2e-9
        } else {
            min_val - (1.0 + (-diff).exp()).ln() // stable form
        }
    }

    #[inline]
    pub const fn infinity() -> Self { LogWeight(f64::INFINITY) }

    #[inline]
    pub fn is_infinite(self) -> bool {
        self.0.is_infinite() && self.0.is_sign_positive()
    }
}

#[cfg(feature = "wfst-log")]
impl Semiring for LogWeight {
    #[inline] fn zero() -> Self { LogWeight(f64::INFINITY) }
    #[inline] fn one()  -> Self { LogWeight(0.0) }

    #[inline]
    fn plus(&self, other: &Self) -> Self {
        LogWeight(Self::log_sum_exp(self.0, other.0))
    }

    #[inline]
    fn times(&self, other: &Self) -> Self {
        LogWeight(self.0 + other.0)
    }

    #[inline]
    fn is_zero(&self) -> bool {
        self.0.is_infinite() && self.0.is_sign_positive()
    }

    #[inline]
    fn is_one(&self) -> bool { self.0 == 0.0 }

    fn approx_eq(&self, other: &Self, epsilon: f64) -> bool {
        if self.is_zero() && other.is_zero() { true }
        else if self.is_zero() || other.is_zero() { false }
        else { (self.0 - other.0).abs() <= epsilon }
    }
}
```

### 13.1 Ordering and Hashing

```rust
#[cfg(feature = "wfst-log")]
impl Ord for LogWeight {
    fn cmp(&self, other: &Self) -> Ordering {
        self.0.total_cmp(&other.0)     // NaN-safe total ordering
    }
}

#[cfg(feature = "wfst-log")]
impl Hash for LogWeight {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.0.to_bits().hash(state);  // bit-level hashing for f64
    }
}
```

Both `Ord` and `Hash` use `f64::total_cmp` / `to_bits()` to handle NaN and
negative zero correctly, ensuring consistent behavior in hash maps and sorted
containers.

### 13.2 Display

```rust
#[cfg(feature = "wfst-log")]
impl fmt::Display for LogWeight {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.is_zero() { write!(f, "inf") }
        else { write!(f, "{:.4}", self.0) }
    }
}
```

Display shows 4 decimal places for finite weights and "inf" for zero elements.

---

## 14. Integration into PraTTaIL

### 14.1 Training Pipeline

The typical workflow:

```
  1. Define grammar with language! { ... }
  2. Collect training corpus of (input, expected_parse) pairs
  3. Train:
       let mut weights = RuleWeights::uniform(&rule_labels);
       let stats = weights.train(&examples, 100);
       let model = weights.to_trained_model(&stats);
       model.save("model.bin")?;

  4. Configure DSL:
       language! {
           options {
               beam_width: auto
               log_semiring_model_path: "model.bin"
           }
           ...
       }

  5. At compile time, generated code loads the model:
       static TRAINED_MODEL: LazyLock<TrainedModel> = LazyLock::new(|| {
           TrainedModel::from_embedded(include_bytes!("model.bin"))
               .expect("embedded model")
       });
```

### 14.2 LogWeight to TropicalWeight Conversion

At WFST construction time, trained LogWeight values are converted to
TropicalWeight for runtime dispatch. Since both semirings use the same
numerical representation (non-negative f64 with +inf as zero), the conversion
is a direct value transfer:

```rust
impl PredictionWfst {
    #[cfg(feature = "wfst-log")]
    pub fn with_trained_weights(&mut self, model: &TrainedModel) {
        for (idx, action) in self.actions.iter_mut().enumerate() {
            let label = action.rule_label();
            if let Some(&trained_w) = model.rule_weights.get(label) {
                action.weight = TropicalWeight::new(trained_w);
                // Also update corresponding transition
                self.states[self.start as usize]
                    .transitions[idx].weight = TropicalWeight::new(trained_w);
            }
        }
    }
}
```

The numeric value is preserved -- a LogWeight of 0.5 becomes a TropicalWeight
of 0.5. The semantic interpretation changes (from "negative log probability"
to "arbitrary cost"), but the numerical ranking is identical. Lower weight
still means higher priority.

### 14.3 Beam Width from Training

The training process automatically computes a recommended beam width:

```
beam_width = max(correct_weight - best_weight) + safety_margin
```

This ensures the beam is wide enough to include the correct parse for all
training examples, with a configurable safety margin (default 0.5) for
unseen inputs.

---

## 15. Source Reference & See Also

### Source Files

- `prattail/src/automata/semiring.rs` -- LogWeight definition (lines 626-814)
- `prattail/src/forward_backward.rs` -- Forward-backward algorithm
- `prattail/src/log_push.rs` -- Mohri weight pushing
- `prattail/src/training.rs` -- SGD training loop, RuleWeights, TrainedModel

### Related Theory Documents

- [Semiring Algebra for Weighted Parsing](../semirings.md)
  -- the Semiring trait, axiom definitions, TropicalWeight
- [Product Semiring Theory](./product-weight.md) -- ProductWeight for
  multi-objective optimization
- [Viterbi, Forward-Backward, and N-Best Paths](../viterbi-and-forward-backward.md)
  -- algorithms parameterized over semirings

### Related Design Documents

- [Weight Training Design](../../../design/wfst/weight-training.md)
  -- training pipeline architecture
- [DSL Configuration](../../../usage/wfst/dsl-configuration.md)
  -- `log_semiring_model_path` and `beam_width: auto` options
- [Feature Gates](../../../usage/wfst/feature-gates.md)
  -- `wfst-log` feature documentation

### References

- Mohri, M. (2002). "Semiring Frameworks and Algorithms for Shortest-Distance
  Problems." *Journal of Automata, Languages and Combinatorics*, 7(3):321-350.
- Mohri, M., Pereira, F., & Riley, M. (2002). "Weighted Finite-State
  Transducers in Speech Recognition." *Computer Speech & Language*,
  16(1):69-88. Section 4: Weight pushing.
- Eisner, J. (2002). "Parameter Estimation for Probabilistic Finite-State
  Transducers." *Proceedings of ACL*. Training via forward-backward.
