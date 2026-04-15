# ExpectationWeight: The Expectation Semiring

## What Is It?

The `ExpectationWeight` is a semiring whose carrier is a pair (w, c) where w is a **log-domain weight** (negative log probability) and c is the **expected cost** (probability-weighted cost accumulator). It combines parallel paths via logsumexp and sequences path segments via addition.

Located in `simulation/src/semiring/expectation.rs`.

## What Does It Do?

The expectation semiring simultaneously computes:

1. **Total probability** of all paths reaching a state (via the weight component).
2. **Expected cost** along those paths, weighted by their probabilities (via the cost component).

This enables computing expected rewrite chain lengths, expected parse depths, risk-weighted scheduling costs, and gradients of the total path weight.

## Why Was It Chosen?

### Eisner's Expectation Semiring

Eisner (2002) introduced the expectation semiring for parameter estimation in probabilistic finite-state transducers. The key insight is that the expectation of a cost function over a probability distribution can be computed by a single forward pass through a weighted automaton, if the semiring operations correctly combine weights and costs.

In the MeTTaIL context, this means we can answer questions like: "What is the expected number of rewrite steps to reach normal form, weighted by the probability of each rewrite path?" This is valuable for performance analysis and rewrite system optimization.

### Gradient Computation

A remarkable property of the expectation semiring is that the expected cost component naturally computes ∂/∂θ of the total path weight (Eisner (2002), Section 4). This enables gradient-based optimization of parameterized rewrite systems without requiring automatic differentiation.

## Mathematical Definition

### Carrier

```
S = ℝ⁺ × ℝ  =  {(w, c) : w ∈ ℝ⁺ ∪ {+∞}, c ∈ ℝ}
```

where w is in log-domain (w = -ln(p) for probability p).

### Operations

**Plus (⊕): combine parallel paths**

```
(w₁, c₁) ⊕ (w₂, c₂) = (logsumexp(w₁, w₂), weighted_avg(c₁, c₂))
```

where:
```
logsumexp(w₁, w₂) = -ln(exp(-w₁) + exp(-w₂))
                   = min(w₁, w₂) - ln(1 + exp(-|w₁ - w₂|))

weighted_avg(c₁, c₂) = (p₁·c₁ + p₂·c₂) / (p₁ + p₂)
                       where pᵢ = exp(-wᵢ)
```

**Intuition:** When two paths merge at a state, their probabilities add (logsumexp in log-domain) and their costs are averaged, weighted by their respective probabilities. A high-probability path contributes more to the expected cost than a low-probability one.

**Times (⊗): sequence path segments**

```
(w₁, c₁) ⊗ (w₂, c₂) = (w₁ + w₂, c₁ + c₂)
```

**Intuition:** When traversing two segments in sequence, probabilities multiply (addition in log-domain) and costs accumulate (addition).

**Zero (0̄): unreachable path**

```
0̄ = (+∞, 0)
```

An unreachable path has zero probability (w = +∞ in log-domain) and zero cost contribution.

**One (1̄): zero-cost identity**

```
1̄ = (0, 0)
```

Probability 1 (w = 0 in log-domain), zero cost.

### Verification of Semiring Axioms

**Zero is additive identity:**
```
(w, c) ⊕ (+∞, 0) = (logsumexp(w, +∞), ...) = (w, c)  ✓
```
Since logsumexp(w, +∞) = w (adding zero probability).

**One is multiplicative identity:**
```
(w, c) ⊗ (0, 0) = (w + 0, c + 0) = (w, c)  ✓
```

**Zero annihilates:**
```
(w, c) ⊗ (+∞, 0) = (w + ∞, c + 0) = (+∞, c)
```
Since w + ∞ = ∞, this is effectively zero (unreachable). The implementation checks `is_zero()` by testing `w.is_infinite() && w.is_sign_positive()`.

## Implementation Details

### Numerical Stability

The logsumexp computation uses the identity:
```
logsumexp(a, b) = min(a, b) - ln(1 + exp(-|a - b|))
```

When |a - b| > 20, the correction term exp(-|a - b|) < 2.1 × 10⁻⁹, which is negligible for `f64`. The implementation drops this correction for efficiency:

```
PROCEDURE log_sum_exp(a, b) → f64:
    IF a == +∞ THEN RETURN b
    IF b == +∞ THEN RETURN a
    min_val ← min(a, b)
    diff ← |a - b|
    IF diff > 20.0 THEN RETURN min_val
    RETURN min_val - ln(1.0 + exp(-diff))
```

### Weighted Cost Averaging

The cost component of ⊕ computes a probability-weighted average. For numerical stability, the probabilities are computed relative to the new combined weight:

```
PROCEDURE plus(self, other) → ExpectationWeight:
    IF self.is_zero() THEN RETURN other
    IF other.is_zero() THEN RETURN self

    new_w ← log_sum_exp(self.w, other.w)

    // Compute relative probabilities (shifted by new_w for stability)
    p₁ ← exp(-(self.w - new_w))
    p₂ ← exp(-(other.w - new_w))
    p_sum ← p₁ + p₂

    new_c ← IF p_sum > 0 THEN
        (p₁ · self.c + p₂ · other.c) / p_sum
    ELSE
        0.0

    RETURN (new_w, new_c)
```

### Probability Conversion

```rust
pub fn from_probability(p: f64, cost: f64) -> Self {
    assert!(p > 0.0);
    ExpectationWeight { weight: -p.ln(), expected_cost: cost }
}

pub fn to_probability(&self) -> f64 {
    (-self.weight).exp()
}
```

## Use in Simulation

### Expected Rewrite Chain Length

Label each rewrite transition with weight `ExpectationWeight::from_probability(p, 1.0)` where p is the probability of that rewrite and cost 1.0 counts one step. The shortest-distance algorithm then computes the expected number of steps to reach normal form.

### Risk-Aware Scheduling

Label transitions with `ExpectationWeight::new(w, latency)` where w is the negative log probability and latency is the expected latency. The semiring naturally computes expected latency across all possible scheduling paths.

## References

- Eisner, J. (2002). "Parameter Estimation for Probabilistic Finite-State Transducers." Proceedings of the 40th Annual Meeting of the ACL, pp. 1-8.
- Li, Z. and Eisner, J. (2009). "First- and Second-Order Expectation Semirings with Applications to Minimum-Risk Training on Translation Forests." Proceedings of EMNLP.
