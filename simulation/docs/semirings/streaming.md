# StreamingWeight: Online Statistics via Welford's Algorithm

## What Is It?

The `StreamingWeight` is a semiring that tracks running statistics (count, mean, M₂, min, max) over a stream of observations, using O(1) space per update. It implements Welford's online algorithm (Welford (1962)) for numerically stable variance computation and Chan et al.'s parallel merge formula (Chan, Golub, and LeVeque (1979)) for combining independent streams.

Located in `simulation/src/semiring/streaming.rs`.

## What Does It Do?

The streaming weight maintains sufficient statistics for computing:

- **Count** (n): number of observations
- **Mean** (μ): running average
- **Variance** (σ²): via M₂/(n-1) for sample variance or M₂/n for population variance
- **Standard deviation** (σ): √variance
- **Range** [min, max]: extremal values

All of these are maintained incrementally, without storing individual observations.

## Why Was It Chosen?

### The Memory Problem

Monitoring simulation traces can produce millions of observations. Storing every value to compute statistics post-hoc is wasteful and may exceed available memory. Welford's algorithm solves this by maintaining a fixed-size summary that can be updated in O(1) time per observation.

### Numerical Stability

The naive formula for variance:

```
σ² = E[X²] - (E[X])²
```

suffers from **catastrophic cancellation** when E[X] is large relative to σ. For example, with observations around 10⁸ and variance around 1, the naive formula computes σ² ≈ 10¹⁶ - 10¹⁶, losing all significant digits.

Welford's algorithm avoids this by maintaining the sum of squared deviations from the **running** mean, which stays small:

```
M₂ = Σᵢ (xᵢ - μ̄ₙ)²
```

This sum is numerically stable because each term (xᵢ - μ̄ₙ) is the deviation from the current mean, not from zero.

### Parallel Merge

Chan, Golub, and LeVeque (1979) showed how to merge two independently computed Welford summaries into a combined summary. This enables:

- Parallel computation across threads
- Combining results from multiple simulation campaigns
- Expressing merge as a semiring operation

## Mathematical Definition

### Carrier

```
S = ℕ × ℝ × ℝ⁺ × ℝ̄ × ℝ̄
    (count, mean, M₂, min, max)

where ℝ̄ = ℝ ∪ {±∞}
```

### Welford's Online Update

Given a stream x₁, x₂, ..., xₙ, the update for observation xₙ is:

```
PROCEDURE observe(x):
    n ← n + 1
    δ ← x - μ
    μ ← μ + δ/n
    δ₂ ← x - μ           // note: μ has been updated
    M₂ ← M₂ + δ · δ₂
    min ← min(min, x)
    max ← max(max, x)
```

**Derivation:** The identity underlying Welford's algorithm is:

```
M₂(n) = Σᵢ₌₁ⁿ (xᵢ - μ̄ₙ)²

M₂(n) - M₂(n-1) = (xₙ - μ̄ₙ)(xₙ - μ̄ₙ₋₁)
                  = δ · δ₂
```

where δ = xₙ - μ̄ₙ₋₁ (deviation from old mean) and δ₂ = xₙ - μ̄ₙ (deviation from new mean). This gives an O(1) incremental update.

### Parallel Merge (Chan et al.)

Given two independent streams A = (nₐ, μₐ, M₂ₐ, minₐ, maxₐ) and B = (nᵦ, μᵦ, M₂ᵦ, minᵦ, maxᵦ):

```
PROCEDURE merge(A, B) → StreamingWeight:
    n ← nₐ + nᵦ
    δ ← μᵦ - μₐ
    μ ← μₐ + δ · (nᵦ / n)
    M₂ ← M₂ₐ + M₂ᵦ + δ² · (nₐ · nᵦ / n)
    min ← min(minₐ, minᵦ)
    max ← max(maxₐ, maxᵦ)
    RETURN (n, μ, M₂, min, max)
```

**Derivation:** The cross-term δ² · (nₐ · nᵦ / n) accounts for the difference in means between the two streams. When the streams have equal means (δ = 0), the M₂ values simply add.

### Semiring Structure

**Plus (⊕) = parallel merge**

```
A ⊕ B = merge(A, B)
```

Combining two independent streams of observations.

**Times (⊗) = sequential composition**

```
A ⊗ B = merge(A, B)
```

In the streaming statistics semiring, ⊕ and ⊗ are the same operation because the combined statistics are order-independent. This is mathematically valid: the semiring axioms only require that (S, ⊗, 1̄) be a monoid and that ⊗ distribute over ⊕. When ⊕ = ⊗ = merge, all axioms are satisfied (the merge operation is associative, commutative, and has the empty stream as identity).

**Zero (0̄) = One (1̄) = empty stream**

```
0̄ = 1̄ = (0, 0, 0, +∞, -∞)
```

The empty stream has count 0, mean 0, M₂ = 0, min = +∞ (no observations), max = -∞ (no observations).

### Variance Recovery

```
population_variance = M₂ / n         (biased estimator)
sample_variance     = M₂ / (n - 1)   (unbiased estimator; Bessel's correction)
```

Both are available as methods:

```rust
pub fn population_variance(&self) -> f64;
pub fn sample_variance(&self) -> f64;
pub fn population_stddev(&self) -> f64;
pub fn sample_stddev(&self) -> f64;
pub fn range(&self) -> f64;           // max - min
```

## Implementation Details

### Singleton Constructor

```rust
pub const fn singleton(value: f64) -> Self {
    StreamingWeight { count: 1, mean: value, m2: 0.0, min: value, max: value }
}
```

A single observation has mean = value, zero variance, and min = max = value.

### Empty-Stream Handling

The merge function handles empty streams explicitly:

```rust
pub fn merge(&self, other: &Self) -> Self {
    if self.count == 0 { return *other; }
    if other.count == 0 { return *self; }
    // ... full merge
}
```

This ensures the empty stream is a true identity for merge.

### Equality and Hashing

Floating-point equality is implemented via bit-level comparison (`to_bits()`), which treats +0.0 and -0.0 as different values and NaN as equal to itself. This is appropriate for a semiring element where exact reproducibility matters:

```rust
impl PartialEq for StreamingWeight {
    fn eq(&self, other: &Self) -> bool {
        self.count == other.count
            && self.mean.to_bits() == other.mean.to_bits()
            && self.m2.to_bits() == other.m2.to_bits()
            && self.min.to_bits() == other.min.to_bits()
            && self.max.to_bits() == other.max.to_bits()
    }
}
```

## Use in Simulation

### Runtime Monitoring

Attach a `StreamingWeight` to each state in a streaming automaton (see [automata/streaming-automaton.md](../automata/streaming-automaton.md)). As terms flow through the rewrite pipeline, each step contributes an observation (e.g., term size). The accumulated `StreamingWeight` provides real-time mean, variance, and range without storing the full trace.

### Anomaly Detection

Compare the running statistics against a baseline. If the current mean exceeds the baseline mean by more than 3σ, flag the trace as anomalous.

### Memory-Bounded Monitoring

Since `StreamingWeight` uses O(1) space regardless of stream length, it can monitor arbitrarily long simulation traces without running out of memory. This is crucial for non-terminating systems where the trace may be infinite.

## References

- Welford, B.P. (1962). "Note on a Method for Calculating Corrected Sums of Squares and Products." Technometrics, 4(3), pp. 419-420.
- Chan, T.F., Golub, G.H., and LeVeque, R.J. (1979). "Updating Formulae and a Pairwise Algorithm for Computing Sample Variances." Technical Report STAN-CS-79-773, Stanford University.
- Knuth, D.E. (1998). The Art of Computer Programming, Volume 2: Seminumerical Algorithms, 3rd edition. Addison-Wesley. (Section 4.2.2, Algorithm B.)
