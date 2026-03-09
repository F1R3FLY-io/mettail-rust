# ArcticWeight -- Design & Pipeline Integration

> **Date:** 2026-03-09

ArcticWeight is the dual of TropicalWeight. Where tropical finds the
**shortest** (minimum-cost) path, arctic finds the **longest**
(maximum-benefit) path. This duality arises from replacing `min` with
`max` while keeping additive accumulation. The name "arctic" is standard
in the literature: if tropical computes hot-climate shortest paths,
arctic computes cold-climate longest paths.

---

## Table of Contents

1. [Intuition](#1-intuition)
2. [Mathematical Definition](#2-mathematical-definition)
3. [Duality with TropicalWeight](#3-duality-with-tropicalweight)
4. [Data Structure](#4-data-structure)
5. [Semiring Operations](#5-semiring-operations)
6. [StarSemiring: Divergence for Positive Values](#6-starsemiring-divergence-for-positive-values)
7. [Reversed Ord Semantics](#7-reversed-ord-semantics)
8. [Trait Hierarchy](#8-trait-hierarchy)
9. [Pipeline Integration](#9-pipeline-integration)
10. [Rust API](#10-rust-api)
11. [Test Coverage](#11-test-coverage)
12. [Source References](#12-source-references)
13. [Cross-References](#13-cross-references)

---

## 1. Intuition

Consider measuring the **benefit** (or speedup) of applying an
optimization. Each optimization step adds benefit along a path:

```
Step 1: benefit 2.0
Step 2: benefit 3.0
Total path benefit: 2.0 + 3.0 = 5.0
```

When choosing among alternatives, we want the **maximum** total benefit:

```
Path A: total benefit 5.0
Path B: total benefit 3.0
Best: max(5.0, 3.0) = 5.0
```

This is the arctic semiring: `max` for alternatives, `+` for sequencing.
It naturally models critical-path analysis, worst-case propagation depth,
and optimization speedup ranking.

---

## 2. Mathematical Definition

```
A  =  ( R ∪ {-inf},  max,  +,  -inf,  0.0 )
```

| Component              | Symbol | Concrete value        | Meaning                          |
|------------------------|--------|-----------------------|----------------------------------|
| Carrier set            | K      | R ∪ {-inf}            | Real numbers plus neg. infinity  |
| Addition (⊕)           | max    | max(a, b)             | Select highest-benefit alternative|
| Multiplication (⊗)     | +      | a + b                 | Accumulate benefit along a path  |
| Additive identity (0)  | -inf   | `f64::NEG_INFINITY`   | No benefit (identity for max)    |
| Multiplicative identity| 0.0    | `0.0_f64`             | Zero benefit (identity for +)    |

### Semiring axioms

| Axiom                  | Verification (a=2.0, b=5.0, c=3.0)                          |
|------------------------|--------------------------------------------------------------|
| Additive identity      | max(-inf, 2.0) = 2.0                                        |
| Additive commutativity | max(2.0, 5.0) = max(5.0, 2.0) = 5.0                         |
| Additive associativity | max(max(2.0, 5.0), 3.0) = max(2.0, max(5.0, 3.0)) = 5.0    |
| Mult. identity         | 0.0 + 2.0 = 2.0 + 0.0 = 2.0                                |
| Mult. associativity    | (2.0 + 5.0) + 3.0 = 2.0 + (5.0 + 3.0) = 10.0               |
| Left distributivity    | 2.0 + max(5.0, 3.0) = max(2.0+5.0, 2.0+3.0) = 7.0          |
| Zero annihilation      | -inf + 2.0 = 2.0 + (-inf) = -inf                            |

All axioms hold. A is a valid semiring.

---

## 3. Duality with TropicalWeight

Arctic and tropical semirings are dual structures:

| Property              | TropicalWeight                   | ArcticWeight                      |
|-----------------------|----------------------------------|-----------------------------------|
| ⊕ (addition)          | min(a, b)                        | max(a, b)                         |
| ⊗ (multiplication)    | a + b                            | a + b                             |
| 0 (zero)              | +inf                             | -inf                              |
| 1 (one)               | 0.0                              | 0.0                               |
| Semantics             | Shortest/cheapest path           | Longest/highest-benefit path      |
| Carrier               | R+ ∪ {+inf} (non-negative)       | R ∪ {-inf} (all reals + neg inf)  |

The duality is the negation isomorphism: `arctic(a) = tropical(-a)`.
Under this mapping, `max(a, b)` corresponds to `min(-a, -b)` and
addition is preserved.

**Key difference in carrier**: TropicalWeight restricts to non-negative
reals (costs cannot be negative). ArcticWeight allows all reals
(benefits can be negative, representing penalties).

---

## 4. Data Structure

```rust
#[derive(Clone, Copy)]
pub struct ArcticWeight(pub f64);
```

Single `f64` field. No range restriction beyond the IEEE 754 domain.
Negative infinity represents the zero element (unreachable/no-benefit).

### Constructors

```rust
pub const fn new(value: f64) -> Self { ArcticWeight(value) }
pub const fn neg_infinity() -> Self { ArcticWeight(f64::NEG_INFINITY) }
```

**`neg_infinity()` constructor**: Provides a named constructor for the
zero element. The name parallels `TropicalWeight::infinity()` for the
positive-infinity zero.

### Accessors

```rust
pub const fn value(self) -> f64 { self.0 }
pub fn is_neg_infinite(self) -> bool {
    self.0.is_infinite() && self.0.is_sign_negative()
}
```

**`is_neg_infinite()` checks sign**: IEEE 754 has both `+inf` and `-inf`.
Only `-inf` is the arctic zero. The check requires both `is_infinite()`
and `is_sign_negative()` -- the mirror of TropicalWeight's `is_zero()`
which checks `is_sign_positive()`.

---

## 5. Semiring Operations

| Operation     | Code                                  | Note                              |
|---------------|---------------------------------------|-----------------------------------|
| `zero()`      | `ArcticWeight(f64::NEG_INFINITY)`     | No benefit (unreachable)          |
| `one()`       | `ArcticWeight(0.0)`                   | Zero benefit (identity for +)     |
| `plus()`      | `ArcticWeight(self.0.max(other.0))`   | Select highest benefit            |
| `times()`     | `ArcticWeight(self.0 + other.0)`      | Accumulate benefit                |
| `is_zero()`   | `is_infinite() && is_sign_negative()` | Exact -inf check                  |
| `is_one()`    | `self.0 == 0.0`                       | Exact zero check                  |
| `approx_eq()` | Like TropicalWeight: special-case -inf, else abs diff | Convergence-safe |

### approx_eq special cases

```rust
fn approx_eq(&self, other: &Self, epsilon: f64) -> bool {
    if self.is_zero() && other.is_zero() { true }        // -inf == -inf
    else if self.is_zero() || other.is_zero() { false }  // -inf != finite
    else { (self.0 - other.0).abs() <= epsilon }
}
```

This mirrors TropicalWeight's `approx_eq` with the sign flipped.

---

## 6. StarSemiring: Divergence for Positive Values

```rust
impl StarSemiring for ArcticWeight {
    fn star(&self) -> Self {
        if self.0 <= 0.0 {
            Self::one()       // converges to 0.0
        } else {
            Self::zero()      // diverges (returns -inf as sentinel)
        }
    }
}
```

**Derivation**: `star(a) = max(0, a, 2a, 3a, ...)`.

- If `a <= 0`: The sequence `{0, a, 2a, 3a, ...}` is non-increasing
  (each term is <= the previous). The maximum is the first term: `0.0`.
  Therefore `star(a) = 0.0 = one()`.

- If `a > 0`: The sequence `{0, a, 2a, 3a, ...}` diverges to `+inf`.
  No finite maximum exists. The implementation returns `zero()` (negative
  infinity) as a sentinel value indicating divergence.

This is the dual of TropicalWeight's StarSemiring, where `star(a)` for
non-negative a converges (since `min(0, a, 2a, ...)` = 0) and negative
a causes divergence.

**Design decision**: Returning `zero()` for divergent cases is a
conservative choice. Algorithms that encounter `star(positive)` should
interpret the result as "this closure does not converge" rather than
"the closure is zero."

---

## 7. Reversed Ord Semantics

```rust
impl Ord for ArcticWeight {
    fn cmp(&self, other: &Self) -> Ordering {
        other.0.total_cmp(&self.0)  // Reversed: higher value = "lower" (better)
    }
}
```

Higher benefit is better, so it compares as "lower" in the `Ord` sense.
This matches ViterbiWeight's convention and allows generic `min`-based
path selection to correctly choose the highest-benefit path.

```
ArcticWeight(5.0) < ArcticWeight(2.0)    (5.0 is better, so "lower")
```

---

## 8. Trait Hierarchy

| Trait                | Status       | Justification                                          |
|----------------------|--------------|--------------------------------------------------------|
| `DetectableZero`     | Implemented  | `is_zero()` is O(1): two IEEE 754 checks               |
| `IdempotentSemiring` | Implemented  | `max(a, a) = a` for all a                              |
| `CompleteSemiring`   | Implemented  | Idempotent plus guarantees convergence                 |
| `StarSemiring`       | Implemented  | Converges for a <= 0, diverges for a > 0               |

---

## 9. Pipeline Integration

### 9a. Feature gating

ArcticWeight is available unconditionally (no feature gate).

### 9b. Use cases

| Use Case                        | How ArcticWeight Is Used                                     |
|---------------------------------|--------------------------------------------------------------|
| **cost_benefit.rs: speedup**    | "Speedup" dimension in `ProductWeight<ArcticWeight, TropicalWeight>` -- higher speedup = better |
| **lint.rs: propagation depth**  | Worst-case error propagation depth through inter-category graph (longest path) |
| **decision_tree.rs: critical path** | Critical-path analysis: highest parsing cost across all grammar rules |

### 9c. ProductWeight pairing

The most common use of ArcticWeight is in a `ProductWeight` pair:

```rust
type CostBenefit = ProductWeight<ArcticWeight, TropicalWeight>;
```

The arctic component tracks benefit (higher = better), the tropical
component tracks cost (lower = better). The product semiring evaluates
both independently, enabling cost-benefit trade-off analysis.

---

## 10. Rust API

### Construction

```rust
use prattail::automata::semiring::{ArcticWeight, Semiring};

let w = ArcticWeight::new(3.0);            // benefit of 3.0
let neg = ArcticWeight::new(-1.5);         // penalty of 1.5
let zero = ArcticWeight::neg_infinity();   // unreachable
let one = ArcticWeight::one();             // 0.0 (no benefit)
```

### Operations

```rust
let best = w.plus(&neg);                   // max(3.0, -1.5) = 3.0
let total = w.times(&neg);                 // 3.0 + (-1.5) = 1.5

assert_eq!(ArcticWeight::zero().value(), f64::NEG_INFINITY);
assert!(ArcticWeight::neg_infinity().is_neg_infinite());
```

### StarSemiring

```rust
use prattail::automata::semiring::StarSemiring;

let converges = ArcticWeight::new(-2.0).star();  // one() = 0.0
let diverges = ArcticWeight::new(3.0).star();    // zero() = -inf (sentinel)
```

---

## 11. Test Coverage

ArcticWeight is tested as part of the semiring test suite:

| Category             | Tests                                                    |
|----------------------|----------------------------------------------------------|
| **Axiom verification** | All 7 axioms with concrete numerical examples          |
| **neg_infinity()**   | Constructor, `is_neg_infinite()`, `is_zero()` consistency|
| **StarSemiring**     | Convergent case (a <= 0), divergent case (a > 0)         |
| **Ordering**         | Reversed `Ord`, `total_cmp` determinism                  |
| **Display**          | "-inf" for zero, decimal format for finite values        |

---

## 12. Source References

| Component                     | File                        | Lines       |
|-------------------------------|-----------------------------|-------------|
| Struct definition             | `automata/semiring.rs`      | 2100--2101  |
| Constructors & accessors      | `automata/semiring.rs`      | 2103--2127  |
| `Semiring` impl               | `automata/semiring.rs`      | 2129--2169  |
| `Debug` / `Display`           | `automata/semiring.rs`      | 2171--2189  |
| `PartialEq` / `Eq`            | `automata/semiring.rs`      | 2191--2197  |
| `Ord` (reversed)              | `automata/semiring.rs`      | 2205--2212  |
| `Hash`                        | `automata/semiring.rs`      | 2214--2218  |
| `Default = one()`             | `automata/semiring.rs`      | 2220--2224  |
| Trait impls                   | `automata/semiring.rs`      | 2226--2228  |
| `StarSemiring`                | `automata/semiring.rs`      | 2230--2243  |

---

## 13. Cross-References

- **Theory**: [Tropical Weight](../../../theory/wfst/semirings/tropical-weight.md) -- the dual semiring (min instead of max)
- **TropicalWeight design**: [tropical-weight.md](tropical-weight.md) -- `ProductWeight<ArcticWeight, TropicalWeight>` for cost-benefit
- **ViterbiWeight**: [viterbi-weight.md](viterbi-weight.md) -- another "higher is better" semiring, but in probability space [0,1]
- **FuzzyWeight**: [fuzzy-weight.md](fuzzy-weight.md) -- shares `max` for ⊕ but uses `min` for ⊗ (bottleneck vs. additive)
- **ProductWeight**: [product-weight.md](product-weight.md) -- common pairing mechanism for arctic + tropical
- **Cost-benefit analysis**: `cost_benefit.rs` -- primary consumer of ArcticWeight
- **Lint layer**: `lint.rs` -- propagation depth analysis
- **Decision tree**: `decision_tree.rs` -- critical-path analysis
