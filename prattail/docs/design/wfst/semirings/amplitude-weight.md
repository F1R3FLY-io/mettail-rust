# AmplitudeWeight -- Design & Pipeline Integration

> **Date:** 2026-03-09

AmplitudeWeight brings complex-valued quantum amplitudes into the
semiring framework. Unlike all other PraTTaIL semirings (which model
classical optimization, counting, or reachability), AmplitudeWeight
models quantum interference: two paths can *cancel* when their
amplitudes have opposite signs. The classical observation probability
is obtained via the Born rule: `|z|^2 = re^2 + im^2`.

---

## Table of Contents

1. [Intuition](#1-intuition)
2. [Mathematical Definition](#2-mathematical-definition)
3. [Born Rule Measurement](#3-born-rule-measurement)
4. [Data Structure](#4-data-structure)
5. [Semiring Operations](#5-semiring-operations)
6. [Quantum Feature Gate](#6-quantum-feature-gate)
7. [Viterbi Caveat](#7-viterbi-caveat)
8. [Probability Conversions](#8-probability-conversions)
9. [Ordering Semantics](#9-ordering-semantics)
10. [Trait Hierarchy: NOT star/complete/idempotent](#10-trait-hierarchy-not-starcompleteidempotent)
11. [Pipeline Integration](#11-pipeline-integration)
12. [Rust API](#12-rust-api)
13. [Test Coverage](#13-test-coverage)
14. [Source References](#14-source-references)
15. [Cross-References](#15-cross-references)

---

## 1. Intuition

In quantum computing, a system can exist in a superposition of states.
Each state has a complex amplitude `z = a + bi`, and the probability of
observing that state is `|z|^2 = a^2 + b^2` (the Born rule).

Two paths to the same state can interfere:

```
Path 1 amplitude:  +0.5 + 0.0i
Path 2 amplitude:  -0.5 + 0.0i
Combined:          +0.5 + (-0.5) = 0.0 + 0.0i   (destructive interference!)
```

The two paths cancel each other. A classical semiring (tropical, Viterbi,
counting) would report two paths with positive probability. The amplitude
semiring correctly shows zero probability after interference.

In PraTTaIL, AmplitudeWeight models quantum CTMC (continuous-time Markov
chain) simulation, where grammar rules have complex-valued transition
amplitudes and parse paths can interfere constructively or destructively.

---

## 2. Mathematical Definition

```
C  =  ( C,  +,  x,  0+0i,  1+0i )
```

| Component              | Symbol | Concrete value                    | Meaning                          |
|------------------------|--------|-----------------------------------|----------------------------------|
| Carrier set            | K      | C (complex numbers)               | Quantum amplitudes               |
| Addition (⊕)           | +      | complex addition                  | Superposition (interference)     |
| Multiplication (⊗)     | x      | complex multiplication            | Sequential amplitude composition |
| Additive identity (0)  | 0+0i   | `Complex64::new(0.0, 0.0)`       | Zero amplitude (no contribution) |
| Multiplicative identity| 1+0i   | `Complex64::new(1.0, 0.0)`       | Unit amplitude (identity)        |

This is technically a **ring** (additive inverses exist: `-z` is the
inverse of `z`) but satisfies all semiring requirements. The additional
ring structure (additive inverses) is what enables destructive
interference -- a feature no true semiring can model.

### Semiring axioms (z_1 = 0.6+0.8i, z_2 = 0.3-0.4i, z_3 = 1.0+0.0i)

| Axiom                  | Verification                                                              |
|------------------------|---------------------------------------------------------------------------|
| Additive identity      | (0+0i) + (0.6+0.8i) = 0.6+0.8i                                           |
| Additive commutativity | (0.6+0.8i) + (0.3-0.4i) = (0.3-0.4i) + (0.6+0.8i) = 0.9+0.4i            |
| Additive associativity | Standard complex addition is associative                                  |
| Mult. identity         | (1+0i) * (0.6+0.8i) = 0.6+0.8i                                           |
| Mult. associativity    | Standard complex multiplication is associative                            |
| Left distributivity    | z_1 * (z_2 + z_3) = z_1*z_2 + z_1*z_3 (field distributivity)             |
| Zero annihilation      | (0+0i) * z = z * (0+0i) = 0+0i                                           |

All axioms hold. C is a valid semiring (in fact, a field).

---

## 3. Born Rule Measurement

The Born rule connects quantum amplitudes to classical observation
probabilities:

```
probability  =  |z|^2  =  re^2 + im^2  =  norm_sqr(z)
```

| Amplitude z      | |z|^2     | Probability  | Interpretation           |
|------------------|-----------|--------------|--------------------------|
| 1.0 + 0.0i       | 1.0       | 100%         | Certain                  |
| 0.0 + 0.0i       | 0.0       | 0%           | Impossible               |
| 0.707 + 0.707i   | ~1.0      | ~100%        | Near-certain (unit circle)|
| 0.6 + 0.8i       | 1.0       | 100%         | Unit circle (|z| = 1)   |
| 0.5 + 0.0i       | 0.25      | 25%          | Real amplitude sqrt(0.25)|

**Key insight**: Amplitudes that are not on the unit circle represent
non-normalized states. The Born rule still applies, but the
probabilities may not sum to 1 across all states until normalization.

### norm_sqr() method

```rust
pub fn norm_sqr(self) -> f64 {
    self.0.norm_sqr()  // re^2 + im^2
}
```

This is the primary measurement interface. All classical reasoning
about AmplitudeWeight goes through `norm_sqr()` or `to_probability()`.

---

## 4. Data Structure

```rust
#[cfg(feature = "quantum")]
#[derive(Clone, Copy)]
pub struct AmplitudeWeight(pub num_complex::Complex64);
```

Wraps `num_complex::Complex64`, which is a `(f64, f64)` pair for real
and imaginary components.

**Memory**: 16 bytes (two `f64`), stack-allocated, `Copy`.

**Dependency**: Requires the `num-complex` crate, gated behind the
`quantum` feature to avoid pulling in unnecessary dependencies.

---

## 5. Semiring Operations

| Operation     | Code                                              | Note                              |
|---------------|---------------------------------------------------|-----------------------------------|
| `zero()`      | `AmplitudeWeight(Complex64::new(0.0, 0.0))`      | Zero amplitude                    |
| `one()`       | `AmplitudeWeight(Complex64::new(1.0, 0.0))`      | Unit amplitude (real)             |
| `plus()`      | `AmplitudeWeight(self.0 + other.0)`               | Complex addition (interference)   |
| `times()`     | `AmplitudeWeight(self.0 * other.0)`               | Complex multiplication            |
| `is_zero()`   | `self.0.re == 0.0 && self.0.im == 0.0`            | Exact zero check                  |
| `is_one()`    | `self.0.re == 1.0 && self.0.im == 0.0`            | Exact one check                   |
| `approx_eq()` | Both re and im within epsilon                     | Per-component check               |

### approx_eq: per-component

```rust
fn approx_eq(&self, other: &Self, epsilon: f64) -> bool {
    (self.0.re - other.0.re).abs() <= epsilon
        && (self.0.im - other.0.im).abs() <= epsilon
}
```

Both real and imaginary parts must be within epsilon. This is an
L-infinity (Chebyshev) distance check, not an L2 (Euclidean) distance
check. This means two amplitudes with small real difference but large
imaginary difference will correctly report as not approximately equal.

---

## 6. Quantum Feature Gate

AmplitudeWeight is gated behind `#[cfg(feature = "quantum")]`:

```toml
[features]
quantum = ["dep:num-complex"]

[dependencies]
num-complex = { version = "0.4", optional = true }
```

**Rationale**: The `num-complex` dependency is non-trivial and unused
by most PraTTaIL grammars. Feature-gating ensures zero compile-time
cost for projects that do not need quantum amplitude weights.

### Cross-feature: from_log_weight

The `from_log_weight()` conversion is additionally gated on `wfst-log`:

```rust
#[cfg(all(feature = "quantum", feature = "wfst-log"))]
impl AmplitudeWeight {
    pub fn from_log_weight(w: LogWeight) -> Self {
        if w.is_zero() {
            AmplitudeWeight::zero()
        } else {
            AmplitudeWeight(Complex64::new((-w.value() / 2.0).exp(), 0.0))
        }
    }
}
```

The conversion produces a real amplitude `sqrt(exp(-w))` = `exp(-w/2)`
whose Born rule gives `exp(-w)`, recovering the original probability
that the LogWeight encodes.

---

## 7. Viterbi Caveat

**AmplitudeWeight is NOT suitable for direct Viterbi path selection.**

The Viterbi algorithm assumes that path weights combine monotonically:
the best sub-path extends to the best full path. This fails for
amplitudes due to interference:

```
Path A to state q: amplitude  +0.5
Path B to state q: amplitude  -0.5
Combined at q:     amplitude   0.0  (destructive interference)

Path A to state r: amplitude  +0.5
Path C to state r: amplitude  +0.5
Combined at r:     amplitude  +1.0  (constructive interference)
```

Viterbi would select the sub-path with the highest |z|^2 at each
intermediate state. But the "best" sub-path at q (say Path A with
amplitude 0.5) can cancel with Path B. The Viterbi-optimal path may
have zero probability after interference.

**Correct approach**: Use full forward propagation (summing all path
amplitudes at each state), then apply Born-rule measurement at the
final state. Alternatively, pair with a classical priority channel:

```rust
type HybridWeight = ProductWeight<AmplitudeWeight, TropicalWeight>;
```

The tropical component provides a classical priority for dispatch
ordering, while the amplitude component tracks quantum interference
for simulation purposes.

---

## 8. Probability Conversions

### from_probability(p)

```rust
pub fn from_probability(p: f64) -> Self {
    debug_assert!((0.0..=1.0).contains(&p));
    AmplitudeWeight(Complex64::new(p.sqrt(), 0.0))
}
```

Creates a real-valued amplitude `sqrt(p) + 0i` whose Born rule gives
`p`. This is the standard embedding of classical probabilities into
the amplitude semiring.

**Range check**: `debug_assert!` validates `p in [0, 1]`.

### to_probability()

```rust
pub fn to_probability(self) -> f64 {
    self.0.norm_sqr()  // |z|^2 = re^2 + im^2
}
```

Collapses to classical probability via the Born rule. For amplitudes
created via `from_probability()`, round-trip fidelity is exact (up to
floating-point precision).

### Conversion diagram

```
                    from_probability(0.64)
  Probability 0.64 ────────────────────────▶ AmplitudeWeight(0.8 + 0.0i)
                                                       │
                    to_probability()                    │
  Probability 0.64 ◀──────────────────────── |0.8|^2 = 0.64
```

### from_log_weight (quantum + wfst-log)

```
LogWeight(w) ──▶ AmplitudeWeight(exp(-w/2) + 0i)
                 Born rule: |exp(-w/2)|^2 = exp(-w) = original probability
```

---

## 9. Ordering Semantics

```rust
impl Ord for AmplitudeWeight {
    fn cmp(&self, other: &Self) -> Ordering {
        let self_norm = self.0.norm_sqr();
        let other_norm = other.0.norm_sqr();
        match other_norm.total_cmp(&self_norm) {  // Reversed!
            Ordering::Equal => {
                match self.0.re.total_cmp(&other.0.re) {   // Tiebreak: real part
                    Ordering::Equal => self.0.im.total_cmp(&other.0.im),  // Then: imaginary
                    ord => ord,
                }
            }
            ord => ord,
        }
    }
}
```

**Primary ordering**: By `norm_sqr()` (Born rule probability), reversed
so that higher probability = "lower" (better). This matches the
ViterbiWeight convention.

**Tiebreaking**: When two amplitudes have the same `norm_sqr()` (e.g.,
`0.6+0.8i` and `0.8+0.6i` both have `norm_sqr = 1.0`), ties are broken
by real part (ascending), then imaginary part (ascending). This ensures
a total, deterministic ordering for use in `BTreeMap` keys and sorted
collections.

**Hash consistency**: `Hash` is implemented via `to_bits()` on both
components, ensuring `Eq` and `Hash` are consistent.

---

## 10. Trait Hierarchy: NOT star/complete/idempotent

AmplitudeWeight implements only `DetectableZero`:

| Trait                | Status           | Reason                                                  |
|----------------------|------------------|---------------------------------------------------------|
| `DetectableZero`     | Implemented      | `is_zero()` is O(1): two exact equality checks          |
| `IdempotentSemiring` | NOT implemented  | `z + z = 2z != z` for non-zero z                        |
| `CompleteSemiring`   | NOT implemented  | Infinite sums do not generally converge in C             |
| `StarSemiring`       | NOT implemented  | Geometric series `1 + z + z^2 + ...` diverges for |z| >= 1 |

### Why NOT idempotent

```
z = 0.5 + 0.0i
z + z = 1.0 + 0.0i != z
```

Complex addition is not idempotent. This is fundamental to quantum
mechanics: adding two copies of an amplitude doubles it (constructive
interference), producing a different state.

### Why NOT StarSemiring

The Kleene star would be the geometric series:

```
star(z) = 1 + z + z^2 + z^3 + ... = 1 / (1 - z)   (if |z| < 1)
```

This converges only when `|z| < 1`. For `|z| >= 1`, the series
diverges. Since the carrier is all of C (not just the open unit disk),
star cannot be defined for all elements.

**Design decision**: Rather than implementing star with a precondition
or returning a sentinel for divergent cases, AmplitudeWeight simply
does not implement `StarSemiring`. Algorithms requiring Kleene closure
should use a different weight type.

---

## 11. Pipeline Integration

### 11a. Feature gating

AmplitudeWeight requires `feature = "quantum"`. The `from_log_weight()`
conversion additionally requires `feature = "wfst-log"`.

### 11b. Use cases

| Use Case                        | How AmplitudeWeight Is Used                              |
|---------------------------------|----------------------------------------------------------|
| **Quantum CTMC simulation**     | Grammar rules as quantum transitions with complex amplitudes |
| **Interference analysis**       | Detecting destructive interference between parse paths    |
| **ProductWeight pairing**       | `ProductWeight<AmplitudeWeight, TropicalWeight>` for hybrid quantum+classical dispatch |
| **Gillespie integration**       | Stochastic simulation with quantum effects (see `mettail-gillespie-notes.md`) |

### 11c. Pipeline data flow

```
┌────────────────────────┐
│  Grammar rules with    │
│  complex amplitudes    │
│  (quantum feature)     │
└──────────┬─────────────┘
           │
           ▼
┌────────────────────────┐
│  Forward propagation   │
│  (sum amplitudes at    │
│  each state)           │
└──────────┬─────────────┘
           │
           ▼
┌────────────────────────┐
│  Born rule measurement │
│  |z|^2 = probability   │
│  (to_probability())    │
└──────────┬─────────────┘
           │
           ▼
┌────────────────────────┐
│  Classical dispatch    │
│  (TropicalWeight from  │
│  probability)          │
└────────────────────────┘
```

---

## 12. Rust API

### Construction

```rust
use prattail::automata::semiring::{AmplitudeWeight, Semiring};

let z = AmplitudeWeight::new(0.6, 0.8);       // 0.6 + 0.8i
let real = AmplitudeWeight::new(0.5, 0.0);    // 0.5 + 0.0i (real)
let zero = AmplitudeWeight::zero();            // 0 + 0i
let one = AmplitudeWeight::one();              // 1 + 0i
```

### Measurement

```rust
let z = AmplitudeWeight::new(0.6, 0.8);
assert_eq!(z.norm_sqr(), 1.0);                // |0.6+0.8i|^2 = 0.36+0.64 = 1.0
assert_eq!(z.to_probability(), 1.0);          // same as norm_sqr
```

### Probability round-trip

```rust
let p = 0.64;
let z = AmplitudeWeight::from_probability(p);  // 0.8 + 0.0i
assert!((z.to_probability() - p).abs() < 1e-10);
```

### Interference

```rust
let z1 = AmplitudeWeight::new(0.5, 0.0);
let z2 = AmplitudeWeight::new(-0.5, 0.0);
let combined = z1.plus(&z2);                  // 0.0 + 0.0i
assert!(combined.is_zero());                   // destructive interference!
```

### Sequential composition

```rust
let z1 = AmplitudeWeight::new(0.0, 1.0);      // i
let z2 = AmplitudeWeight::new(0.0, 1.0);      // i
let product = z1.times(&z2);                   // i * i = -1
assert!(product.approx_eq(&AmplitudeWeight::new(-1.0, 0.0), 1e-10));
```

---

## 13. Test Coverage

AmplitudeWeight is tested in the quantum-gated test suite:

| Category             | Tests                                                    |
|----------------------|----------------------------------------------------------|
| **Axiom verification** | All 7 axioms with complex-valued examples              |
| **Born rule**        | `norm_sqr()`, `to_probability()` for various amplitudes  |
| **from_probability** | Round-trip fidelity, edge cases (0.0, 1.0)               |
| **Interference**     | Constructive and destructive interference                |
| **Complex multiply** | Phase rotation, conjugation, i*i = -1                    |
| **Ordering**         | norm_sqr-based reversed `Ord`, tiebreaking determinism   |
| **from_log_weight**  | Cross-feature conversion (quantum + wfst-log)            |

Tests are run under `cargo test --features quantum` and
`cargo test --features quantum,wfst-log`.

---

## 14. Source References

| Component                     | File                        | Lines       |
|-------------------------------|-----------------------------|-------------|
| Struct definition             | `automata/semiring.rs`      | 2536--2538  |
| Constructors & measurement    | `automata/semiring.rs`      | 2540--2571  |
| `from_log_weight()` (cross-feature) | `automata/semiring.rs` | 2573--2587  |
| `Semiring` impl               | `automata/semiring.rs`      | 2589--2625  |
| `Debug` / `Display`           | `automata/semiring.rs`      | 2627--2639  |
| `PartialEq` / `Eq`            | `automata/semiring.rs`      | 2641--2650  |
| `Ord` (norm_sqr reversed)     | `automata/semiring.rs`      | 2659--2679  |
| `Hash`                        | `automata/semiring.rs`      | 2681--2687  |
| `Default = one()`             | `automata/semiring.rs`      | 2689--2694  |
| `DetectableZero`              | `automata/semiring.rs`      | 2696--2698  |

---

## 15. Cross-References

- **ViterbiWeight**: [viterbi-weight.md](viterbi-weight.md) -- real-valued probability space; shares reversed `Ord` convention but without interference
- **LogWeight**: [log-weight.md](log-weight.md) -- negative log-probability; source for `from_log_weight()` conversion
- **TropicalWeight**: [tropical-weight.md](tropical-weight.md) -- classical dispatch weight; paired with AmplitudeWeight in `ProductWeight` for hybrid systems
- **ProductWeight**: [product-weight.md](product-weight.md) -- `ProductWeight<AmplitudeWeight, TropicalWeight>` for quantum+classical
- **Gillespie notes**: `../../../docs/design/mettail-gillespie-notes.md` -- quantum CTMC simulation design
- **Semiring catalog**: `../../../docs/design/semiring-catalog.md` -- overview of all semiring types including quantum feature gate
- **num-complex**: External dependency for `Complex64` arithmetic
