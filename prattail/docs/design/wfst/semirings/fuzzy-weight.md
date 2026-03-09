# FuzzyWeight -- Design & Pipeline Integration

> **Date:** 2026-03-09

FuzzyWeight implements the possibilistic/fuzzy semiring: "how possible
is this path?" Unlike probability (which sums to 1 across alternatives
and multiplies along paths), fuzzy weights express independent degrees
of possibility in `[0, 1]`. The key distinction is **bottleneck
semantics**: the possibility of a multi-step path is limited by its
least possible step, not by the product of all steps.

---

## Table of Contents

1. [Intuition](#1-intuition)
2. [Mathematical Definition](#2-mathematical-definition)
3. [Bottleneck Semantics vs. Probability](#3-bottleneck-semantics-vs-probability)
4. [Data Structure](#4-data-structure)
5. [Semiring Operations](#5-semiring-operations)
6. [Lattice Properties](#6-lattice-properties)
7. [StarSemiring: star = 1.0 Always](#7-starsemiring-star--10-always)
8. [Reversed Ord Semantics](#8-reversed-ord-semantics)
9. [Trait Hierarchy](#9-trait-hierarchy)
10. [Pipeline Integration](#10-pipeline-integration)
11. [Rust API](#11-rust-api)
12. [Test Coverage](#12-test-coverage)
13. [Source References](#13-source-references)
14. [Cross-References](#14-cross-references)

---

## 1. Intuition

Consider evaluating the "plausibility" of a parse recovery strategy.
Each recovery step has a possibility degree: "how likely is this step
to produce a useful repair?"

```
Step 1: delete unexpected token       possibility 0.9
Step 2: insert missing semicolon      possibility 0.6
Step 3: resume normal parsing         possibility 0.8
```

The plausibility of the full strategy is limited by the weakest link:

```
min(0.9, 0.6, 0.8) = 0.6
```

This is bottleneck semantics: a chain is only as plausible as its
least plausible step. When choosing among alternative strategies:

```
Strategy A: plausibility 0.6
Strategy B: plausibility 0.3
Best: max(0.6, 0.3) = 0.6
```

We select the most possible alternative.

---

## 2. Mathematical Definition

```
F  =  ( [0, 1],  max,  min,  0.0,  1.0 )
```

| Component              | Symbol | Concrete value | Meaning                              |
|------------------------|--------|----------------|--------------------------------------|
| Carrier set            | K      | [0, 1]         | Possibility degrees (zero to one)    |
| Addition (⊕)           | max    | max(a, b)      | Most possible alternative            |
| Multiplication (⊗)     | min    | min(a, b)      | Bottleneck: weakest link             |
| Additive identity (0)  | 0.0    | `0.0_f64`      | Impossible (identity for max)        |
| Multiplicative identity| 1.0    | `1.0_f64`      | Fully possible (identity for min)    |

### Semiring axioms

| Axiom                  | Verification (a=0.8, b=0.5, c=0.3)                            |
|------------------------|------------------------------------------------------------|
| Additive identity      | max(0.0, 0.8) = 0.8                                       |
| Additive commutativity | max(0.8, 0.5) = max(0.5, 0.8) = 0.8                       |
| Additive associativity | max(max(0.8, 0.5), 0.3) = max(0.8, max(0.5, 0.3)) = 0.8  |
| Mult. identity         | min(1.0, 0.8) = min(0.8, 1.0) = 0.8                       |
| Mult. associativity    | min(min(0.8, 0.5), 0.3) = min(0.8, min(0.5, 0.3)) = 0.3  |
| Left distributivity    | min(0.8, max(0.5, 0.3)) = max(min(0.8, 0.5), min(0.8, 0.3)) = max(0.5, 0.3) = 0.5 |
| Zero annihilation      | min(0.0, 0.8) = min(0.8, 0.0) = 0.0                       |

All axioms hold. F is a valid semiring.

---

## 3. Bottleneck Semantics vs. Probability

FuzzyWeight and ViterbiWeight both use `[0, 1]` and `max` for ⊕, but
they differ fundamentally in ⊗:

| Property              | FuzzyWeight (Possibilistic) | ViterbiWeight (Probabilistic)  |
|-----------------------|-----------------------------|--------------------------------|
| ⊗ (sequencing)        | min(a, b) = bottleneck      | a * b = joint probability      |
| Interpretation        | Weakest link determines path| Independent events multiply    |
| 0.8 ⊗ 0.5            | min(0.8, 0.5) = 0.5         | 0.8 * 0.5 = 0.4               |
| 0.5 ⊗ 0.5            | min(0.5, 0.5) = 0.5         | 0.5 * 0.5 = 0.25              |
| 0.5 ⊗ 0.5 ⊗ 0.5      | min(0.5, 0.5, 0.5) = 0.5    | 0.5^3 = 0.125                 |
| Degradation rate      | None (bottleneck unchanged) | Exponential (each step halves) |

**Key insight**: FuzzyWeight does not degrade with path length. A 100-step
path where every step has possibility 0.5 still has overall possibility
0.5. ViterbiWeight would give `0.5^100 ~ 8e-31`. This makes FuzzyWeight
appropriate when the "plausibility" of a path is determined by its
weakest link rather than by the cumulative probability of all steps.

### When to use each

| Scenario                                    | Choice        | Reason                           |
|---------------------------------------------|---------------|----------------------------------|
| HMM emission/transition probabilities       | ViterbiWeight | True conditional probability     |
| Expert confidence ratings per rule          | FuzzyWeight   | Bottleneck: weakest expert score |
| Error recovery plausibility                 | FuzzyWeight   | Weakest repair step dominates    |
| Lint true-positive likelihood               | FuzzyWeight   | Independent degree, not probability|
| Forward-backward training                   | LogWeight     | Numerical stability for sums     |

---

## 4. Data Structure

```rust
#[derive(Clone, Copy)]
pub struct FuzzyWeight(pub f64);
```

Single `f64` field storing a possibility degree in `[0.0, 1.0]`. The
`new()` constructor includes a `debug_assert!` to validate the range:

```rust
pub fn new(degree: f64) -> Self {
    debug_assert!(
        (0.0..=1.0).contains(&degree),
        "FuzzyWeight: degree must be in [0, 1], got {degree}"
    );
    FuzzyWeight(degree)
}
```

### degree() accessor

```rust
pub const fn degree(self) -> f64 { self.0 }
```

The accessor is named `degree()` (not `value()` or `probability()`) to
emphasize that this is a possibility degree, not a probability. The
distinction matters: probabilities of alternatives sum to 1, while
possibility degrees are independent and can all be 1.0 simultaneously.

**Memory**: 8 bytes, stack-allocated, `Copy`.

---

## 5. Semiring Operations

| Operation     | Code                                  | Note                              |
|---------------|---------------------------------------|-----------------------------------|
| `zero()`      | `FuzzyWeight(0.0)`                    | Impossible                        |
| `one()`       | `FuzzyWeight(1.0)`                    | Fully possible                    |
| `plus()`      | `FuzzyWeight(self.0.max(other.0))`    | Most possible alternative         |
| `times()`     | `FuzzyWeight(self.0.min(other.0))`    | Bottleneck (weakest link)         |
| `is_zero()`   | `self.0 == 0.0`                       | Exact zero check                  |
| `is_one()`    | `self.0 == 1.0`                       | Exact one check                   |
| `approx_eq()` | `(self.0 - other.0).abs() <= epsilon` | Standard float comparison         |

### No special approx_eq cases

Unlike TropicalWeight and ArcticWeight, FuzzyWeight does not need
special-case handling for infinity in `approx_eq()`. The carrier is
`[0, 1]` -- finite and bounded -- so all comparisons are between
finite values.

---

## 6. Lattice Properties

FuzzyWeight's carrier `[0, 1]` with `max` and `min` forms a bounded
distributive lattice:

```
                1.0
               ╱   ╲
             ...   ...
            ╱         ╲
          0.5         0.5
            ╲         ╱
             ...   ...
               ╲   ╱
                0.0
```

| Lattice property | FuzzyWeight mapping                                     |
|------------------|---------------------------------------------------------|
| Join (∨)         | max (= ⊕)                                               |
| Meet (∧)         | min (= ⊗)                                               |
| Top (⊤)          | 1.0 (= multiplicative identity)                        |
| Bottom (⊥)       | 0.0 (= additive identity)                              |
| Distributive     | min(a, max(b, c)) = max(min(a, b), min(a, c))          |
| Bounded          | 0.0 <= a <= 1.0 for all a                               |
| Absorption       | max(a, min(a, b)) = a; min(a, max(a, b)) = a           |

This lattice structure means FuzzyWeight has stronger algebraic
properties than most semirings. In particular, both operations are
idempotent and the absorption laws hold -- properties not shared by
any other PraTTaIL semiring.

---

## 7. StarSemiring: star = 1.0 Always

```rust
impl StarSemiring for FuzzyWeight {
    fn star(&self) -> Self {
        FuzzyWeight(1.0)
    }
}
```

**Derivation**: `star(a) = max(1.0, a, min(a, a), min(a, a, a), ...)`.

For any `a in [0, 1]`:
- `min(a, a, ..., a)` (k times) = `a` for all k (idempotent min)
- So the series is `max(1.0, a, a, a, ...) = max(1.0, a) = 1.0`

The first term `1.0` (the multiplicative identity) is always the
maximum because no element in `[0, 1]` exceeds 1.0. Therefore
`star(a) = 1.0` for all a.

---

## 8. Reversed Ord Semantics

```rust
impl Ord for FuzzyWeight {
    fn cmp(&self, other: &Self) -> Ordering {
        other.0.total_cmp(&self.0)  // Reversed: higher degree = "lower" (better)
    }
}
```

Higher possibility degree is better, so it compares as "lower" in the
`Ord` sense. This allows generic `min`-based path selection to correctly
choose the most possible alternative.

---

## 9. Trait Hierarchy

| Trait                | Status       | Justification                                          |
|----------------------|--------------|--------------------------------------------------------|
| `DetectableZero`     | Implemented  | `is_zero()` is O(1): `self.0 == 0.0`                  |
| `IdempotentSemiring` | Implemented  | `max(a, a) = a` for all a                              |
| `CompleteSemiring`   | Implemented  | Idempotent plus guarantees convergence                 |
| `StarSemiring`       | Implemented  | `star(a) = 1.0` always (see derivation above)          |

### Additional idempotency of times

Note that `times` is also idempotent: `min(a, a) = a`. This makes
FuzzyWeight a **doubly idempotent** semiring -- both ⊕ and ⊗ are
idempotent. This extra property is unique among PraTTaIL's semirings
and makes FuzzyWeight especially well-behaved for fixed-point
computations.

---

## 10. Pipeline Integration

### 10a. Feature gating

FuzzyWeight is available unconditionally (no feature gate).

### 10b. Use cases

| Use Case                         | How FuzzyWeight Is Used                                      |
|----------------------------------|--------------------------------------------------------------|
| **prediction.rs: confidence**    | Dispatch confidence independent of probability: "how certain is this dispatch decision?" |
| **recovery.rs: plausibility**    | Fuzzy plausibility of a recovery strategy (bottleneck of all repair steps) |
| **lint.rs: true-positive score** | Likelihood that a diagnostic is a true positive (expert rating, not calculated probability) |

### 10c. Comparison with BooleanWeight

FuzzyWeight generalizes BooleanWeight to a continuous scale:

| BooleanWeight | FuzzyWeight   | Interpretation              |
|---------------|---------------|-----------------------------|
| false (0)     | 0.0           | Impossible                  |
| true (1)      | 1.0           | Fully possible / certain    |
| --            | 0.5           | Partially possible          |
| --            | 0.1           | Barely possible             |

FuzzyWeight with only values 0.0 and 1.0 is isomorphic to BooleanWeight.
The continuous range provides finer-grained plausibility assessment.

---

## 11. Rust API

### Construction

```rust
use prattail::automata::semiring::{FuzzyWeight, Semiring};

let high = FuzzyWeight::new(0.9);          // very possible
let low = FuzzyWeight::new(0.2);           // barely possible
let zero = FuzzyWeight::zero();            // impossible (0.0)
let one = FuzzyWeight::one();              // fully possible (1.0)
```

### Operations

```rust
let best = high.plus(&low);               // max(0.9, 0.2) = 0.9
let bottleneck = high.times(&low);         // min(0.9, 0.2) = 0.2

assert_eq!(high.degree(), 0.9);
```

### StarSemiring

```rust
use prattail::automata::semiring::StarSemiring;

let s = FuzzyWeight::new(0.5).star();     // 1.0 (always)
let s0 = FuzzyWeight::zero().star();      // 1.0 (always)
```

---

## 12. Test Coverage

FuzzyWeight is tested as part of the semiring test suite:

| Category             | Tests                                                    |
|----------------------|----------------------------------------------------------|
| **Axiom verification** | All 7 axioms with concrete numerical examples          |
| **Bottleneck**       | min-based times, multi-step paths                        |
| **StarSemiring**     | `star(a) = 1.0` for various a in [0, 1]                 |
| **Ordering**         | Reversed `Ord`, `total_cmp` determinism                  |
| **degree()**         | Accessor correctness                                     |
| **Lattice**          | Absorption laws, double idempotency                      |

---

## 13. Source References

| Component                     | File                        | Lines       |
|-------------------------------|-----------------------------|-------------|
| Struct definition             | `automata/semiring.rs`      | 2267        |
| Constructor & `degree()`      | `automata/semiring.rs`      | 2269--2285  |
| `Semiring` impl               | `automata/semiring.rs`      | 2287--2321  |
| `Debug` / `Display`           | `automata/semiring.rs`      | 2323--2333  |
| `PartialEq` / `Eq`            | `automata/semiring.rs`      | 2335--2341  |
| `Ord` (reversed)              | `automata/semiring.rs`      | 2349--2355  |
| `Hash`                        | `automata/semiring.rs`      | 2357--2361  |
| `Default = one()`             | `automata/semiring.rs`      | 2363--2367  |
| Trait impls                   | `automata/semiring.rs`      | 2369--2371  |
| `StarSemiring`                | `automata/semiring.rs`      | 2373--2380  |

---

## 14. Cross-References

- **ViterbiWeight**: [viterbi-weight.md](viterbi-weight.md) -- shares [0,1] carrier and max ⊕ but uses multiplicative (not bottleneck) ⊗
- **BooleanWeight**: [boolean-weight.md](boolean-weight.md) -- FuzzyWeight with carrier restricted to {0, 1}
- **TropicalWeight**: [tropical-weight.md](tropical-weight.md) -- uses min ⊕ (complementary to FuzzyWeight's max ⊕)
- **ArcticWeight**: [arctic-weight.md](arctic-weight.md) -- shares max ⊕ but uses additive (not bottleneck) ⊗ on unbounded reals
- **Recovery**: `recovery.rs` -- uses fuzzy plausibility for repair strategy ranking
- **Prediction**: `prediction.rs` -- dispatch confidence via possibilistic reasoning
- **Lint**: `lint.rs` -- true-positive likelihood scoring
