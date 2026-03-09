# ViterbiWeight -- Design & Pipeline Integration

> **Date:** 2026-03-09

ViterbiWeight works in probability space `[0, 1]` rather than
negative-log space. Where TropicalWeight selects the minimum cost,
ViterbiWeight selects the maximum probability. The two are isomorphic
via the `-ln` transform, but ViterbiWeight avoids log/exp overhead when
probabilities are already available, and its `max`/`*` operations are
more intuitive for users reasoning about likelihoods.

---

## Table of Contents

1. [Intuition](#1-intuition)
2. [Mathematical Definition](#2-mathematical-definition)
3. [Data Structure](#3-data-structure)
4. [Semiring Operations](#4-semiring-operations)
5. [Isomorphism with TropicalWeight](#5-isomorphism-with-tropicalweight)
6. [Reversed Ord Semantics](#6-reversed-ord-semantics)
7. [Trait Hierarchy](#7-trait-hierarchy)
8. [Pipeline Integration](#8-pipeline-integration)
9. [Rust API](#9-rust-api)
10. [Test Coverage](#10-test-coverage)
11. [Source References](#11-source-references)
12. [Cross-References](#12-cross-references)

---

## 1. Intuition

ViterbiWeight encodes the probability of a parse path. A path with
probability 0.8 is more likely than one with probability 0.3, so
the ⊕ (plus) operation selects the maximum. Sequencing two independent
probabilistic steps multiplies their probabilities (standard
conditional probability), so ⊗ (times) is ordinary multiplication.

```
higher probability  =  more likely path  =  preferred parse
```

The name "Viterbi" comes from the Viterbi algorithm for finding the
most probable path through a hidden Markov model -- the exact
algorithm used for PraTTaIL's lattice disambiguation.

---

## 2. Mathematical Definition

```
V  =  ( [0, 1],  max,  *,  0.0,  1.0 )
```

| Component              | Symbol | Concrete value | Meaning                             |
|------------------------|--------|----------------|-------------------------------------|
| Carrier set            | K      | [0, 1]         | Probabilities (zero to one)         |
| Addition (⊕)           | max    | max(a, b)      | Select most probable alternative    |
| Multiplication (⊗)     | *      | a * b          | Joint probability of sequence       |
| Additive identity (0)  | 0.0    | `0.0_f64`      | Impossible path (probability zero)  |
| Multiplicative identity| 1.0    | `1.0_f64`      | Certain step (probability one)      |

### Semiring axioms

| Axiom                  | Verification (a=0.8, b=0.5, c=0.3)                         |
|------------------------|-------------------------------------------------------------|
| Additive identity      | max(0.0, 0.8) = 0.8 = a                                    |
| Additive commutativity | max(0.8, 0.5) = max(0.5, 0.8) = 0.8                        |
| Additive associativity | max(max(0.8, 0.5), 0.3) = max(0.8, max(0.5, 0.3)) = 0.8   |
| Mult. identity         | 1.0 * 0.8 = 0.8 * 1.0 = 0.8                                |
| Mult. associativity    | (0.8*0.5)*0.3 = 0.8*(0.5*0.3) = 0.12                       |
| Left distributivity    | 0.8 * max(0.5, 0.3) = max(0.8*0.5, 0.8*0.3) = 0.4         |
| Zero annihilation      | 0.0 * 0.8 = 0.8 * 0.0 = 0.0                                |

All axioms hold. V is a valid semiring.

---

## 3. Data Structure

```rust
#[derive(Clone, Copy)]
pub struct ViterbiWeight(pub f64);
```

Single `f64` field storing a probability in `[0.0, 1.0]`. The `new()`
constructor includes a `debug_assert!` to validate the range:

```rust
pub fn new(probability: f64) -> Self {
    debug_assert!(
        (0.0..=1.0).contains(&probability),
        "ViterbiWeight: probability must be in [0, 1], got {probability}"
    );
    ViterbiWeight(probability)
}
```

**Memory**: 8 bytes, stack-allocated, `Copy`.

---

## 4. Semiring Operations

| Operation   | Code                                  | Semantics                     |
|-------------|---------------------------------------|-------------------------------|
| `zero()`    | `ViterbiWeight(0.0)`                  | Impossible path               |
| `one()`     | `ViterbiWeight(1.0)`                  | Certain step                  |
| `plus()`    | `ViterbiWeight(self.0.max(other.0))`  | Most probable alternative     |
| `times()`   | `ViterbiWeight(self.0 * other.0)`     | Joint probability             |
| `is_zero()` | `self.0 == 0.0`                       | Exact zero check              |
| `is_one()`  | `self.0 == 1.0`                       | Exact one check               |
| `approx_eq` | `(self.0 - other.0).abs() <= epsilon` | Convergence check             |

### Design decision: no `from_priority()`

Unlike TropicalWeight, ViterbiWeight does not provide a `from_priority()`
constructor. Token priorities are integer values in [0, 10] that map
naturally to cost space (lower is better) but not to probability space
(where the mapping `priority / 10.0` would conflate distinct priority
levels). Use `TropicalWeight::from_priority()` and then convert with
`ViterbiWeight::from_tropical()` if needed.

---

## 5. Isomorphism with TropicalWeight

ViterbiWeight and TropicalWeight are related by the negative-log
transform:

```
                 -ln
ViterbiWeight(p) ────▶ TropicalWeight(-ln(p))
                 exp
ViterbiWeight(e^{-w}) ◀──── TropicalWeight(w)
```

| ViterbiWeight | TropicalWeight | Transform                |
|---------------|----------------|--------------------------|
| 1.0           | 0.0            | -ln(1.0) = 0.0          |
| 0.5           | ~0.693         | -ln(0.5) = ln(2)        |
| 0.0           | +inf           | -ln(0.0) = +inf         |
| max(a,b)      | min(-ln a,-ln b)| max(a,b) <-> min(w,w')  |
| a * b         | (-ln a)+(-ln b)| ln(ab) = ln a + ln b    |

### Conversion API

```rust
/// Convert from a TropicalWeight (negative log-probability).
pub fn from_tropical(w: TropicalWeight) -> Self {
    if w.is_zero() { ViterbiWeight(0.0) }
    else { ViterbiWeight((-w.value()).exp()) }
}

/// Convert to a TropicalWeight (negative log-probability).
pub fn to_tropical(self) -> TropicalWeight {
    if self.0 == 0.0 { TropicalWeight::infinity() }
    else { TropicalWeight(-self.0.ln()) }
}
```

**Edge cases**: Zero probability maps to infinite cost (unreachable).
Infinite cost maps to zero probability (impossible).

### When to use which

| Scenario                               | Preferred Weight          | Reason                        |
|----------------------------------------|---------------------------|-------------------------------|
| Dispatch ordering (priority-based)     | TropicalWeight            | `from_priority()` available   |
| Token lattice Viterbi                  | TropicalWeight            | Standard in pipeline          |
| Probabilistic model output             | ViterbiWeight             | Avoids log/exp overhead       |
| Product with counting (confidence)     | ViterbiWeight             | Intuitive probability space   |
| Forward-backward training              | LogWeight                 | Numerical stability           |

---

## 6. Reversed Ord Semantics

ViterbiWeight implements `Ord` with *reversed* semantics: higher
probability compares as "lower" (better) in the ordering:

```rust
impl Ord for ViterbiWeight {
    fn cmp(&self, other: &Self) -> Ordering {
        other.0.total_cmp(&self.0)  // Reversed!
    }
}
```

**Rationale**: PraTTaIL's generic algorithms use `min` to select the
"best" alternative (following the tropical convention where lower =
better). By reversing the ordering, `min(ViterbiWeight(0.8),
ViterbiWeight(0.3))` returns `ViterbiWeight(0.8)` -- the higher
probability. This allows the same generic algorithm to work with both
tropical (lower cost = better) and Viterbi (higher probability =
better) weights without modification.

```
Ordering::Less    means "better"
ViterbiWeight(0.8) < ViterbiWeight(0.3)    (0.8 is better)
TropicalWeight(1.0) < TropicalWeight(5.0)  (1.0 is better)
```

---

## 7. Trait Hierarchy

ViterbiWeight implements the full trait hierarchy:

| Trait                | Status       | Justification                                          |
|----------------------|--------------|--------------------------------------------------------|
| `DetectableZero`     | Implemented  | `is_zero()` is O(1): `self.0 == 0.0`                  |
| `IdempotentSemiring` | Implemented  | `max(a, a) = a` for all a                              |
| `CompleteSemiring`   | Implemented  | Idempotent plus guarantees convergence                 |
| `StarSemiring`       | Implemented  | `star(a) = 1.0` always                                |

### StarSemiring: star(a) = 1.0

```rust
impl StarSemiring for ViterbiWeight {
    fn star(&self) -> Self {
        ViterbiWeight(1.0)
    }
}
```

**Derivation**: `star(a) = max(1.0, a, a^2, a^3, ...)`. For any
`a in [0, 1]`, the powers `a^k` are non-increasing (`a^{k+1} <= a^k`).
The maximum of this sequence is always the first term: `1.0` (the
multiplicative identity). Therefore `star(a) = 1.0` for all a.

---

## 8. Pipeline Integration

### 8a. Feature gating

ViterbiWeight is available unconditionally (no feature gate).

### 8b. Use cases

| Use Case                        | How ViterbiWeight Is Used                                |
|---------------------------------|----------------------------------------------------------|
| **Probabilistic lattice**       | Edge weights as probabilities for HMM-style disambiguation|
| **Confidence product weight**   | `ProductWeight<ViterbiWeight, TropicalWeight>` for joint confidence + cost |
| **Recovery plausibility**       | Probability-space repair scoring in `recovery.rs`        |
| **Provenance confidence**       | Target of `ProvenanceWeight::evaluate()` with probability valuation |

### 8c. Relationship to Viterbi algorithm

Despite the name, `ViterbiWeight` is not the only weight used with
the Viterbi algorithm. The generic `viterbi_best_path_beam()` accepts
any `Semiring + Ord`. ViterbiWeight is simply a convenient choice when
weights are naturally in probability space.

---

## 9. Rust API

### Construction

```rust
use prattail::automata::semiring::{ViterbiWeight, TropicalWeight, Semiring};

let p = ViterbiWeight::new(0.8);          // probability 0.8
let q = ViterbiWeight(0.5);               // direct construction (no range check)
let zero = ViterbiWeight::zero();         // 0.0 (impossible)
let one = ViterbiWeight::one();           // 1.0 (certain)
```

### Operations

```rust
let best = p.plus(&q);                   // max(0.8, 0.5) = 0.8
let joint = p.times(&q);                 // 0.8 * 0.5 = 0.4

assert!(p.probability() == 0.8);
```

### Conversion

```rust
let tw = TropicalWeight::new(0.693);
let vw = ViterbiWeight::from_tropical(tw);   // ~0.5
let tw2 = vw.to_tropical();                  // ~0.693
```

---

## 10. Test Coverage

ViterbiWeight is tested as part of the semiring test suite in
`semiring.rs`:

| Category             | Tests                                                    |
|----------------------|----------------------------------------------------------|
| **Axiom verification** | plus commutativity, associativity; times associativity; identity; zero annihilation; distributivity |
| **Conversion**       | `from_tropical` round-trip, edge cases (zero, one, infinity) |
| **StarSemiring**     | `star(a) = 1.0` for various a values                    |
| **Ordering**         | Reversed `Ord` semantics, `total_cmp` consistency        |
| **Hash/Eq**          | `to_bits()`-based `Hash`, `total_cmp`-based `PartialEq`  |

---

## 11. Source References

| Component                     | File                        | Lines       |
|-------------------------------|-----------------------------|-------------|
| Struct definition             | `automata/semiring.rs`      | 1942        |
| Constructors & accessors      | `automata/semiring.rs`      | 1944--1980  |
| `Semiring` impl               | `automata/semiring.rs`      | 1982--2016  |
| `Debug` / `Display`           | `automata/semiring.rs`      | 2018--2028  |
| `PartialEq` / `Eq`            | `automata/semiring.rs`      | 2030--2036  |
| `Ord` (reversed)              | `automata/semiring.rs`      | 2044--2052  |
| `Hash`                        | `automata/semiring.rs`      | 2054--2058  |
| `Default = one()`             | `automata/semiring.rs`      | 2060--2064  |
| Trait impls                   | `automata/semiring.rs`      | 2066--2068  |
| `StarSemiring`                | `automata/semiring.rs`      | 2070--2077  |

---

## 12. Cross-References

- **Theory**: [Tropical Weight](../../../theory/wfst/semirings/tropical-weight.md) -- isomorphic weight in negative-log space
- **TropicalWeight design**: [tropical-weight.md](tropical-weight.md) -- the default dispatch weight; ViterbiWeight converts to/from
- **CountingWeight**: [counting-weight.md](counting-weight.md) -- often paired with ViterbiWeight in `ProductWeight` or `TensorWeight` for confidence-count correlation
- **LogWeight**: [log-weight.md](log-weight.md) -- for numerically stable forward-backward training (where ViterbiWeight would lose precision)
- **ProductWeight**: [product-weight.md](product-weight.md) -- `ProductWeight<ViterbiWeight, TropicalWeight>` for joint confidence + cost
- **Lattice/Viterbi**: `lattice.rs` -- generic Viterbi works with ViterbiWeight via reversed `Ord`
- **ProvenanceWeight**: [provenance-weight.md](provenance-weight.md) -- ViterbiWeight is a target of the provenance homomorphism (confidence valuation)
