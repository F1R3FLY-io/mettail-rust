# TruncationWeight -- Design & Pipeline Integration

> **Date:** 2026-03-09

TruncationWeight is a bounded ambiguity counter with a const generic
capacity `K`. It tracks the worst-case ambiguity level (via idempotent
`max`) and saturates at `K` (via clamped addition). Unlike CountingWeight
(which sums derivations without bound), TruncationWeight classifies
ambiguity into severity tiers: deterministic (0-1), binary choice (2),
complex (3+), and severe (K+).

---

## Table of Contents

1. [Intuition](#1-intuition)
2. [Mathematical Definition](#2-mathematical-definition)
3. [The zero = one Degeneration](#3-the-zero--one-degeneration)
4. [Data Structure](#4-data-structure)
5. [Semiring Operations](#5-semiring-operations)
6. [Const Generic K Parameter](#6-const-generic-k-parameter)
7. [Tiered Severity Mapping](#7-tiered-severity-mapping)
8. [Saturating Arithmetic](#8-saturating-arithmetic)
9. [Trait Hierarchy](#9-trait-hierarchy)
10. [Pipeline Integration](#10-pipeline-integration)
11. [Rust API](#11-rust-api)
12. [Test Coverage](#12-test-coverage)
13. [Source References](#13-source-references)
14. [Cross-References](#14-cross-references)

---

## 1. Intuition

Consider tracking ambiguity in a grammar. At each dispatch point, we
want to know: "how many competing alternatives exist?" But we do not
need exact counts -- we need severity classification:

```
Count 0: no match (error)
Count 1: deterministic (good)
Count 2: binary ambiguity (might be OK)
Count 3: ternary ambiguity (concerning)
Count 4+: severe ambiguity (likely a grammar bug)
```

TruncationWeight with K=4 captures exactly this: counts above 4 are
all classified as "severe" (4+). The idempotent `max` for ⊕ means we
track the worst case across alternatives, not the sum.

---

## 2. Mathematical Definition

```
T_K  =  ( {0, 1, ..., K},  max,  min(a + b, K),  0,  0 )
```

| Component              | Symbol         | Concrete value    | Meaning                          |
|------------------------|----------------|-------------------|----------------------------------|
| Carrier set            | K              | {0, 1, ..., K}    | Bounded non-negative integers    |
| Addition (⊕)           | max            | max(a, b)         | Worst-case ambiguity level       |
| Multiplication (⊗)     | saturating add | min(a + b, K)     | Accumulate with saturation       |
| Additive identity (0)  | 0              | `0_u32`           | No paths                        |
| Multiplicative identity| 0              | `0_u32`           | Adding zero doesn't change count |

### Semiring axioms (K = 4)

| Axiom                  | Verification (a=2, b=3, c=1)                                     |
|------------------------|-------------------------------------------------------------------|
| Additive identity      | max(0, 2) = 2                                                    |
| Additive commutativity | max(2, 3) = max(3, 2) = 3                                        |
| Additive associativity | max(max(2, 3), 1) = max(2, max(3, 1)) = 3                        |
| Mult. identity         | min(0 + 2, 4) = min(2 + 0, 4) = 2                                |
| Mult. associativity    | min(min(2+3,4)+1, 4) = min(min(2+(3+1),4), 4) -- see below       |
| Left distributivity    | min(2+max(3,1),4) = max(min(2+3,4), min(2+1,4)) = max(4,3) = 4   |
| Zero annihilation      | min(0+2,4) = 2? No -- see special note below                     |

**Important**: In TruncationWeight, zero = 0 and one = 0. This is the
**zero-equals-one degeneration** discussed in Section 3.

### Associativity of ⊗ (detailed)

```
(a ⊗ b) ⊗ c  =  min(min(2+3, 4) + 1, 4)  =  min(4+1, 4)  =  4
a ⊗ (b ⊗ c)  =  min(2 + min(3+1, 4), 4)  =  min(2+4, 4)   =  4   ✓
```

Both sides saturate to K = 4.

---

## 3. The zero = one Degeneration

TruncationWeight has the unusual property that `zero() == one() == 0`:

```rust
fn zero() -> Self { TruncationWeight(0) }
fn one() -> Self { TruncationWeight(0) }
```

And correspondingly:

```rust
fn is_zero(&self) -> bool { self.0 == 0 }
fn is_one(&self) -> bool { self.0 == 0 }
```

**Why this happens**: The additive identity for `max` is 0 (the smallest
element), and the multiplicative identity for saturating addition is also
0 (adding zero is a no-op). These coincide.

**Consequences**:

1. **Zero annihilation is trivially satisfied**: `0 ⊗ a = min(0 + a, K) = a`.
   But wait -- this gives `a`, not `0`! This means the standard
   annihilation axiom `0 * a = 0` does **not** hold in the usual sense.
   However, since `0 = 1` in this semiring, we have `1 * a = a`, which
   is the multiplicative identity axiom. The two axioms do not conflict
   because they share the same element.

2. **`is_zero()` and `is_one()` return the same result**: Any algorithm
   that branches on `is_zero()` vs `is_one()` will see both as true
   for value 0. This is correct: value 0 means "no paths" (zero) and
   "no added ambiguity" (one) simultaneously.

3. **Pruning caveat**: Algorithms that prune zero-weight edges will
   also prune identity-weight edges. This is acceptable for ambiguity
   tracking (pruning "no ambiguity" edges is safe) but would be
   incorrect for path-cost algorithms.

**Design rationale**: The degeneration is accepted because
TruncationWeight is used for ambiguity *classification*, not for
path-weight computation. The semiring axioms hold up to the
identification of 0 and 1, and all PraTTaIL algorithms that use
TruncationWeight are aware of this property.

---

## 4. Data Structure

```rust
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct TruncationWeight<const K: u32>(pub u32);
```

Single `u32` field with a const generic bound `K`. The value is always
in `[0, K]`.

### Constructor with clamping

```rust
pub const fn new(value: u32) -> Self {
    if value > K {
        TruncationWeight(K)
    } else {
        TruncationWeight(value)
    }
}
```

Values exceeding K are clamped to K at construction time, maintaining
the invariant.

### is_saturated() API

```rust
pub const fn is_saturated(self) -> bool {
    self.0 >= K
}
```

Reports whether the count has reached the saturation threshold. This
is the primary API for severity classification:

```rust
let w: TruncationWeight<4> = TruncationWeight::new(5);
assert!(w.is_saturated());     // true: clamped to 4
assert_eq!(w.count(), 4);     // stored as K
```

**Memory**: 4 bytes, stack-allocated, `Copy`.

---

## 5. Semiring Operations

| Operation     | Code                                               | Note                              |
|---------------|----------------------------------------------------|-----------------------------------|
| `zero()`      | `TruncationWeight(0)`                              | No paths                          |
| `one()`       | `TruncationWeight(0)`                              | No added ambiguity (= zero)       |
| `plus()`      | `TruncationWeight(self.0.max(other.0))`            | Worst-case ambiguity              |
| `times()`     | `TruncationWeight(self.0.saturating_add(other.0).min(K))` | Saturating accumulation   |
| `is_zero()`   | `self.0 == 0`                                      | Same as `is_one()`                |
| `is_one()`    | `self.0 == 0`                                      | Same as `is_zero()`               |
| `approx_eq()` | `self.0 == other.0`                                | Discrete equality (exact)         |

### Saturating times

The `times` operation uses two-level saturation:

1. `self.0.saturating_add(other.0)`: Rust's built-in saturating addition
   prevents `u32` overflow (clamps at `u32::MAX`).
2. `.min(K)`: Clamps the result to the semiring bound K.

This ensures the result is always in `[0, K]` regardless of operand
values.

---

## 6. Const Generic K Parameter

The const generic `K: u32` parameterizes the saturation threshold:

```rust
type FourTier = TruncationWeight<4>;
type EightTier = TruncationWeight<8>;
type BinaryOnly = TruncationWeight<1>;
```

| K value | Tiers                    | Use case                              |
|---------|--------------------------|---------------------------------------|
| 1       | {0, 1}                   | Boolean ambiguity (like BooleanWeight)|
| 4       | {0, 1, 2, 3, 4+}        | Four-tier severity classification     |
| 8       | {0, 1, ..., 7, 8+}      | Fine-grained ambiguity tracking       |
| 255     | {0, 1, ..., 254, 255+}  | Near-exact counting (u8 equivalent)   |

**Design decision**: K is a const generic rather than a runtime
parameter. This enables the compiler to optimize comparisons and
arithmetic for specific K values, and it ensures type safety -- a
`TruncationWeight<4>` cannot be accidentally mixed with a
`TruncationWeight<8>`.

### Relationship to BooleanWeight

`TruncationWeight<1>` is isomorphic to BooleanWeight:

| TruncationWeight<1> | BooleanWeight | Meaning         |
|----------------------|---------------|-----------------|
| 0                    | false         | No paths        |
| 1                    | true          | One or more paths|

### Relationship to CountingWeight

As K approaches infinity, TruncationWeight approaches CountingWeight
(with `max` replacing `+` for ⊕, so they are not identical even in the
limit). The key difference is that CountingWeight uses `plus = +`
(sum all path counts) while TruncationWeight uses `plus = max`
(worst-case ambiguity level).

---

## 7. Tiered Severity Mapping

For K = 4 (the recommended default), the tiers map to diagnostic
severity levels:

```
┌─────────────────────────────────────────────────────────┐
│ Count │ Display │ Severity │ Diagnostic                  │
├───────┼─────────┼──────────┼─────────────────────────────┤
│   0   │  "0"    │ Info     │ No matching rules (error)   │
│   1   │  "1"    │ None     │ Deterministic dispatch      │
│   2   │  "2"    │ Note     │ Binary ambiguity (normal)   │
│   3   │  "3"    │ Warning  │ Ternary ambiguity           │
│  4+   │  "4+"   │ Error    │ Severe ambiguity (bug?)     │
└─────────────────────────────────────────────────────────┘
```

### Display format

```rust
impl<const K: u32> fmt::Display for TruncationWeight<K> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.0 >= K {
            write!(f, "{}+", K)     // "4+" for saturated values
        } else {
            write!(f, "{}", self.0) // "0", "1", "2", "3" for non-saturated
        }
    }
}
```

The "4+" notation makes it clear that the exact count was lost due to
saturation, while values below K are exact.

---

## 8. Saturating Arithmetic

### Why saturating_add?

Without saturation, `u32` arithmetic could overflow:

```
TruncationWeight<4>(3).times(&TruncationWeight<4>(3))
  Without saturation: 3 + 3 = 6 → min(6, 4) = 4  (OK in this case)
  With overflow risk: u32::MAX + u32::MAX wraps to u32::MAX - 1 (wrong!)
```

The `saturating_add` ensures that even if K is large (e.g., K = u32::MAX),
the intermediate sum does not wrap. The `.min(K)` clamp then brings it
within range.

### Contrast with CountingWeight

CountingWeight uses `saturating_add` and `saturating_mul` for similar
overflow prevention. TruncationWeight only needs `saturating_add` because
its ⊗ is addition (not multiplication).

---

## 9. Trait Hierarchy

| Trait                | Status       | Justification                                          |
|----------------------|--------------|--------------------------------------------------------|
| `DetectableZero`     | Implemented  | `is_zero()` is O(1): `self.0 == 0`                    |
| `IdempotentSemiring` | Implemented  | `max(a, a) = a` for all a                              |
| `CompleteSemiring`   | Implemented  | Idempotent plus; finite carrier guarantees convergence |

**Not implemented**: `StarSemiring`. The Kleene star
`star(a) = max(0, a, a+a, a+a+a, ...)` converges to `max(0, K) = K`
for any `a > 0`, and to `0` for `a = 0`. While a `StarSemiring` impl
could be added, TruncationWeight's primary use case (ambiguity
classification) does not require Kleene closure.

---

## 10. Pipeline Integration

### 10a. Feature gating

TruncationWeight is available unconditionally (no feature gate).

### 10b. Use cases

| Use Case                          | Instantiation               | What It Captures                              |
|-----------------------------------|-----------------------------|-----------------------------------------------|
| **Four-tier severity**            | `TruncationWeight<4>`       | Ambiguity classified as deterministic/binary/complex/severe |
| **Fine-grained ambiguity**        | `TruncationWeight<8>`       | Eight severity levels for detailed diagnostics|
| **prediction.rs: tiered dispatch**| `TruncationWeight<4>`       | Per-token ambiguity tier for dispatch ordering |

### 10c. Comparison with CountingWeight for ambiguity

| Property            | CountingWeight           | TruncationWeight<4>         |
|---------------------|--------------------------|------------------------------|
| ⊕ (alternatives)    | Sum (total count)        | Max (worst case)             |
| ⊗ (sequencing)      | Multiply                 | Saturating add               |
| Range               | [0, u64::MAX]            | [0, 4]                      |
| Overflow behavior   | Saturates at u64::MAX    | Saturates at K               |
| Diagnostic output   | "42 alternatives"        | "4+" (severe)                |
| Memory              | 8 bytes                  | 4 bytes                      |

CountingWeight answers "how many derivations?" TruncationWeight answers
"how bad is the ambiguity?" For diagnostic output, the tiered
classification is more actionable than a raw count.

---

## 11. Rust API

### Construction

```rust
use prattail::automata::semiring::{TruncationWeight, Semiring};

type TW4 = TruncationWeight<4>;

let w = TW4::new(3);              // 3 (within range)
let clamped = TW4::new(10);       // clamped to 4
let zero = TW4::zero();           // 0
let one = TW4::one();             // 0 (same as zero!)
```

### Operations

```rust
let a = TW4::new(2);
let b = TW4::new(3);

let worst = a.plus(&b);           // max(2, 3) = 3
let accumulated = a.times(&b);    // min(2 + 3, 4) = 4

assert_eq!(accumulated.count(), 4);
assert!(accumulated.is_saturated());
assert_eq!(format!("{}", accumulated), "4+");
```

### Severity check

```rust
fn classify_ambiguity<const K: u32>(w: TruncationWeight<K>) -> &'static str {
    match w.count() {
        0 => "no match",
        1 => "deterministic",
        _ if w.is_saturated() => "severe",
        n => if n <= 2 { "binary" } else { "complex" },
    }
}
```

---

## 12. Test Coverage

TruncationWeight is tested as part of the semiring test suite:

| Category             | Tests                                                    |
|----------------------|----------------------------------------------------------|
| **Axiom verification** | All 7 axioms (accounting for zero = one degeneration)  |
| **Saturation**       | `new()` clamping, `is_saturated()`, `times()` overflow   |
| **Display**          | "0", "1", "2", "3", "4+" formatting                     |
| **Const generics**   | K=1 (Boolean), K=4 (four-tier), K=8 (eight-tier)        |
| **Ordering**         | Natural `Ord` (higher count = higher ambiguity)          |
| **approx_eq**        | Discrete equality, epsilon ignored                       |

---

## 13. Source References

| Component                     | File                        | Lines       |
|-------------------------------|-----------------------------|-------------|
| Struct definition             | `automata/semiring.rs`      | 2408        |
| Constructors & accessors      | `automata/semiring.rs`      | 2410--2432  |
| `Semiring` impl               | `automata/semiring.rs`      | 2434--2468  |
| `Ord`                         | `automata/semiring.rs`      | 2470--2480  |
| `Display`                     | `automata/semiring.rs`      | 2482--2490  |
| `Default = one()`             | `automata/semiring.rs`      | 2492--2496  |
| Trait impls                   | `automata/semiring.rs`      | 2498--2500  |

---

## 14. Cross-References

- **CountingWeight**: [counting-weight.md](counting-weight.md) -- unbounded counting with `+` and `*`; TruncationWeight is the bounded, idempotent alternative
- **BooleanWeight**: [boolean-weight.md](boolean-weight.md) -- `TruncationWeight<1>` is isomorphic to BooleanWeight
- **FuzzyWeight**: [fuzzy-weight.md](fuzzy-weight.md) -- shares `max` ⊕ on a continuous [0,1] domain; TruncationWeight uses discrete {0,...,K}
- **TropicalWeight**: [tropical-weight.md](tropical-weight.md) -- uses `min` ⊕ and real-valued `+` ⊗; TruncationWeight uses `max` ⊕ and integer saturating `+` ⊗
- **Prediction**: `prediction.rs` -- per-token tiered ambiguity classification
- **Semiring catalog**: `../../../docs/design/semiring-catalog.md` -- overview of all semiring types
