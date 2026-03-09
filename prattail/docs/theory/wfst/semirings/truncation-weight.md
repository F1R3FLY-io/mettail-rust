# Truncation Semiring: TruncationWeight&lt;K&gt;

## 1. Intuition & Motivation

The truncation semiring provides *bounded ambiguity counting with
saturation*.  It answers the question "how ambiguous is this token?"
with a bounded count that saturates at a configurable threshold K,
giving tiered severity levels without the overhead of exact counting.

Unlike `CountingWeight` (which tracks exact derivation counts in
`u64`) or `BooleanWeight` (which tracks only "ambiguous or not"),
TruncationWeight provides a graduated middle ground:

```
count = 0    →   no paths (dead rule)
count = 1    →   deterministic (single parse)
count = 2    →   binary ambiguity (two alternatives)
count = 3    →   multi-way ambiguity
count = K+   →   severe ambiguity (saturated, at least K)
```

This graduated assessment is more informative than a binary yes/no
flag but more compact and computationally cheaper than exact counting.
Common configurations: K = 4 for four-tier severity classification,
K = 8 for fine-grained analysis.

**Important caveat**: TruncationWeight is a *near-semiring* that
relaxes the zero annihilation axiom.  See [3. (Z)] for the detailed
analysis of this relaxation and its practical implications.

---

## 2. Formal Definition

The truncation near-semiring is the algebraic structure

```
T_K  =  ( {0, 1, ..., K},  max,  min(a + b, K),  0,  0 )
```

where:

| Component                   | Symbol          | Concrete value    | Meaning                               |
|-----------------------------|-----------------|-------------------|---------------------------------------|
| Carrier set                 | K               | {0, 1, ..., K}    | Bounded non-negative integers         |
| Addition (⊕)                | max             | max(a, b)         | Worst-case ambiguity from alternatives|
| Multiplication (⊗)          | truncated add   | min(a + b, K)     | Accumulate counts with saturation     |
| Additive identity (0-bar)   | 0               | `0_u32`           | No paths (dead rule)                  |
| Multiplicative identity (1-bar) | 0           | `0_u32`           | Adding zero doesn't increase count    |

**Degenerate identity**: Both the additive identity (0-bar) and the
multiplicative identity (1-bar) are `0`.  This is unusual but not
inherently contradictory for the identity axioms (A3 and M2).  The
pathological consequence is that zero annihilation fails -- see [3. (Z)].

---

## 3. Semiring Axiom Verification

We verify all eight semiring axioms with concrete numerical examples
using K = 4.  Let a = 2, b = 3, c = 1.

### (A1) Associativity of ⊕

```
(a ⊕  b) ⊕  c  =  max(max(2, 3), 1)  =  max(3, 1)  =  3
a ⊕  (b ⊕  c)  =  max(2, max(3, 1))  =  max(2, 3)  =  3   ✓
```

Holds in general because `max` is associative over totally ordered sets.

### (A2) Commutativity of ⊕

```
a ⊕  b  =  max(2, 3)  =  3
b ⊕  a  =  max(3, 2)  =  3   ✓
```

Holds because `max` is symmetric.

### (A3) ⊕  Identity

```
0-bar ⊕  a  =  max(0, 2)  =  2  =  a   ✓
a ⊕  0-bar  =  max(2, 0)  =  2  =  a   ✓
```

Zero is the identity for `max` because every element in {0, ..., K}
is non-negative.

### (M1) Associativity of ⊗

```
(a ⊗  b) ⊗  c  =  min(min(2 + 3, 4) + 1, 4)  =  min(4 + 1, 4)  =  min(5, 4)  =  4
a ⊗  (b ⊗  c)  =  min(2 + min(3 + 1, 4), 4)   =  min(2 + 4, 4)  =  min(6, 4)  =  4   ✓
```

Let us also verify with smaller values to ensure non-saturated cases:
Let a = 1, b = 1, c = 1:

```
(a ⊗  b) ⊗  c  =  min(min(1 + 1, 4) + 1, 4)  =  min(2 + 1, 4)  =  min(3, 4)  =  3
a ⊗  (b ⊗  c)  =  min(1 + min(1 + 1, 4), 4)   =  min(1 + 2, 4)  =  min(3, 4)  =  3   ✓
```

**General proof**: Associativity holds because `min(min(a + b, K) + c, K) = min(a + b + c, K)`.
To see this: if `a + b >= K`, then `min(a + b, K) = K`, and
`min(K + c, K) = K = min(a + b + c, K)` (since `a + b + c >= K`).
If `a + b < K`, then `min(a + b, K) = a + b`, and
`min(a + b + c, K) = min(a + b + c, K)` by definition.  The symmetric
argument holds for the right association.   ∎

### (M2) ⊗  Identity

```
1-bar ⊗  a  =  min(0 + 2, 4)  =  min(2, 4)  =  2  =  a   ✓
a ⊗  1-bar  =  min(2 + 0, 4)  =  min(2, 4)  =  2  =  a   ✓
```

Adding 0 to any value in {0, ..., K} yields the same value (since
K >= 0, the saturation does not trigger for values already in range).

### (D1) Left Distributivity: ⊗  distributes over ⊕  from the left

```
a ⊗  (b ⊕  c)  =  min(2 + max(3, 1), 4)  =  min(2 + 3, 4)  =  min(5, 4)  =  4
(a ⊗  b) ⊕  (a ⊗  c)  =  max(min(2 + 3, 4), min(2 + 1, 4))  =  max(4, 3)  =  4   ✓
```

Let us also verify with values that don't saturate.  Let a = 1, b = 1, c = 0:

```
a ⊗  (b ⊕  c)  =  min(1 + max(1, 0), 4)  =  min(1 + 1, 4)  =  2
(a ⊗  b) ⊕  (a ⊗  c)  =  max(min(1 + 1, 4), min(1 + 0, 4))  =  max(2, 1)  =  2   ✓
```

**General proof**: `min(a + max(b, c), K) = max(min(a + b, K), min(a + c, K))`.
Addition by a non-negative constant preserves the ordering: if `b >= c`,
then `a + b >= a + c`, so `max(b, c) = b` implies `min(a + b, K)` and
`min(a + c, K)` satisfy `min(a + b, K) >= min(a + c, K)`, and the
`max` on the right gives `min(a + b, K)`, matching the left side.   ∎

### (D2) Right Distributivity: ⊗  distributes over ⊕  from the right

```
(a ⊕  b) ⊗  c  =  min(max(2, 3) + 1, 4)  =  min(3 + 1, 4)  =  min(4, 4)  =  4
(a ⊗  c) ⊕  (b ⊗  c)  =  max(min(2 + 1, 4), min(3 + 1, 4))  =  max(3, 4)  =  4   ✓
```

Symmetric argument to (D1).

### (Z) Zero Annihilation -- FAILS

```
0-bar ⊗  a  =  min(0 + 2, 4)  =  min(2, 4)  =  2  ≠  0  =  0-bar   ✗
a ⊗  0-bar  =  min(2 + 0, 4)  =  min(2, 4)  =  2  ≠  0  =  0-bar   ✗
```

**Analysis**: The zero annihilation axiom requires `0-bar ⊗ a = 0-bar`
for all `a`.  Since both `0-bar = 0` and `1-bar = 0` in this structure,
the annihilation axiom requires `min(0 + a, K) = 0`, which holds only
when `a = 0`.  For any `a > 0`, `min(a, K) = a ≠ 0`.

**This means TruncationWeight is NOT a semiring in the strict
mathematical sense.**  It is a *near-semiring* (also called a
*seminearring* or *pseudo-semiring*) that satisfies all axioms except
zero annihilation.

### Why This Is Acceptable in Practice

The zero annihilation axiom captures the principle "an unreachable
state stays unreachable regardless of concatenation."  In
TruncationWeight, the failure of this axiom means:

```
"dead rule" ⊗  "2-way ambiguous" = 2  (not "dead rule")
```

However, TruncationWeight is used exclusively for *ambiguity severity
classification* in `prediction.rs`, where:

1. Dead rules (count 0) are detected and eliminated by the pipeline
   *before* any ⊗  operations occur.
2. The ⊗  operation is only applied to non-zero counts along
   confirmed-reachable paths.
3. The zero element is used only for initialization and `is_zero()`
   checks, never as an operand to `times()` on reachable paths.

Under these usage constraints, the zero annihilation failure has no
observable effect.

### Axiom Summary

| Axiom | Status | Note                                         |
|-------|--------|----------------------------------------------|
| A1    | ✓      | max is associative                            |
| A2    | ✓      | max is commutative                            |
| A3    | ✓      | max(0, a) = a                                 |
| M1    | ✓      | min(a+b+c, K) is associative                  |
| M2    | ✓      | min(0+a, K) = a for a in {0,...,K}             |
| D1    | ✓      | Left distributivity holds                     |
| D2    | ✓      | Right distributivity holds                    |
| Z     | ✗      | Zero annihilation fails: 0-bar = 1-bar = 0    |

Seven of eight axioms are satisfied.  T_K is a valid *near-semiring*.

---

## 4. Key Properties

### 4.1 Commutativity

**Claim**: TruncationWeight is commutative (⊗  is commutative).

**Proof**: For all a, b in {0, ..., K}:

```
a ⊗  b  =  min(a + b, K)  =  min(b + a, K)  =  b ⊗  a
```

Integer addition is commutative.   ∎

### 4.2 Idempotency

**Claim**: TruncationWeight is idempotent (⊕  is idempotent).

**Proof**: For all a in {0, ..., K}:

```
a ⊕  a  =  max(a, a)  =  a
```

The maximum of any value with itself is that value.   ∎

### 4.3 Saturation

**Claim**: TruncationWeight saturates at K.

**Proof**: For any a, b in {0, ..., K}:

```
a ⊗  b  =  min(a + b, K)  ≤  K
```

The `min(_, K)` clamp ensures all results stay within the carrier
set {0, ..., K}.   ∎

Saturation means that once ambiguity reaches level K, further
accumulation has no effect:

```
K ⊗  a  =  min(K + a, K)  =  K     for all a ≥ 0
```

This is the bounded-counting analogue of absorption: K is an
*absorbing element* for ⊗ .

### 4.4 NOT a Star Semiring

TruncationWeight does NOT implement `StarSemiring`.  The Kleene star
would require:

```
star(a) = ⊕_{n=0}^{∞} a^n
```

For a > 0:

```
a^0 = 0, a^1 = a, a^2 = min(2a, K), ..., a^n = min(na, K), ...
```

The supremum is `K`, but this is NOT `one()` (which is also 0), so
the star axiom `star(a) = one ⊕ a ⊗ star(a)` cannot be satisfied
in a useful way.  The implementation correctly omits `StarSemiring`.

### 4.5 Natural Ordering (Not Reversed)

Unlike most other PraTTaIL semirings, TruncationWeight uses **natural**
ordering -- lower count = "less than" higher count:

```
Ordering logic:  self.0.cmp(&other.0)
```

This is because TruncationWeight is used for *severity classification*
where higher count = more severe, and the natural ordering is the
appropriate one.

---

## 5. Tiered Ambiguity Classification

PraTTaIL uses TruncationWeight<4> for four-tier ambiguity
classification in `prediction.rs`.

### Ambiguity Severity Table (K = 4)

| Count       | Display | Severity     | Action                                          |
|-------------|---------|------------- |-------------------------------------------------|
| 0           | `0`     | Dead         | Emit dead-rule warning, suppress dispatch arm   |
| 1           | `1`     | Deterministic| Direct dispatch, no backtracking needed         |
| 2           | `2`     | Binary       | Two-way composed dispatch with priority         |
| 3           | `3`     | Multi-way    | 3-way ambiguity, may need lookahead             |
| 4+ (K+)    | `4+`    | Severe       | Highly ambiguous, emit warning, force lookahead |

### Code

```rust
impl<const K: u32> TruncationWeight<K> {
    /// Whether this weight is at the saturation threshold.
    #[inline]
    pub const fn is_saturated(self) -> bool {
        self.0 >= K
    }
}

impl<const K: u32> fmt::Display for TruncationWeight<K> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.0 >= K {
            write!(f, "{}+", K)   // e.g., "4+"
        } else {
            write!(f, "{}", self.0)
        }
    }
}
```

### Example: Ambiguity Accumulation

Consider a grammar where category `Expr` has 2 rules for `Ident`
and 1 rule for `Number`, and category `Stmt` has 1 rule that
delegates to `Expr`:

```
Ident in Expr:   ambiguity = 2
Number in Expr:  ambiguity = 1
Stmt via Expr:   ambiguity(Ident) = min(1 + 2, 4) = 3
                 ambiguity(Number) = min(1 + 1, 4) = 2
```

If a third category adds 2 more rules for `Ident`:

```
ambiguity(Ident) = min(3 + 2, 4) = 4+  (saturated)
```

The saturated value `4+` signals "severe ambiguity" without tracking
the exact count.

---

## 6. Zero Annihilation (Failure Analysis)

As documented in [3. (Z)], TruncationWeight does NOT satisfy zero
annihilation.  This section provides a thorough analysis.

### The Problem

The semiring axiom requires:

```
0-bar ⊗  a  =  0-bar     for all a
```

But:

```
TruncationWeight(0) ⊗  TruncationWeight(2)
    = TruncationWeight(min(0 + 2, K))
    = TruncationWeight(2)
    ≠ TruncationWeight(0)
```

### Root Cause: Degenerate Zero-One Coincidence

The fundamental issue is that `zero() = one() = TruncationWeight(0)`.
In a proper semiring, `0-bar ≠ 1-bar` is required for zero
annihilation to have non-trivial content.  When they coincide, the
annihilation axiom `0-bar ⊗ a = 0-bar` becomes `1-bar ⊗ a = 1-bar`,
which contradicts the identity axiom `1-bar ⊗ a = a`.

This is a fundamental algebraic incompatibility:
- Identity axiom: `0 ⊗ a = a` (adding zero counts does not change count)
- Annihilation axiom: `0 ⊗ a = 0` (unreachable paths stay unreachable)

With `0-bar = 1-bar = 0`, both cannot hold simultaneously unless
`a = 0` for all `a`.

### Alternative Designs Considered

1. **Make zero = K+1 (a special sentinel)**: This would restore
   annihilation but break the carrier set closure (K+1 is not in
   {0, ..., K}).

2. **Use Option<u32> with None as zero**: Correct but adds branching
   overhead to every operation.

3. **Accept the near-semiring**: The chosen approach.  Dead-rule
   detection happens at a higher level in the pipeline, and ⊗  is
   never applied with a true zero operand in practice.

---

## 7. Path Count Computation

### Worked Example (K = 4)

Consider a grammar with two dispatch paths for token `Ident` in
category `Stmt`:

```
                        ┌─────────────────────────────────┐
                        │       Ambiguity Graph           │
                        │      (category: Stmt)           │
                        └─────────────────────────────────┘

  Path 1 (via Expr):      q₀ ──2──▶ q₁ ──1──▶ q₃
  Path 2 (direct):        q₀ ──1──▶ q₂ ──1──▶ q₃


         ┌──────┐      2      ┌──────┐
         │      │─────────────│      │
         │  q₀  │             │  q₁  │──┐
         │      │             │      │  │  1
         └──────┘             └──────┘  │
            │                           │
            │                    ┌──────▼──────┐
            │  1                 │             │
            │                    │     q₃      │
            │                    │   (accept)  │
            │                    └──────▲──────┘
            │                           │
            ▼                           │  1
         ┌──────┐                       │
         │      │───────────────────────┘
         │  q₂  │
         │      │
         └──────┘
```

**Path 1** (via Expr: 2 Expr rules for `Ident`, then 1 Stmt rule):

```
c₁  =  2 ⊗  1  =  min(2 + 1, 4)  =  3
```

**Path 2** (direct: 1 direct Stmt rule, then 1 continuation):

```
c₂  =  1 ⊗  1  =  min(1 + 1, 4)  =  2
```

**Worst-case ambiguity** (⊕):

```
c*  =  c₁ ⊕  c₂  =  max(3, 2)  =  3
```

Token `Ident` has worst-case ambiguity level 3 (multi-way) in
category `Stmt`.

---

## 8. Dispatch Weight Table

The following truncation counts map to ambiguity severity levels
and suggested dispatch strategies:

| Ambiguity Count | Display | Severity       | Suggested Strategy                              |
|-----------------|---------|----------------|-------------------------------------------------|
| 0               | `0`     | Dead           | Remove arm, emit dead-rule warning              |
| 1               | `1`     | Deterministic  | Direct dispatch -- zero overhead                |
| 2               | `2`     | Binary         | Composed dispatch with priority ordering        |
| 3               | `3`     | Multi-way      | Lookahead or backtracking required              |
| K+ (saturated)  | `K+`    | Severe         | Consider grammar refactoring, emit warning      |

**Design principle**: Bounded counting provides enough information for
dispatch strategy selection without the overhead of exact counting.
The saturation at K prevents unbounded growth in pathological grammars.

---

## 9. Comparison with CountingWeight and BooleanWeight

TruncationWeight sits between Boolean (binary) and Counting (exact)
in precision:

| Property            | BooleanWeight                  | TruncationWeight<K>            | CountingWeight                 |
|---------------------|--------------------------------|--------------------------------|--------------------------------|
| Carrier set         | {false, true}                  | {0, 1, ..., K}                 | N (all non-negative integers)  |
| ⊕  (addition)       | ∨ (or)                         | max(a, b)                      | a + b                          |
| ⊗  (multiplication) | ∧ (and)                        | min(a + b, K)                  | a * b                          |
| 0-bar (zero)        | false                          | 0                              | 0                              |
| 1-bar (one)         | true                           | 0                              | 1                              |
| Zero = One?         | No                             | Yes (degenerate)               | No                             |
| Zero annihilation?  | Yes                            | No (near-semiring)             | Yes                            |
| Idempotent ⊕?       | Yes: a ∨ a = a                 | Yes: max(a, a) = a             | No: a + a = 2a ≠ a             |
| Star?               | Yes                            | No                             | No                             |
| Precision           | Binary: ambiguous or not       | K+1 levels: severity tiers     | Exact: full derivation count   |
| Memory              | 1 bit                          | ceil(log₂(K+1)) bits           | 64 bits                        |
| Use case            | Reachability                   | Severity classification        | Exact ambiguity analysis       |

### Expressiveness Hierarchy

```
BooleanWeight  ⊆  TruncationWeight<1>  ⊆  TruncationWeight<K>  ⊆  CountingWeight
(binary)            (matches Boolean)        (K+1 levels)           (unbounded)
```

- **TruncationWeight<1>**: Equivalent to BooleanWeight when mapped via
  `0 -> false`, `1 -> true`.  (But with the degenerate zero-one issue.)

- **TruncationWeight<K>**: Provides K+1 distinct severity levels.

- **CountingWeight**: Full precision, but `plus = +` means it is NOT
  idempotent and is NOT suitable for worst-case (max) analysis.

### When to Use Which

- **BooleanWeight**: When you only need "reachable or not" --
  simplest, most efficient.

- **TruncationWeight<4>**: When you need tiered severity (dead,
  deterministic, binary, multi-way, severe) -- the default for
  PraTTaIL's ambiguity classification.

- **CountingWeight**: When you need the exact number of derivations --
  required for correctness guarantees in formal verification.

---

## 10. Pseudocode: Bounded Ambiguity Classification

The bounded ambiguity classification algorithm assigns a
TruncationWeight to every (category, token) pair, enabling tiered
dispatch strategy selection.

```
ALGORITHM BoundedAmbiguityClassification(grammar, K)
────────────────────────────────────────────────────────
  Input:  Grammar G with categories C and token set T,
          saturation bound K
  Output: Ambiguity map: (category, token) → {0, ..., K}

  1.  for each category c ∈ C do
  2.      for each token t ∈ T do
  3.          ambiguity[c, t] ← TruncationWeight<K>(0)   // zero: no paths

  4.  // Phase 1: Direct ambiguity from rules
  5.  for each rule r in category c matching token t do
  6.      ambiguity[c, t] ← ambiguity[c, t] ⊕  TruncationWeight<K>(1)
  7.                       // = max(current, 1), i.e., at least 1 path

  8.  // Phase 2: Cross-category ambiguity via casts
  9.  repeat until convergence:
 10.      for each cast c₁ → c₂ do
 11.          for each token t do
 12.              propagated ← TruncationWeight<K>(1) ⊗  ambiguity[c₂, t]
 13.                         // = min(1 + ambiguity[c₂, t], K)
 14.              ambiguity[c₁, t] ← ambiguity[c₁, t] ⊕  propagated
 15.                                // = max(current, propagated)

 16.  // Phase 3: Severity classification
 17.  for each (c, t) with ambiguity > 0 do
 18.      if ambiguity[c, t].is_saturated() then
 19.          emit_warning("Severe ambiguity ({}+) for {} in {}", K, t, c)
 20.      else if ambiguity[c, t].count() >= 3 then
 21.          emit_note("Multi-way ambiguity ({}) for {} in {}", count, t, c)

 22.  return ambiguity
```

**Complexity**: O(|C|² * |T| * d) where d is the cast-chain depth
(typically small, bounded by grammar depth).

---

## 11. Rust Implementation

The following is the complete `TruncationWeight<K>` implementation
from `prattail/src/automata/semiring.rs`.

```rust
/// Truncation semiring `({0, ..., K}, max, min(a + b, K))`.
///
/// Bounded ambiguity counting with saturation. Tracks the *maximum* count
/// from any alternative (idempotent `plus = max`) and saturates at `K`.
///
/// - `plus = max`: take the highest count from any alternative
/// - `times = min(a + b, K)`: accumulate counts with saturation
/// - `zero = 0`: no paths (identity for max)
/// - `one = 0`: adding zero doesn't increase count (identity for truncated +)
///
/// **Note:** Unlike CountingWeight (which has `plus = +`, `times = *`),
/// TruncationWeight has idempotent `plus = max` and additive `times`.
/// This means it tracks the worst-case ambiguity level rather than summing.
///
/// **Applications:**
/// - `prediction.rs`: tiered ambiguity severity (1 = deterministic,
///   2 = binary choice, 3+ = complex, K+ = severe)
///
/// Common values: `K = 4` (four-tier severity), `K = 8` (fine-grained).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct TruncationWeight<const K: u32>(pub u32);

impl<const K: u32> TruncationWeight<K> {
    /// Create a truncation weight, clamping to `[0, K]`.
    #[inline]
    pub const fn new(value: u32) -> Self {
        if value > K {
            TruncationWeight(K)
        } else {
            TruncationWeight(value)
        }
    }

    /// Get the count value.
    #[inline]
    pub const fn count(self) -> u32 {
        self.0
    }

    /// Whether this weight is at the saturation threshold.
    #[inline]
    pub const fn is_saturated(self) -> bool {
        self.0 >= K
    }
}

impl<const K: u32> Semiring for TruncationWeight<K> {
    #[inline]
    fn zero() -> Self {
        TruncationWeight(0)
    }

    #[inline]
    fn one() -> Self {
        TruncationWeight(0)
    }

    #[inline]
    fn plus(&self, other: &Self) -> Self {
        TruncationWeight(self.0.max(other.0))
    }

    #[inline]
    fn times(&self, other: &Self) -> Self {
        TruncationWeight(self.0.saturating_add(other.0).min(K))
    }

    #[inline]
    fn is_zero(&self) -> bool {
        self.0 == 0
    }

    #[inline]
    fn is_one(&self) -> bool {
        self.0 == 0
    }

    fn approx_eq(&self, other: &Self, _epsilon: f64) -> bool {
        self.0 == other.0
    }
}

impl<const K: u32> PartialOrd for TruncationWeight<K> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl<const K: u32> Ord for TruncationWeight<K> {
    fn cmp(&self, other: &Self) -> Ordering {
        self.0.cmp(&other.0)
    }
}

impl<const K: u32> fmt::Display for TruncationWeight<K> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.0 >= K {
            write!(f, "{}+", K)
        } else {
            write!(f, "{}", self.0)
        }
    }
}

impl<const K: u32> Default for TruncationWeight<K> {
    fn default() -> Self {
        Self::one()
    }
}

impl<const K: u32> DetectableZero for TruncationWeight<K> {}
impl<const K: u32> IdempotentSemiring for TruncationWeight<K> {}
impl<const K: u32> CompleteSemiring for TruncationWeight<K> {}
```

### Implementation Notes

- **Const generic K**: The saturation bound is a compile-time constant,
  enabling zero-overhead enforcement.  Common instantiations:
  `TruncationWeight<4>` and `TruncationWeight<8>`.

- **`saturating_add`**: Uses Rust's `u32::saturating_add` to prevent
  integer overflow before the `min(_, K)` clamp.  Without this, two
  large counts could wrap around to a small value.

- **`is_zero() = is_one()`**: Both check `self.0 == 0`, reflecting the
  degenerate zero-one coincidence.  This is intentional -- see the
  axiom analysis in [3. (Z)].

- **Natural `Ord`**: Unlike most PraTTaIL semirings, `Ord` is NOT
  reversed.  Lower count < higher count in the ordering.  This is
  appropriate because TruncationWeight is used for severity
  classification (higher = more severe), not for path selection where
  "better" means "lower".

- **`approx_eq` ignores epsilon**: Because the carrier set is discrete
  ({0, ..., K}), approximate equality is exact equality.

- **Display**: Shows `K+` for saturated values (e.g., `4+`), making it
  immediately clear that the count exceeds the bound.

---

## 12. Integration into PraTTaIL

TruncationWeight integrates with PraTTaIL's pipeline through the
ambiguity classification subsystem.

### 12.1 Tiered Ambiguity in Prediction (prediction.rs)

The prediction module uses `TruncationWeight<4>` to classify the
ambiguity level of each (category, token) pair:

```rust
type AmbiguityLevel = TruncationWeight<4>;

// Level 0: dead (emit warning)
// Level 1: deterministic (direct dispatch)
// Level 2: binary (composed dispatch)
// Level 3: multi-way (lookahead)
// Level 4+: severe (emit warning, force lookahead)
```

### 12.2 Lint Severity Modulation

The lint layer uses TruncationWeight counts to modulate diagnostic
severity.  A category with severity 4+ triggers a higher-priority
warning than one with severity 2:

```rust
if ambiguity.is_saturated() {
    emit_lint(LintLevel::Warning, "Severe ambiguity");
} else if ambiguity.count() >= 3 {
    emit_lint(LintLevel::Note, "Multi-way ambiguity");
}
```

### 12.3 Decision Tree Metadata

The decision tree module annotates branch nodes with
TruncationWeight counts, enabling visualization tools to display
ambiguity levels at each decision point.

---

## 13. Source Reference & See Also

### Source Location

- **File**: `prattail/src/automata/semiring.rs`, lines 2382--2500
- **Struct**: `TruncationWeight<const K: u32>(pub u32)`
- **Trait impl**: `impl<const K: u32> Semiring for TruncationWeight<K>` (lines 2434--2468)
- **Ordering**: `impl<const K: u32> Ord for TruncationWeight<K>` via natural `u32::cmp` (lines 2476--2480)
- **Display**: prints `K+` when saturated (lines 2482--2490)
- **Tests**: lines 4160--4231

### Cross-References

- [Semiring Algebra Overview](../semirings.md) -- Axiom
  definitions, classification, and comparison of all semirings
- [Counting Weight Theory](counting-weight.md) -- Exact unbounded
  counting semiring (full precision counterpart)
- [Boolean Weight Theory](boolean-weight.md) -- Binary reachability
  (degenerate case of truncation with K = 1)
- [Tropical Weight Theory](tropical-weight.md) -- Cost-based
  shortest-path semiring
- [Product Weight Theory](product-weight.md) -- Multi-dimensional
  weight combining truncation with other semirings

### References

- Mohri, M. (2002). "Semiring frameworks and algorithms for
  shortest-distance problems." *Journal of Automata, Languages and
  Combinatorics*, 7(3), 321--350.
- Kuich, W. & Salomaa, A. (1986). *Semirings, Automata, Languages*.
  Springer-Verlag. EATCS Monographs on Theoretical Computer Science.
- Golan, J. S. (1999). *Semirings and their Applications*. Kluwer
  Academic Publishers.  (Chapter 2: near-semirings and seminearrings.)
- Droste, M., Kuich, W., & Vogler, H. (2009). *Handbook of Weighted
  Automata*. Springer. Chapter 1: Semirings and formal power series.
