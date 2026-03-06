# Counting Semiring: CountingWeight

## 1. Intuition & Motivation

The counting semiring answers the question: *how many distinct
derivations exist?* -- without enumerating them.

In a weighted parser, a token that admits multiple parse rules is
*ambiguous*. Detecting ambiguity at compile time is critical for
generating efficient dispatch code: unambiguous tokens get direct
dispatch (zero overhead), while ambiguous tokens require either
composed-dispatch resolution or save/restore backtracking.

The key insight is that **the count of derivations alone suffices**
for ambiguity detection. We do not need to enumerate or rank the
derivations -- we only need to know whether the count exceeds 1.
The counting semiring provides exactly this information:

```
count = 1    →   unambiguous (direct dispatch)
count > 1    →   ambiguous (needs resolution strategy)
count = 0    →   dead rule (emit compile-time warning)
```

The counting semiring composes naturally with the tropical semiring
via `ProductWeight<TropicalWeight, CountingWeight>`, yielding a pair
`(best_weight, derivation_count)` that simultaneously identifies the
best parse *and* flags whether it was unique.

---

## 2. Formal Definition

The counting semiring is the algebraic structure

```
C  =  ( N,  +,  ×,  0,  1 )
```

where:

| Component                   | Symbol | Concrete value     | Meaning                                 |
|-----------------------------|--------|--------------------|-----------------------------------------|
| Carrier set                 | K      | N = {0, 1, 2, ...} | Natural numbers (non-negative integers) |
| Addition (⊕)                | +      | a + b (saturating) | Sum parallel path counts                |
| Multiplication (⊗)          | ×      | a × b (saturating) | Multiply sequential segment counts      |
| Additive identity (0̄)       | 0      | `0_u64`            | No derivations (dead rule)              |
| Multiplicative identity (1̄) | 1      | `1_u64`            | Exactly one derivation                  |

This is the standard natural-number semiring from abstract algebra,
restricted to `u64` with saturating arithmetic for overflow safety.

---

## 3. Semiring Axiom Verification

We verify all eight semiring axioms. Let a = 2, b = 3, c = 5.

### (A1) Associativity of ⊕

```
(a ⊕  b) ⊕  c  =  (2 + 3) + 5  =  5 + 5  =  10
a ⊕  (b ⊕  c)  =  2 + (3 + 5)  =  2 + 8  =  10   ✓
```

Natural number addition is associative. *Parsing interpretation:* the
total derivation count at a dispatch point does not depend on the order in
which the parser discovers competing rules.

### (A2) Commutativity of ⊕

```
a ⊕  b  =  2 + 3  =  5
b ⊕  a  =  3 + 2  =  5   ✓
```

Natural number addition is commutative. *Parsing interpretation:*
rule ordering in the grammar file does not affect the ambiguity count.

### (A3) ⊕  Identity

```
0̄ ⊕  a  =  0 + 2  =  2  =  a   ✓
a ⊕  0̄  =  2 + 0  =  2  =  a   ✓
```

Zero is the additive identity: a path count plus zero dead-rule
paths equals the original count. *Parsing interpretation:* an unreachable
alternative contributes nothing to the total derivation count.

### (M1) Associativity of ⊗

```
(a ⊗  b) ⊗  c  =  (2 × 3) × 5  =  6 × 5  =  30
a ⊗  (b ⊗  c)  =  2 × (3 × 5)  =  2 × 15  =  30   ✓
```

Natural number multiplication is associative. *Parsing interpretation:*
grouping a three-segment parse as `(A·B)·C` or `A·(B·C)` produces the same
combinatorial derivation count.

### (M2) ⊗  Identity

```
1̄ ⊗  a  =  1 × 2  =  2  =  a   ✓
a ⊗  1̄  =  2 × 1  =  2  =  a   ✓
```

One is the multiplicative identity: one derivation of a prefix
combined with a known count of suffixes yields that same count. *Parsing
interpretation:* a deterministic prefix (exactly one derivation) does not
multiply the suffix count — it passes through unchanged.

### (D1) Left Distributivity

```
a ⊗  (b ⊕  c)  =  2 × (3 + 5)  =  2 × 8  =  16
(a ⊗  b) ⊕  (a ⊗  c)  =  (2 × 3) + (2 × 5)  =  6 + 10  =  16   ✓
```

Standard distributivity of multiplication over addition. *Parsing
interpretation:* factoring a shared prefix preserves the total derivation
count: 2 prefix-ways × (3 + 5) suffix-ways = 6 + 10 = 16 total.

### (D2) Right Distributivity

```
(a ⊕  b) ⊗  c  =  (2 + 3) × 5  =  5 × 5  =  25
(a ⊗  c) ⊕  (b ⊗  c)  =  (2 × 5) + (3 × 5)  =  10 + 15  =  25   ✓
```

Symmetric to (D1). *Parsing interpretation:* shared suffixes can also be
factored without changing the total count.

### (Z) Zero Annihilation

```
0̄ ⊗  a  =  0 × 2  =  0  =  0̄   ✓
a ⊗  0̄  =  2 × 0  =  0  =  0̄   ✓
```

If any segment along a derivation path is impossible (zero
derivations), the entire path has zero derivations. *Parsing interpretation:*
a dead cross-category cast (zero derivations) kills all paths through it —
no finite count of suffix derivations can rescue an impossible prefix.

All eight axioms are satisfied. C is a valid semiring.

> For the parsing-specific interpretation of these axioms, see
> [§4 Why Each Axiom Matters for Parsing](../semirings.md#4-why-each-axiom-matters-for-parsing).

---

## 4. Key Properties

### 4.1 Commutativity

**Claim**: The counting semiring is commutative (⊗  is commutative).

**Proof**: For all a, b in N:

```
a ⊗  b  =  a × b  =  b × a  =  b ⊗  a
```

Natural number multiplication is commutative.   ∎

### 4.2 Non-Idempotency

**Claim**: The counting semiring is NOT idempotent.

**Proof by counterexample**: Let a = 3.

```
a ⊕  a  =  3 + 3  =  6  ≠  3  =  a
```

Therefore there exists a ∈ N such that a ⊕  a ≠ a, so the
semiring is not idempotent.   ∎

Non-idempotency is the fundamental distinction between the counting
and tropical semirings. In the counting semiring, merging a path
with itself *doubles* the count -- correctly reflecting that two
copies of a derivation contribute two derivations, not one.

This property makes CountingWeight unsuitable for Viterbi-style
best-path extraction (which requires idempotency) but ideal for
*counting* applications: ambiguity detection, confidence scoring,
and diagnostic reporting.

### 4.3 Zero Divisor Freedom

**Claim**: CountingWeight has no zero divisors: if a ⊗  b = 0̄, then
a = 0̄ or b = 0̄.

**Proof**: If a × b = 0 in N, then a = 0 or b = 0 (standard
property of natural number multiplication).   ∎

This means a zero derivation count always traces back to at least one
impossible segment -- there are no "phantom cancellations."

---

## 5. Parse-Tree Counting Semantics

The counting semiring tracks derivation counts through the standard
WFST interpretation:

### Parallel Alternatives (⊕  = addition)

When a token can be parsed by multiple rules in parallel, the total
derivation count is the *sum* of each rule's count:

```
                      ┌─── Rule A: 2 derivations ───┐
    Token "x" ────────┤                              ├────▶  2 + 3 = 5 total
                      └─── Rule B: 3 derivations ───┘
```

### Sequential Segments (⊗  = multiplication)

When a derivation consists of two sequential segments, the total
count is the *product* of each segment's count (combinatorial
explosion):

```
    ┌── Prefix: 3 ways ──┐     ┌── Suffix: 4 ways ──┐
    │                    │     │                    │     3 × 4 = 12 total
    └────────────────────┘     └────────────────────┘
```

### Forward Pass

A forward pass through the WFST (or equivalently, the composed
dispatch automaton) accumulates counts:

```
    q₀ ─── 1 ───▶ q₁ ─── 1 ───▶ q₂
     │                           ▲
     └──────── 1 ────────────────┘
                                        total at q₂: 1 + (1 × 1) = 2
```

The final count at an accept state equals the total number of
distinct derivation paths from start to accept.

---

## 6. Ambiguity Detection

### Worked Example

Consider a PraTTaIL grammar with category `Proc` that has three rules
whose FIRST sets overlap on certain tokens:

```
    Rule Send:    Proc → Name "!" "(" Proc ")"
    Rule Lookup:  Proc → Name "!" "(" "*" Name ")"
    Rule Invoke:  Proc → Name "(" Proc ")"
```

All three rules begin with the token `Name`. The composed dispatch
table for `(Proc, Name)` looks like:

```
    ┌────────────────────────────────────────────────────┐
    │       Ambiguity Detection for Token "Name"         │
    │              (Category: Proc)                      │
    ├────────────────────────────────────────────────────┤
    │                                                    │
    │   q₀ ──── Name ────▶ q₁ (Send)      count: 1       │
    │    │                                               │
    │    ├──── Name ────▶ q₂ (Lookup)     count: 1       │
    │    │                                               │
    │    └──── Name ────▶ q₃ (Invoke)     count: 1       │
    │                                                    │
    │   Total: 1 ⊕  1 ⊕  1 = 3                           │
    └────────────────────────────────────────────────────┘
```

### Per-Token Derivation Count Table

| Token      | Proc rules applicable | Count | Status      |
|------------|-----------------------|-------|-------------|
| Name       | Send, Lookup, Invoke  | 3     | Ambiguous   |
| LParen     | (none directly)       | 0     | Dead        |
| Star       | (none directly)       | 0     | Dead        |
| Bang       | (none directly)       | 0     | Dead        |
| Integer    | NumLit                | 1     | Unambiguous |
| StringLit  | StrLit                | 1     | Unambiguous |
| True/False | BoolLit               | 1     | Unambiguous |

When `count > 1`, the pipeline emits a compile-time ambiguity
warning and uses the composed dispatch table (tropical weights)
to resolve the ambiguity deterministically. When `count = 0`,
the token is not in the category's FIRST set and can be flagged
as a dead rule for that token.

### Ambiguity Detection Pseudocode

The following pseudocode describes how CountingWeight drives ambiguity
detection inside `compute_composed_dispatch()`:

```
FUNCTION detect_ambiguity(composed_table, categories):
    FOR (category, token) IN composed_table.keys():
        entries := composed_table[(category, token)]
        count := CountingWeight::zero()        // 0 derivations

        FOR entry IN entries:
            count := count ⊕  CountingWeight::one()     // count += 1

        MATCH count.count():
            0 => emit_dead_rule_warning(category, token)
            1 => // unambiguous — direct dispatch, no action needed
            n => emit_ambiguity_warning(category, token, n)
                 // resolve via tropical weights:
                 winner := entries.min_by(|e| e.tropical_weight)
                 emit_resolution_note(winner)
```

### Code Path

In `compute_composed_dispatch()` (prediction.rs), the counting
semiring is used implicitly: the number of `ComposedEntry` values
per `(category, token)` key equals the derivation count. The
pipeline logs warnings when this count exceeds 1:

```
    warning: ambiguous dispatch for (Proc, Name): 3 alternatives
```

---

## 7. Relationship to BooleanWeight

The boolean semiring `({false, true}, ∨, ∧, false, true)` is the
*image* of the counting semiring under the collapse homomorphism:

```
    φ : C → B
    φ(n) = (n > 0)
```

### Homomorphism Verification

A function φ between semirings is a homomorphism if it preserves
both operations and both identities:

**(H1) Preserves ⊕:**

```
φ(a ⊕_C b)  =  φ(a + b)  =  (a + b > 0)

For a, b ∈ N:
  - If a = 0 and b = 0: φ(0) = false, φ(a) ∨ φ(b) = false ∨ false = false   ✓
  - If a > 0 or b > 0:  φ(a + b) = true, φ(a) ∨ φ(b) = true                 ✓
    (since a + b > 0 iff a > 0 or b > 0)

Therefore: φ(a ⊕_C b) = φ(a) ⊕_B φ(b)   ✓
```

**(H2) Preserves ⊗:**

```
φ(a ⊗_C b)  =  φ(a × b)  =  (a × b > 0)

For a, b ∈ N:
  - If a = 0 or b = 0:  φ(0) = false, φ(a) ∧ φ(b) = false                   ✓
  - If a > 0 and b > 0: φ(a × b) = true, φ(a) ∧ φ(b) = true ∧ true = true   ✓
    (since a × b > 0 iff a > 0 and b > 0, given a, b ∈ N)

Therefore: φ(a ⊗_C b) = φ(a) ⊗_B φ(b)   ✓
```

**(H3) Preserves identities:**

```
φ(0̄_C) = φ(0) = false = 0̄_B   ✓
φ(1̄_C) = φ(1) = true  = 1̄_B   ✓
```

Therefore φ is a surjective semiring homomorphism from C to B.   ∎

### Practical Implication

BooleanWeight answers "is this rule reachable at all?" while
CountingWeight answers "how many ways can it be reached?" The
boolean answer is strictly less informative: it tells you whether
ambiguity exists but not its degree. In PraTTaIL:

- **CountingWeight** is used in `compute_composed_dispatch()` for
  ambiguity *quantification* (how many alternatives?)
- **BooleanWeight** is used for dead-rule *detection* (any
  alternatives at all?)

The homomorphism guarantees: if CountingWeight says 0 derivations,
BooleanWeight agrees the rule is dead; if CountingWeight says n > 0,
BooleanWeight agrees the rule is reachable.

---

## 8. Saturating Arithmetic

The implementation uses `saturating_add` and `saturating_mul` rather
than wrapping or panicking arithmetic:

```rust
fn plus(&self, other: &Self) -> Self {
    CountingWeight(self.0.saturating_add(other.0))
}

fn times(&self, other: &Self) -> Self {
    CountingWeight(self.0.saturating_mul(other.0))
}
```

### Rationale

Pathological grammars can produce exponentially many derivations.
Consider a grammar with n binary-ambiguous rules chained
sequentially:

```
    derivation_count  =  2ⁿ
```

For n = 64, this exceeds `u64::MAX ≈ 1.8 × 10¹⁹`. Without
saturation, the count would wrap to a small number, potentially
reporting an ambiguous rule as unambiguous (false negative).

With saturation:

```
    u64::MAX + k  =  u64::MAX        (for any k > 0)
    u64::MAX × k  =  u64::MAX        (for any k > 1)
```

The count saturates at `u64::MAX`, preserving the invariant
`count > 1 ⟹ ambiguous`. The exact count is lost, but the
ambiguity signal is preserved -- and `u64::MAX ≈ 1.8 × 10¹⁹`
is more than sufficient for any realistic grammar.

### Axiom Preservation Under Saturation

Saturating arithmetic over N ∩ [0, u64::MAX] does not form a
true semiring (distributivity can fail at the boundary), but this
is acceptable because:

1. Saturation only triggers on pathological inputs (> 2⁶⁴ paths).
2. The only property we need at saturation is monotonicity:
   `count > 1` remains `count > 1` after further operations.
3. No PraTTaIL algorithm depends on exact counts at the u64::MAX
   boundary -- only on the `count > 1` ambiguity predicate.

---

## 9. Comparison Table

| Property            | CountingWeight     | TropicalWeight     | LogWeight           | BooleanWeight       |
|---------------------|--------------------|--------------------|---------------------|---------------------|
| Carrier set         | N                  | R⁺ ∪ {+∞}          | R⁺ ∪ {+∞}           | {false, true}       |
| ⊕  (addition)       | a + b              | min(a, b)          | −ln(e⁻ᵃ + e⁻ᵇ)      | a ∨ b               |
| ⊗  (multiplication) | a × b              | a + b              | a + b               | a ∧ b               |
| 0̄ (zero)            | 0                  | +∞                 | +∞                  | false               |
| 1̄ (one)             | 1                  | 0.0                | 0.0                 | true                |
| Commutative?        | Yes                | Yes                | Yes                 | Yes                 |
| Idempotent?         | No (3+3=6)         | Yes (min(a,a)=a)   | No (lse(a,a)≠a)     | Yes (a∨a=a)         |
| Semantics           | Derivation count   | Shortest path cost | Neg-log probability | Reachability        |
| PraTTaIL use        | Ambiguity warnings | Dispatch ordering  | Training & scoring  | Dead-rule detection |
| Feature gate        | Always on          | Always on          | `wfst-log`          | Always on           |
| Rust type           | `u64`              | `f64`              | `f64`               | `bool`              |

---

## 10. Rust Implementation

The following is the complete `CountingWeight` implementation from
`prattail/src/automata/semiring.rs`.

```rust
/// Counting semiring (N, +, x, 0, 1).
///
/// Counts the number of distinct paths/derivations through the automaton.
///
/// - plus = addition: sums path counts from parallel alternatives
/// - times = multiplication: multiplies segment counts along a path
/// - zero = 0: no paths (identity for addition)
/// - one = 1: one path (identity for multiplication)
///
/// Application: Compose with TropicalWeight via ProductWeight to get
/// (best_weight, derivation_count). Tokens with count > 1 are ambiguous.
///
/// Uses saturating arithmetic to avoid overflow on pathological grammars.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct CountingWeight(pub u64);

impl CountingWeight {
    /// Create a counting weight with the given path count.
    #[inline]
    pub const fn new(count: u64) -> Self {
        CountingWeight(count)
    }

    /// Get the path count.
    #[inline]
    pub const fn count(self) -> u64 {
        self.0
    }
}

impl Semiring for CountingWeight {
    #[inline]
    fn zero() -> Self {
        CountingWeight(0)           // no derivations
    }

    #[inline]
    fn one() -> Self {
        CountingWeight(1)           // exactly one derivation
    }

    #[inline]
    fn plus(&self, other: &Self) -> Self {
        CountingWeight(self.0.saturating_add(other.0))  // sum parallel paths
    }

    #[inline]
    fn times(&self, other: &Self) -> Self {
        CountingWeight(self.0.saturating_mul(other.0))  // product of segments
    }

    #[inline]
    fn is_zero(&self) -> bool {
        self.0 == 0                 // dead rule: zero derivations
    }

    #[inline]
    fn is_one(&self) -> bool {
        self.0 == 1                 // unique derivation
    }

    fn approx_eq(&self, other: &Self, _epsilon: f64) -> bool {
        self.0 == other.0           // exact comparison (integer)
    }
}

impl fmt::Display for CountingWeight {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.0)     // display the raw count
    }
}

impl Default for CountingWeight {
    fn default() -> Self {
        Self::one()                 // default = 1 (one derivation)
    }
}
```

### Implementation Notes

- **Derived traits**: `Debug`, `PartialEq`, `Eq`, `PartialOrd`, `Ord`,
  `Hash` are all derived automatically. Unlike `TropicalWeight` (which
  wraps `f64` and needs custom impls for NaN handling), `u64` has
  well-behaved derived implementations.

- **`approx_eq` ignores epsilon**: Since `CountingWeight` wraps an
  integer, there is no floating-point imprecision. The `epsilon`
  parameter (required by the `Semiring` trait) is ignored; exact
  equality is used.

- **`Default = one()`**: Consistent with `TropicalWeight` -- a newly
  created weight represents one derivation (the multiplicative
  identity), not zero derivations (the additive identity / dead rule).

---

## 11. Integration into PraTTaIL

### 11.1 Ambiguity Warnings via compute_composed_dispatch() (prediction.rs)

During pipeline codegen, `compute_composed_dispatch()` builds a table
mapping `(category, state_id)` to a vector of `ComposedEntry` values.
The length of this vector is the implicit derivation count:

```
    entries.len() = 1   →  unambiguous dispatch
    entries.len() > 1   →  ambiguous, needs weight-based resolution
    entries.len() = 0   →  token not in FIRST set
```

When ambiguity is detected, the pipeline uses tropical weights from
the composed entries to select a winner via
`resolve_dispatch_winners()`, and emits compile-time diagnostics:

```
    warning: ambiguous dispatch for (Proc, Name): 3 alternatives
             resolved to Send (weight 0.5)
```

### 11.2 Confidence Metrics via predict_with_confidence() (wfst.rs)

The `PredictionWfst::predict_with_confidence()` method annotates each
weighted action with a `CountingWeight` representing the total number
of alternatives for that token:

```rust
pub fn predict_with_confidence(
    &self,
    token_name: &str,
) -> Vec<(&WeightedAction, CountingWeight)> {
    let actions = self.predict(token_name);
    let count = CountingWeight::new(actions.len() as u64);
    actions.into_iter().map(|a| (a, count)).collect()
}
```

This enables downstream consumers to distinguish:

- `count = 1`: The prediction is unambiguous; dispatch directly.
- `count > 1`: Multiple rules compete; the tropical weight determines
  which is tried first, but save/restore may be needed.

The confidence metric is used in `ProductWeight<TropicalWeight,
CountingWeight>` compositions, where the pair `(best_weight, count)`
captures both *which* parse is best and *how confident* that
selection is.

### 11.3 Composition with ProductWeight

The standard composition `ProductWeight<TropicalWeight, CountingWeight>`
applies operations component-wise:

```
    ⊕: (min(w₁, w₂),  c₁ + c₂)     // best weight + total count
    ⊗: (w₁ + w₂,      c₁ × c₂)     // accumulated cost + combinatorial count
```

Example: two paths to parse `Name` in category `Proc`:

```
    Path 1:  (weight=0.5, count=1)     Send rule
    Path 2:  (weight=2.0, count=1)     Variable fallback

    ⊕  result: (min(0.5, 2.0), 1 + 1) = (0.5, 2)
```

The product tells us: best parse has weight 0.5, but there are 2
alternatives (ambiguous). If count were 1, we would know the best
parse is unique and can be dispatched without backtracking.

---

## 12. Source Reference & See Also

### Source Location

- **File**: `prattail/src/automata/semiring.rs`, lines 204--281
- **Struct**: `CountingWeight(pub u64)`
- **Trait impl**: `impl Semiring for CountingWeight` (lines 235--269)
- **Display**: `impl Display for CountingWeight` (lines 271--275)
- **Tests**: `test_counting_*` (lines 929--996)

### Cross-References

- [Semiring Algebra Overview](../semirings.md) --
  Axiom definitions and classification of all semirings
- [Tropical Weight Theory](tropical-weight.md) -- The tropical semiring
  for shortest-path dispatch ordering
- [BooleanWeight](../../../src/automata/semiring.rs) (lines 300--363) --
  The reachability semiring; target of the collapse homomorphism
  φ(n) = (n > 0)
- [ProductWeight](../../../src/automata/semiring.rs) (lines 496--620) --
  Component-wise product for composing TropicalWeight with
  CountingWeight
- [predict_with_confidence()](../../../src/wfst.rs) (line 169) --
  CountingWeight annotation of WFST predictions
- [compute_composed_dispatch()](../../../src/prediction.rs) (line 1454)
  -- Ambiguity detection via implicit path counting
- [Composed Dispatch Design](../../../docs/design/composed-dispatch.md)
  -- How ambiguity counts drive dispatch strategy selection
