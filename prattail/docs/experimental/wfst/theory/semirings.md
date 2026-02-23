# Semiring Algebra for Weighted Parsing

## 1. Motivation

A weighted parser assigns a numerical score to each parse alternative.
To combine scores meaningfully — whether selecting the single best parse or
summing over all parses — the arithmetic must satisfy algebraic laws that
preserve correctness under composition. The semiring abstraction captures
exactly those laws.

PraTTaIL uses two semirings:

- **TropicalWeight** (always available) — for shortest-path dispatch ordering
  and beam pruning. Lower weight means higher parse priority.
- **LogWeight** (feature `wfst-log`) — for probabilistic parsing, forward-backward
  scoring, N-best extraction, and weight training.

Both semirings share the same `Semiring` trait; swapping them changes
*what the parser optimises* without changing the algorithmic structure.

---

## 2. Semiring Axioms

A semiring **S = (K, ⊕, ⊗, 0̄, 1̄)** consists of:

- A carrier set **K** of weight values.
- An additive operation **⊕** (combines parallel paths).
- A multiplicative operation **⊗** (sequences path segments).
- An additive identity **0̄** (the unreachable / impossible weight).
- A multiplicative identity **1̄** (the zero-cost / probability-1 weight).

### 2.1 Required Properties

```
(A1)  (a ⊕ b) ⊕ c  =  a ⊕ (b ⊕ c)          [⊕ associative]
(A2)  a ⊕ b         =  b ⊕ a                   [⊕ commutative]
(A3)  0̄ ⊕ a         =  a ⊕ 0̄  =  a             [⊕ identity]
(M1)  (a ⊗ b) ⊗ c  =  a ⊗ (b ⊗ c)             [⊗ associative]
(M2)  1̄ ⊗ a         =  a ⊗ 1̄  =  a             [⊗ identity]
(D1)  a ⊗ (b ⊕ c)  =  (a ⊗ b) ⊕ (a ⊗ c)      [⊗ left-distributes over ⊕]
(D2)  (a ⊕ b) ⊗ c  =  (a ⊗ c) ⊕ (b ⊗ c)      [⊗ right-distributes over ⊕]
(Z)   0̄ ⊗ a         =  a ⊗ 0̄  =  0̄             [0̄ annihilates ⊗]
```

### 2.2 Additional Classifications

A semiring is **commutative** if:

```
(MC)  a ⊗ b  =  b ⊗ a
```

A semiring is **idempotent** if:

```
(I)   a ⊕ a  =  a
```

Idempotent semirings support *tropical-style* best-path extraction.
Non-idempotent semirings (like LogWeight) support *sum-over-all-paths*
computations like the partition function.

### 2.3 The Rust Trait

```rust
pub trait Semiring: Clone + Copy + fmt::Debug + PartialEq + Send + Sync + 'static {
    fn zero()  -> Self;                               // 0̄
    fn one()   -> Self;                               // 1̄
    fn plus(&self,  other: &Self) -> Self;            // ⊕
    fn times(&self, other: &Self) -> Self;            // ⊗
    fn is_zero(&self) -> bool;
    fn is_one(&self)  -> bool;
    fn approx_eq(&self, other: &Self, epsilon: f64) -> bool;
}
```

Seven methods — six algebraic, one numerical-tolerance check for convergence
tests in forward-backward and training.

---

## 3. TropicalWeight

### 3.1 Definition

The **tropical semiring** over ℝ⁺ ∪ {+∞}:

```
K   =  ℝ⁺ ∪ {+∞}
a ⊕ b  =  min(a, b)
a ⊗ b  =  a + b
0̄      =  +∞           (unreachable; identity for min)
1̄      =  0.0          (zero cost; identity for addition)
```

Properties:
- **Commutative**: min(a,b) = min(b,a); addition commutes.
- **Idempotent**: min(a,a) = a.

### 3.2 Priority Mapping

PraTTaIL's lexer assigns each token kind a `priority` value in `0..=10`.
Higher priority means the token should be matched before lower-priority ones.
TropicalWeight inverts this so that *lower weight = higher priority*:

```
weight = MAX_PRIORITY − priority
       = 10.0 − priority
```

| Priority | TropicalWeight | Meaning                    |
|:--------:|:--------------:|:---------------------------|
| 10       | 0.0            | Highest priority (fixed)   |
|  5       | 5.0            | Mid-range                  |
|  1       | 9.0            | Low priority (identifier)  |
|  0       | 10.0           | Lowest priority (fallback) |

The `from_priority` constructor implements this mapping:

```rust
pub fn from_priority(priority: u8) -> Self {
    TropicalWeight((10.0_f64) - priority as f64)
}
```

### 3.3 Zero-Annihilation

Because 0̄ = +∞ and ⊗ = addition:

```
+∞ + 5.0  =  +∞   (unreachable path stays unreachable)
```

This correctly models "if any segment is impossible, the whole path is
impossible."

### 3.4 Dispatch Weight Assignments

In PraTTaIL's WFST prediction layer, `compute_action_weight` maps each
`DispatchAction` variant to a TropicalWeight:

| DispatchAction variant               | Weight | Rationale                         |
|:-------------------------------------|:------:|:----------------------------------|
| `Direct`                             | 0.0    | Unambiguous, try immediately      |
| `Grouping`                           | 0.0    | Delimiter-driven, deterministic   |
| `CrossCategory { needs_backtrack: false }` | 0.0 | Deterministic cross-category   |
| `CrossCategory { needs_backtrack: true }`  | 0.5 | Prefer source path, allow fallback |
| `Cast`                               | 0.5    | Slightly penalised vs direct      |
| `Lookahead { order }`                | 1.0 + order | Needs extra tokens to decide  |
| `Variable`                           | 2.0    | Last-resort fallback              |

---

## 4. LogWeight

*Requires feature `wfst-log`.*

### 4.1 Definition

The **log semiring** over ℝ⁺ ∪ {+∞}, representing **negative log-probabilities**
(w = −ln p):

```
K   =  ℝ⁺ ∪ {+∞}
a ⊕ b  =  −ln(e⁻ᵃ + e⁻ᵇ)     (log-sum-exp)
a ⊗ b  =  a + b                (log-domain multiplication)
0̄      =  +∞                   (probability 0; identity for log-sum-exp)
1̄      =  0.0                  (probability 1; identity for addition)
```

Properties:
- **Commutative**: log-sum-exp is symmetric; addition commutes.
- **NOT idempotent**: a ⊕ a = −ln(2e⁻ᵃ) = a − ln 2 ≠ a (in general).

The non-idempotency is the key distinction: LogWeight sums *all* path
probabilities rather than selecting only the best.

### 4.2 Probability Correspondence

| Weight (w = −ln p) | Probability (p = e⁻ʷ) | Interpretation         |
|:------------------:|:---------------------:|:-----------------------|
| 0.0                | 1.0                   | Certain (1̄)            |
| 0.693 ≈ ln 2       | 0.5                   | Fifty-fifty            |
| 2.303 ≈ ln 10      | 0.1                   | Ten percent            |
| +∞                 | 0.0                   | Impossible (0̄)         |

Conversion helpers:

```rust
// Probability → weight
fn from_probability(p: f64) -> LogWeight { LogWeight(-p.ln()) }

// Weight → probability
fn to_probability(self) -> f64 { (-self.0).exp() }
```

### 4.3 Numerical Stability

The naive computation `−ln(e⁻ᵃ + e⁻ᵇ)` overflows when a or b is large.
The stable form factors out the smaller value:

```
logsumexp(a, b) = min(a,b) − ln(1 + e^(−|a−b|))
```

When |a − b| > 20, the correction term e^(−|a−b|) < e⁻²⁰ ≈ 2×10⁻⁹.
The implementation uses a fast path that drops the correction entirely:

```rust
fn log_sum_exp(a: f64, b: f64) -> f64 {
    let min_val = a.min(b);
    let diff = (a - b).abs();
    if diff > 20.0 {
        min_val                               // correction < 2e-9
    } else {
        min_val - (1.0 + (-diff).exp()).ln()
    }
}
```

The threshold 20.0 gives an absolute error below 2×10⁻⁹, well within
f64's 15-digit precision budget.

---

## 5. Semiring Hierarchy

The two semirings relate to broader families as follows:

```
              Semiring
              ╔═══════════════════════════════════╗
              ║                                   ║
        Commutative Semiring                      ║
        ╔═══════════════════════════╗             ║
        ║                          ║             ║
  Commutative + Idempotent    Commutative         ║
  ╔═══════════════════════╗   ╔═══════════════╗  ║
  ║                       ║   ║               ║  ║
  ║  TropicalWeight  ◄────╫───╫── LogWeight   ║  ║
  ║  (min, +, ∞, 0)       ║   ║  (lse, +, ∞, 0) ║
  ╚═══════════════════════╝   ╚═══════════════╝  ║
        ║                          ║             ║
        ╚══════════════════════════╝             ║
                      ║                          ║
                      ╚══════════════════════════╝
```

Both semirings sit in the commutative family. TropicalWeight additionally
satisfies idempotency (a ⊕ a = a), which enables best-path dynamic
programming without double-counting.

---

## 6. Worked Example: Same Graph, Two Semirings

Consider a graph with four nodes **A, B, C, D** and the following arcs:

```
  A ──(1.0)──► B ──(3.0)──► D
  │                          ▲
  └──(2.0)──► C ──(0.5)──────┘
```

Path weights:
- A → B → D: segments 1.0 and 3.0
- A → C → D: segments 2.0 and 0.5

### 6.1 TropicalWeight (shortest path)

Segment weights combined with ⊗ = addition:

```
w(A→B→D) = 1.0 + 3.0 = 4.0
w(A→C→D) = 2.0 + 0.5 = 2.5
```

Parallel alternatives combined with ⊕ = min:

```
w(A→D)  = min(4.0, 2.5) = 2.5
```

**Best path: A → C → D, total weight 2.5.**

### 6.2 LogWeight (sum over all paths)

Interpret weights as negative log-probabilities: w = −ln p.

```
p(A→B) = e⁻¹·⁰ ≈ 0.3679    p(B→D) = e⁻³·⁰ ≈ 0.0498
p(A→C) = e⁻²·⁰ ≈ 0.1353    p(C→D) = e⁻⁰·⁵ ≈ 0.6065

p(A→B→D) = 0.3679 × 0.0498 ≈ 0.01832
p(A→C→D) = 0.1353 × 0.6065 ≈ 0.08206
```

Log-weight ⊗ = addition (multiplies probabilities in log-domain):

```
w(A→B→D) = 1.0 + 3.0 = 4.0   (log-domain: same as tropical times)
w(A→C→D) = 2.0 + 0.5 = 2.5
```

Log-weight ⊕ = log-sum-exp (sums probabilities):

```
total probability  = 0.01832 + 0.08206 ≈ 0.10038
w(A→D) = −ln(0.10038) ≈ 2.299
```

Or equivalently, via the stable formula:

```
w(A→D) = logsumexp(4.0, 2.5)
        = 2.5 − ln(1 + e^(−|4.0−2.5|))
        = 2.5 − ln(1 + e^(−1.5))
        ≈ 2.5 − ln(1.2231)
        ≈ 2.5 − 0.2014
        ≈ 2.299
```

**Sum weight: ≈ 2.299** (lower than 2.5 because both paths contribute
probability mass, making the combined path more likely than either alone).

### 6.3 Comparison Table

| Metric             | TropicalWeight | LogWeight    |
|:-------------------|:--------------:|:------------:|
| Best path          | A→C→D (2.5)    | N/A (sums all) |
| Total weight       | 2.5            | ≈ 2.299        |
| Idempotent?        | Yes            | No             |
| Use case           | Dispatch order | Probability    |

---

## 7. Test Coverage

The test suite in `automata/semiring.rs` contains **20 tests** in total:

**TropicalWeight (12 tests):**

| Test | Property verified |
|:-----|:-----------------|
| `test_tropical_zero_is_infinity` | 0̄ = +∞ |
| `test_tropical_one_is_zero_cost` | 1̄ = 0.0 |
| `test_tropical_plus_is_min` | ⊕ = min, commutative |
| `test_tropical_times_is_add` | ⊗ = addition |
| `test_tropical_zero_annihilates` | 0̄ ⊗ a = 0̄ |
| `test_tropical_one_is_identity` | 1̄ ⊗ a = a |
| `test_tropical_zero_is_plus_identity` | 0̄ ⊕ a = a |
| `test_tropical_plus_idempotent` | a ⊕ a = a |
| `test_tropical_from_priority` | Priority → weight inversion |
| `test_tropical_ordering` | Total order a < b < +∞ |
| `test_tropical_approx_eq` | Epsilon comparison |
| `test_tropical_hash_consistency` | Hash matches Eq |

**LogWeight (8 tests, feature `wfst-log`):**

| Test | Property verified |
|:-----|:-----------------|
| `test_log_weight_semiring_laws` | All six axioms |
| `test_log_weight_probability_roundtrip` | from_probability / to_probability inverse |
| `test_log_weight_non_idempotent` | a ⊕ a = a − ln 2 ≠ a |
| `test_log_weight_numerical_stability` | No NaN/Inf for large inputs |
| `test_log_sum_exp_large_diff` | Fast path when \|a−b\| > 20 |
| `test_log_weight_times_is_addition` | ⊗ = addition |
| `test_log_weight_ordering` | Total order preserved |
| `test_log_weight_display` | Display formatting |

---

## 8. Source Reference

| Symbol | Location |
|:-------|:---------|
| `Semiring` trait | `prattail/src/automata/semiring.rs` lines 36–51 |
| `TropicalWeight` struct | `prattail/src/automata/semiring.rs` lines 68–198 |
| `LogWeight` struct | `prattail/src/automata/semiring.rs` lines 226–392 |
| `TropicalWeight::from_priority` | `prattail/src/automata/semiring.rs` line 102 |
| `compute_action_weight` | `prattail/src/wfst.rs` lines 349–372 |

---

**See also:**
- [`weighted-automata.md`](weighted-automata.md) — how semirings label WFST transitions
- [`viterbi-and-forward-backward.md`](viterbi-and-forward-backward.md) — algorithms over semiring-weighted DAGs
