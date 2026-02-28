# Semiring Algebra for Weighted Parsing

## 1. Motivation

A weighted parser assigns a numerical score to each parse alternative.
To combine scores meaningfully — whether selecting the single best parse or
summing over all parses — the arithmetic must satisfy algebraic laws that
preserve correctness under composition. The semiring abstraction captures
exactly those laws.

PraTTaIL provides six concrete semiring types:

- **TropicalWeight** (always available) — for shortest-path dispatch ordering
  and beam pruning. Lower weight means higher parse priority.
- **CountingWeight** (always available) — for parse-tree counting and
  ambiguity detection at codegen time.
- **BooleanWeight** (always available) — for reachability analysis and
  dead-rule detection after WFST construction.
- **EditWeight** (always available) — for minimum-repair parsing and
  error recovery cost computation.
- **ProductWeight** (always available) — for multi-objective optimization,
  combining any two semirings componentwise with lexicographic ordering.
- **LogWeight** (feature `wfst-log`) — for probabilistic parsing, forward-backward
  scoring, N-best extraction, and weight training.

All six types implement the same `Semiring` trait; swapping them changes
*what the parser optimises* without changing the algorithmic structure.

For detailed theory on each semiring, see the per-semiring documents in
[`semirings/`](semirings/) (when available).

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

The **tropical semiring** over R+ union {+inf}:

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

Because 0̄ = +inf and ⊗ = addition:

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

The **log semiring** over R+ union {+inf}, representing **negative log-probabilities**
(w = -ln p):

```
K   =  ℝ⁺ ∪ {+∞}
a ⊕ b  =  −ln(e⁻ᵃ + e⁻ᵇ)     (log-sum-exp)
a ⊗ b  =  a + b                (log-domain multiplication)
0̄      =  +∞                   (probability 0; identity for log-sum-exp)
1̄      =  0.0                  (probability 1; identity for addition)
```

Properties:
- **Commutative**: log-sum-exp is symmetric; addition commutes.
- **NOT idempotent**: a ⊕ a = -ln(2e^-a) = a - ln 2 != a (in general).

The non-idempotency is the key distinction: LogWeight sums *all* path
probabilities rather than selecting only the best.

### 4.2 Probability Correspondence

| Weight (w = -ln p) | Probability (p = e^-w) | Interpretation         |
|:------------------:|:---------------------:|:-----------------------|
| 0.0                | 1.0                   | Certain (1̄)            |
| 0.693 ~ ln 2       | 0.5                   | Fifty-fifty            |
| 2.303 ~ ln 10      | 0.1                   | Ten percent            |
| +inf               | 0.0                   | Impossible (0̄)         |

Conversion helpers:

```rust
// Probability → weight
fn from_probability(p: f64) -> LogWeight { LogWeight(-p.ln()) }

// Weight → probability
fn to_probability(self) -> f64 { (-self.0).exp() }
```

### 4.3 Numerical Stability

The naive computation `-ln(e^-a + e^-b)` overflows when a or b is large.
The stable form factors out the smaller value:

```
logsumexp(a, b) = min(a,b) − ln(1 + e^(−|a−b|))
```

When |a - b| > 20, the correction term e^(-|a-b|) < e^-20 ~ 2x10^-9.
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

The threshold 20.0 gives an absolute error below 2x10^-9, well within
f64's 15-digit precision budget.

---

## 5. Semiring Hierarchy

The six semirings relate to broader families as follows:

```
              Semiring
              ╔═══════════════════════════════════════════════════════════════════╗
              ║                                                                   ║
        Commutative Semiring                                                      ║
        ╔══════════════════════════════════════════════════════════════════╗       ║
        ║                                                                 ║       ║
  Commutative + Idempotent              Commutative (not idempotent)      ║       ║
  ╔══════════════════════════════╗      ╔══════════════════════════╗      ║       ║
  ║                              ║      ║                          ║      ║       ║
  ║  TropicalWeight              ║      ║  LogWeight [wfst-log]    ║      ║       ║
  ║  (min, +, ∞, 0)             ║      ║  (lse, +, ∞, 0)         ║      ║       ║
  ║                              ║      ║                          ║      ║       ║
  ║  BooleanWeight               ║      ║  CountingWeight          ║      ║       ║
  ║  (∨, ∧, 0, 1)               ║      ║  (+, x, 0, 1)           ║      ║       ║
  ║                              ║      ║                          ║      ║       ║
  ║  EditWeight                  ║      ╚══════════════════════════╝      ║       ║
  ║  (min, +, ∞, 0)             ║                                        ║       ║
  ╚══════════════════════════════╝                                       ║       ║
        ║                                                                 ║       ║
        ╚═════════════════════════════════════════════════════════════════╝       ║
                      ║                                                           ║
                      ║  ProductWeight<S1, S2>                                    ║
                      ║  (inherits properties from S1 and S2)                     ║
                      ║                                                           ║
                      ╚═══════════════════════════════════════════════════════════╝
```

TropicalWeight, BooleanWeight, and EditWeight are commutative and idempotent,
enabling best-path dynamic programming without double-counting. CountingWeight
and LogWeight are commutative but not idempotent, supporting sum-over-all-paths
computations. ProductWeight inherits the properties of its component semirings.

---

## 6. Worked Example: Same Graph, Two Semirings

Consider a graph with four nodes **A, B, C, D** and the following arcs:

```
  A ──(1.0)──► B ──(3.0)──► D
  │                          ▲
  └──(2.0)──► C ──(0.5)──────┘
```

Path weights:
- A -> B -> D: segments 1.0 and 3.0
- A -> C -> D: segments 2.0 and 0.5

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

**Best path: A -> C -> D, total weight 2.5.**

### 6.2 LogWeight (sum over all paths)

Interpret weights as negative log-probabilities: w = -ln p.

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

**Sum weight: ~ 2.299** (lower than 2.5 because both paths contribute
probability mass, making the combined path more likely than either alone).

### 6.3 Comparison Table

| Metric             | TropicalWeight | LogWeight    |
|:-------------------|:--------------:|:------------:|
| Best path          | A->C->D (2.5)    | N/A (sums all) |
| Total weight       | 2.5            | ~ 2.299        |
| Idempotent?        | Yes            | No             |
| Use case           | Dispatch order | Probability    |

---

## 7. Test Coverage

The test suite in `automata/semiring.rs` contains **38 tests** in total:

**TropicalWeight (12 tests):**

| Test | Property verified |
|:-----|:-----------------|
| `test_tropical_zero_is_infinity` | 0̄ = +inf |
| `test_tropical_one_is_zero_cost` | 1̄ = 0.0 |
| `test_tropical_plus_is_min` | ⊕ = min, commutative |
| `test_tropical_times_is_add` | ⊗ = addition |
| `test_tropical_zero_annihilates` | 0̄ ⊗ a = 0̄ |
| `test_tropical_one_is_identity` | 1̄ ⊗ a = a |
| `test_tropical_zero_is_plus_identity` | 0̄ ⊕ a = a |
| `test_tropical_plus_idempotent` | a ⊕ a = a |
| `test_tropical_from_priority` | Priority -> weight inversion |
| `test_tropical_ordering` | Total order a < b < +inf |
| `test_tropical_approx_eq` | Epsilon comparison |
| `test_tropical_hash_consistency` | Hash matches Eq |

**CountingWeight, BooleanWeight, EditWeight, ProductWeight (26 tests):**

These semirings are always available and cover axiom verification,
identity/annihilation properties, idempotency (or lack thereof),
ordering, and composition. See `automata/semiring.rs` for the full
test listing.

**LogWeight (8 tests, feature `wfst-log`):**

| Test | Property verified |
|:-----|:-----------------|
| `test_log_weight_semiring_laws` | All six axioms |
| `test_log_weight_probability_roundtrip` | from_probability / to_probability inverse |
| `test_log_weight_non_idempotent` | a ⊕ a = a - ln 2 != a |
| `test_log_weight_numerical_stability` | No NaN/Inf for large inputs |
| `test_log_sum_exp_large_diff` | Fast path when \|a-b\| > 20 |
| `test_log_weight_times_is_addition` | ⊗ = addition |
| `test_log_weight_ordering` | Total order preserved |
| `test_log_weight_display` | Display formatting |

**Test counts:** default (no features): 644, `wfst-log`: 678.

---

## 8. Source Reference

| Symbol | Location |
|:-------|:---------|
| `Semiring` trait | `prattail/src/automata/semiring.rs` |
| `TropicalWeight` struct | `prattail/src/automata/semiring.rs` |
| `CountingWeight` struct | `prattail/src/automata/semiring.rs` |
| `BooleanWeight` struct | `prattail/src/automata/semiring.rs` |
| `EditWeight` struct | `prattail/src/automata/semiring.rs` |
| `ProductWeight` struct | `prattail/src/automata/semiring.rs` |
| `LogWeight` struct | `prattail/src/automata/semiring.rs` (feature `wfst-log`) |
| `TropicalWeight::from_priority` | `prattail/src/automata/semiring.rs` |
| `compute_action_weight` | `prattail/src/wfst.rs` |

---

**See also:**
- [`weighted-automata.md`](weighted-automata.md) — how semirings label WFST transitions
- [`viterbi-and-forward-backward.md`](viterbi-and-forward-backward.md) — algorithms over semiring-weighted DAGs

---

## 9. Semiring Catalog for Parser Generators

The following table provides a comprehensive reference of semirings relevant to
parser generator construction. Each row specifies the algebraic structure,
primary application domain, key properties, and current implementation status
within PraTTaIL.

| # | Semiring | Carrier Set K | ⊕ | ⊗ | 0̄ | 1̄ | Application | Properties | PraTTaIL Status |
|:-:|:---------|:--------------|:--|:--|:--|:--|:------------|:-----------|:----------------|
| 1 | **Tropical** | R+ union {+inf} | min | + | +inf | 0.0 | Shortest-path dispatch, beam pruning | commutative, idempotent | **Implemented** (`TropicalWeight`) |
| 2 | **Log** | R+ union {+inf} | -ln(e^-a+e^-b) | + | +inf | 0.0 | Probabilistic parsing, forward-backward, training | commutative, NOT idempotent | **Implemented** (`LogWeight`, feature `wfst-log`) |
| 3 | **Counting** | N | + | x | 0 | 1 | Parse-tree counting, ambiguity detection | commutative, NOT idempotent | **Implemented** (`CountingWeight`) |
| 4 | **Boolean** | {0, 1} | ∨ | ∧ | 0 | 1 | Reachability, dead-rule detection, emptiness | commutative, idempotent | **Implemented** (`BooleanWeight`) |
| 5 | **Edit Distance** | N union {+inf} | min | + | +inf | 0 | Minimum-repair parsing, error correction | commutative, idempotent | **Implemented** (`EditWeight`) |
| 6 | **Product** | S1 x S2 | (⊕1, ⊕2) | (⊗1, ⊗2) | (0̄1, 0̄2) | (1̄1, 1̄2) | Multi-objective optimization (weight + count, weight + distance) | inherits from components | **Implemented** (`ProductWeight`) |
| 7 | **Set/Forest** | 2^(Parse Trees) | union | lift(⊗) | {} | {epsilon} | All-parses enumeration, parse forest construction | commutative, idempotent | Not planned |
| 8 | **Max-Plus (Arctic)** | R union {-inf} | max | + | -inf | 0.0 | Maximum-reward parsing, longest path | commutative, idempotent | Not planned |

### 9.1 Practical Usefulness Ranking

Ranked by practical value for parser generator construction, from most to least
useful:

1. **Tropical** — The workhorse. Shortest-path semantics directly solve the
   dispatch ordering problem: given multiple parse alternatives for a token,
   select the one with lowest accumulated weight. The default in PraTTaIL;
   all grammars receive WFST-weighted dispatch.

2. **Log** — Essential for any system that trains weights from data. The
   non-idempotent ⊕ preserves probability mass across alternatives, enabling
   forward-backward, EM training, and N-best extraction. Implemented
   behind `wfst-log`.

3. **Counting** — Ambiguity detection at codegen time. If the count for a
   (state, token) pair exceeds 1, the grammar is ambiguous at that point.
   Used in `compute_composed_dispatch()` for ambiguity warnings.

4. **Boolean** — Reachability analysis. Answers "can this state be
   reached?" and "does this rule ever fire?" Used for dead-rule detection
   in the pipeline after WFST construction.

5. **Product** — Enables multi-objective decisions. Tropical x Counting gives
   (best_weight, num_alternatives) for disambiguation with confidence.
   Tropical x Edit gives (best_parse, repair_distance) for error-tolerant
   parsing. ProductWeight has lexicographic Ord (left first, then right).

6. **Edit Distance** — Bridges parsing and error correction. Used via
   `RepairAction::edit_cost()` in recovery.rs. Composing an edit
   transducer with the lexer/parser WFST yields closest-valid-parse with a
   computable distance metric. Natural integration point with `liblevenshtein`.

7. **Max-Plus (Arctic)** — The dual of Tropical. Useful when the objective is
   to *maximize* a reward rather than minimize a cost. Rarely needed in parser
   generators but occasionally arises in longest-match lexing or maximum-
   specificity rule selection.

8. **Set/Forest** — Complete parse enumeration. Powerful but expensive: the
   carrier set grows combinatorially. Practical only for small grammars or
   bounded enumeration during debugging.

**Justification:** The ranking reflects the frequency with which each semiring
addresses a concrete parser generator problem. Tropical and Log are daily-use
tools; Counting and Boolean are diagnostics that improve developer experience;
Product, Edit Distance, and Max-Plus are specialized extensions; Set/Forest is
a theoretical completeness tool.

---

## 10. Counting Semiring

### 10.1 Formal Definition

The **counting semiring** over the natural numbers:

```
S  =  (ℕ, +, x, 0, 1)

K   =  ℕ  =  {0, 1, 2, 3, ...}
a ⊕ b  =  a + b       (sum counts from parallel alternatives)
a ⊗ b  =  a x b       (multiply counts across sequential segments)
0̄      =  0            (no paths; identity for addition)
1̄      =  1            (one path; identity for multiplication)
```

### 10.2 Properties

- **Commutative**: a + b = b + a and a x b = b x a.
- **NOT idempotent**: a ⊕ a = a + a = 2a != a (for a != 0). This is correct:
  two distinct paths contributing the same sub-count should double the total.

### 10.3 Parse-Tree Counting Semantics

Each WFST arc carries a count weight equal to the number of distinct parse trees
that traverse that arc. When two paths merge at a state, their counts add (⊕ = +).
When a path traverses two arcs in sequence, their counts multiply (⊗ = x) because
each tree through the first arc can combine with each tree through the second.

The total weight at the accept state equals the total number of distinct parse
trees for the input, computed in a single forward pass over the lattice.

### 10.4 Ambiguity Detection at Codegen Time

PraTTaIL uses CountingWeight in `compute_composed_dispatch()` to detect
ambiguity at codegen time. Under the counting semiring, the weight at each
dispatch entry equals the number of distinct rules that could fire. If that
count exceeds 1, the grammar is ambiguous at that dispatch point, and the
codegen emits a warning:

```
                    Counting Semiring Dispatch Table
        ┌──────────────────────────────────────────────────┐
        │  State   Token      Count   Status               │
        │  ─────   ─────      ─────   ──────               │
        │    3     Ident        1     ok (unambiguous)      │
        │    5     LParen       1     ok (unambiguous)      │
        │    7     Ident        3     WARNING: 3-way ambig  │
        │    9     Integer      1     ok (unambiguous)      │
        └──────────────────────────────────────────────────┘
```

### 10.5 Worked Example: 3-Way Ambiguous Dispatch

Consider a grammar with category `Proc` containing three rules that can all
begin with an identifier token:

```
rule Send:    Proc ::= name "!" "(" Proc ")"
rule Lookup:  Proc ::= name
rule Invoke:  Proc ::= name "(" ProcList ")"
```

At state 7 (the prefix entry point for `Proc`), the lookahead token `Ident`
matches all three rules. Under the counting semiring:

```
Step 1: Each rule contributes count 1 to the (state 7, Ident) entry.

  count(Send)   = 1
  count(Lookup) = 1
  count(Invoke) = 1

Step 2: Parallel alternatives combined with ⊕ = +:

  total = 1 ⊕ 1 ⊕ 1 = 1 + 1 + 1 = 3

Step 3: count = 3 > 1  →  emit codegen warning:

  warning: grammar is 3-way ambiguous at (Proc, state 7, Ident)
           candidates: Send, Lookup, Invoke
           resolution: lookahead disambiguation or explicit priority
```

This warning fires at codegen time (not at parse time), giving the grammar
author immediate feedback about ambiguity without needing to construct a test
input that triggers it.

### 10.6 Relationship to Boolean

The counting semiring strictly generalizes the Boolean semiring. The collapse
function is:

```
collapse: ℕ → {0, 1}
collapse(n) = { 0  if n = 0
              { 1  if n > 0
```

This is a semiring homomorphism: collapse(a + b) = collapse(a) v collapse(b)
and collapse(a x b) = collapse(a) ^ collapse(b). Therefore, any reachability
query answerable by Boolean is also answerable by Counting — but Counting
additionally provides *how many* paths exist, not merely *whether* one does.

### 10.7 Comparison with Other Semirings

| Aspect | Counting | Tropical | Log |
|:-------|:---------|:---------|:----|
| Answers | "how many parses?" | "which parse is cheapest?" | "what is the total probability?" |
| ⊕ semantics | sum counts | select minimum | sum probabilities (log-domain) |
| Idempotent | No | Yes | No |
| Codegen use | ambiguity detection | dispatch ordering | weight training |
| Runtime cost | O(1) per operation | O(1) per operation | O(1) per operation (with exp/ln) |

---

## 11. Boolean Semiring

### 11.1 Formal Definition

The **Boolean semiring** over the two-element set:

```
S  =  ({0, 1}, ∨, ∧, 0, 1)

K   =  {0, 1}  =  {false, true}
a ⊕ b  =  a ∨ b       (logical OR: reachable if either path is reachable)
a ⊗ b  =  a ∧ b       (logical AND: reachable only if both segments are)
0̄      =  0 (false)    (unreachable; identity for OR)
1̄      =  1 (true)     (reachable; identity for AND)
```

### 11.2 Properties

- **Commutative**: a v b = b v a and a ^ b = b ^ a.
- **Idempotent**: a v a = a. Once a state is known reachable, additional paths
  contribute no new information.

### 11.3 Reachability Semantics

Under the Boolean semiring, each WFST arc carries weight 1 (reachable) or 0
(unreachable). The forward pass computes, for each state, whether *any* path
from the start state reaches it. The backward pass computes whether *any* path
from it reaches an accept state. A state reachable in both directions is *live*;
all others are *dead*.

```
             Boolean Reachability Analysis
  ┌─────────────────────────────────────────────────────┐
  │                                                     │
  │  start ──(1)──► s1 ──(1)──► s2 ──(1)──► accept     │
  │    │                         ▲                      │
  │    └──(1)──► s3 ──(0)───────┘                       │
  │              │                                      │
  │              └──(1)──► s4  (dead: no path to accept) │
  │                                                     │
  │  Forward:   start=1, s1=1, s2=1, s3=1, s4=1        │
  │  Backward:  accept=1, s2=1, s1=1, start=1          │
  │             s3: 0∧1 ∨ 1∧? → depends on s4          │
  │             s4: no outgoing to accept → 0           │
  │             s3: only path to s2 has weight 0 → 0    │
  │                                                     │
  │  Live states:  {start, s1, s2, accept}              │
  │  Dead states:  {s3, s4}  →  eliminate               │
  │                                                     │
  └─────────────────────────────────────────────────────┘
```

### 11.4 Applications in PraTTaIL

**Dead-rule detection.** After constructing the prediction WFST, BooleanWeight
reachability analysis identifies rules that can never fire. The pipeline
performs this check and reports dead rules (e.g., FloatToStr, FloatToBool,
StrToBool, IntId, FloatId, BoolId, StrId, POutput) as diagnostics.

**Grammar emptiness test.** A grammar category `Cat` is *empty* (derives no
terminal strings) if and only if the accept state for `Cat` has Boolean forward
weight 0. This is a single semiring evaluation — no iterative fixed-point
computation is needed beyond the standard forward pass.

**Unreachable-state elimination.** States that are forward-reachable but not
backward-reachable (or vice versa) waste space in the generated transition
tables. Boolean analysis identifies these for removal during WFST minimization.

### 11.5 Contrast with Counting

| Aspect | Boolean | Counting |
|:-------|:--------|:---------|
| Question answered | "is it reachable?" | "how many ways?" |
| ⊕ semantics | a v b | a + b |
| Idempotent | Yes: 1 v 1 = 1 | No: 1 + 1 = 2 |
| Information content | 1 bit per state | Unbounded integer per state |
| Computational cost | Bitwise operations | Integer arithmetic |
| Use case | elimination of dead code | ambiguity quantification |

Boolean is the quotient of Counting under the collapse homomorphism
(Section 10.6). When the question is binary — reachable or not — Boolean is
strictly cheaper. When the multiplicity matters — how ambiguous — Counting is
required.

### 11.6 Comparison with Other Semirings

| Aspect | Boolean | Tropical | Counting |
|:-------|:--------|:---------|:---------|
| Carrier set size | 2 | Uncountable (R+ union {inf}) | Countably infinite (N) |
| Information per state | 1 bit | 1 float | 1 integer |
| Primary question | "reachable?" | "cheapest?" | "how many?" |
| Idempotent | Yes | Yes | No |
| Typical use | dead code elimination | dispatch ordering | ambiguity detection |

---

## 12. Max-Plus (Arctic) Semiring

### 12.1 Formal Definition

The **max-plus semiring** (also called the **Arctic semiring**) over the
extended real numbers:

```
S  =  (ℝ ∪ {-∞}, max, +, -∞, 0)

K   =  ℝ ∪ {-∞}
a ⊕ b  =  max(a, b)    (select the maximum-reward alternative)
a ⊗ b  =  a + b        (accumulate reward along a path)
0̄      =  -∞           (no reward; identity for max)
1̄      =  0.0          (zero reward; identity for addition)
```

### 12.2 Properties

- **Commutative**: max(a, b) = max(b, a) and a + b = b + a.
- **Idempotent**: max(a, a) = a. Selecting the best reward twice yields the
  same result as selecting it once.

### 12.3 Maximum-Reward Semantics

Where the tropical semiring finds the *cheapest* (minimum cost) path, the
max-plus semiring finds the *most rewarding* (maximum reward) path. The ⊗
operation is identical — addition accumulates along sequential segments — but
the ⊕ operation takes max instead of min, selecting the path with highest
total reward.

### 12.4 Negation Duality with Tropical

Max-plus and Tropical are dual under negation. Given any weight assignment
w: Arcs -> R, define the negated assignment w'(e) = -w(e). Then:

```
            Duality Transform
   ┌───────────────────────────────────────┐
   │                                       │
   │  Tropical problem         Max-Plus    │
   │  minimize Σ w(eᵢ)   ←──►  maximize Σ r(eᵢ) │
   │                                       │
   │  Transform:  r(e) = -w(e)             │
   │                                       │
   │  min over paths of Σ w(eᵢ)            │
   │    = -max over paths of Σ (-w(eᵢ))    │
   │    = -max over paths of Σ r(eᵢ)       │
   │                                       │
   │  Proof:                               │
   │    min(a, b) = -max(-a, -b)           │
   │    a + b     = (-a) + (-b) negated    │
   │                                       │
   │  The optimal path is the same path    │
   │  under both formulations.             │
   │                                       │
   └───────────────────────────────────────┘
```

Formally, the map phi: R union {+inf} -> R union {-inf} defined by phi(x) = -x is a
semiring isomorphism from (R union {+inf}, min, +, +inf, 0) to
(R union {-inf}, max, +, -inf, 0). This means any algorithm written for Tropical
can be mechanically transformed to Max-Plus by negating all weights and
replacing min with max (or equivalently, negating inputs and outputs while
keeping the algorithm unchanged).

### 12.5 When Max-Plus is More Natural

Max-plus is the more natural choice when the weight semantics are inherently
reward-based rather than cost-based:

- **Longest-match lexing.** The reward is the number of characters consumed.
  The lexer should select the token that consumes the most input (maximal munch).
  Under max-plus, the longest match has the highest reward and is naturally
  selected by ⊕ = max.

- **Maximum-specificity dispatch.** When multiple rules match, prefer the most
  specific rule. Specificity can be modeled as a reward (more terminals = more
  specific = higher reward). Under max-plus, the most specific rule wins.

- **Confidence scoring.** If parse alternatives are scored by a confidence
  metric (higher = better), max-plus directly selects the highest-confidence
  alternative without negation gymnastics.

In each case, Tropical would work equally well after negating all weights,
but max-plus avoids the cognitive overhead of the negation transform and
makes the intent explicit in the algebra.

### 12.6 Comparison with Other Semirings

| Aspect | Max-Plus (Arctic) | Tropical | Log |
|:-------|:-------------------|:---------|:----|
| ⊕ operation | max (select best reward) | min (select least cost) | log-sum-exp (sum probabilities) |
| Optimization direction | maximize | minimize | N/A (sums, not optimizes) |
| Idempotent | Yes | Yes | No |
| Dual of | Tropical (via negation) | Max-Plus (via negation) | N/A |
| Natural for | rewards, confidence | costs, penalties | probabilities, training |

---

## 13. Edit Distance Semiring

### 13.1 Formal Definition

The **edit distance semiring** over the extended natural numbers:

```
S  =  (ℕ ∪ {+∞}, min, +, +∞, 0)

K   =  ℕ ∪ {+∞}
a ⊕ b  =  min(a, b)    (select the repair with fewest edits)
a ⊗ b  =  a + b        (accumulate edits along a path)
0̄      =  +∞           (no valid repair; identity for min)
1̄      =  0            (zero edits; identity for addition)
```

This is structurally identical to Tropical restricted to non-negative integers,
but the *interpretation* is fundamentally different: weights count Levenshtein
edit operations (insert, delete, substitute) rather than abstract costs.

### 13.2 Properties

- **Commutative**: min(a, b) = min(b, a) and a + b = b + a.
- **Idempotent**: min(a, a) = a. The minimum-edit repair is unique once found.

### 13.3 Construction from Levenshtein Operations

The edit transducer is a WFST that maps *any* input string to *every* string
in the target language, with each transition weighted by the number of edit
operations it represents:

```
  Edit Operations and Their Weights
  ┌────────────────────────────────────────────┐
  │  Operation    Input    Output    Weight     │
  │  ─────────    ─────    ──────    ──────     │
  │  Match        a        a         0          │
  │  Substitute   a        b         1  (a!=b)   │
  │  Delete       a        epsilon   1          │
  │  Insert       epsilon  b         1          │
  └────────────────────────────────────────────┘
```

The edit transducer has a single state with four self-loops (one per operation).
Composing it with the lexer or parser WFST yields a transducer that maps
erroneous input to the nearest valid parse, where "nearest" is measured by
Levenshtein distance.

### 13.4 Minimum-Repair Parsing

Composing the edit transducer **E** with the parser's recognition WFST **P**
yields a composed transducer **E o P** that, for any input string:

1. Finds all possible edits that transform the input into a string accepted
   by **P**.
2. Weights each edit sequence by the total number of operations (via ⊗ = +).
3. Selects the minimum-edit sequence (via ⊕ = min).

The shortest-path through **E o P** gives the *closest valid parse* — the
accepted string reachable from the input with the fewest insertions, deletions,
and substitutions.

```
  Composition: Edit Transducer ∘ Lexer WFST
  ┌───────────────────────────────────────────────────────────┐
  │                                                           │
  │  Input: "eror == tru"                                     │
  │                                                           │
  │  Edit              Lexer WFST                             │
  │  Transducer        (accepts valid token sequences)        │
  │  ┌─────┐           ┌─────┐     ┌─────┐     ┌─────┐       │
  │  │     │──(m/0)──► │ s0  │─e──►│ s1  │─r──►│ s2  │       │
  │  │  E  │──(s/1)──► │     │─r──►│     │─r──►│     │       │
  │  │     │──(d/1)──► │     │─o──►│     │─o──►│     │       │
  │  │     │──(i/1)──► │     │─r──►│     │─r──►│     │       │
  │  └─────┘           └─────┘     └─────┘     └─────┘       │
  │                                                           │
  │  Composed result (shortest path, distance 2):             │
  │                                                           │
  │  "eror"  →  "error"    (insert 'r' at pos 3)     cost 1  │
  │  " == "  →  " == "     (match)                    cost 0  │
  │  "tru"   →  "true"     (insert 'e' at end)       cost 1  │
  │                                                   ─────   │
  │  Total edit distance:                             2       │
  │                                                           │
  │  Repaired parse: Ident("error") Eq Ident("true")          │
  │                                                           │
  └───────────────────────────────────────────────────────────┘
```

### 13.5 PraTTaIL Integration

EditWeight is used in PraTTaIL's error recovery subsystem via the
`RepairAction::edit_cost()` method in `recovery.rs`, which computes the
edit-distance cost of each repair action (skip, delete, insert, substitute).
This provides a principled cost metric for comparing alternative repair
strategies.

The `liblevenshtein` library (at `/home/dylon/Workspace/f1r3fly.io/liblevenshtein-rust/`)
provides optimized Levenshtein automata that compute edit distances in time
linear in the query length. The key integration points with PraTTaIL's edit
distance semiring are:

- **Dictionary lookup.** `DynamicDawg` and `DoubleArrayTrie` provide fuzzy
  dictionary matching. When the lexer encounters an unrecognized token,
  `liblevenshtein` can suggest the nearest valid keyword or identifier within
  a bounded edit distance.

- **Automaton composition.** Levenshtein automata are themselves WFSTs with
  edit-distance weights. Composing a `liblevenshtein` automaton with PraTTaIL's
  lexer WFST is algebraically identical to the edit transducer composition
  described above, but benefits from `liblevenshtein`'s optimized state
  representation (parametric automata, SIMD acceleration).

- **Bounded error correction.** The `max_distance` parameter in `liblevenshtein`
  bounds the search space, preventing the composed transducer from exploring
  repairs beyond a practical threshold (typically 2-3 edits for identifiers,
  1 edit for keywords).

### 13.6 Comparison with Other Semirings

| Aspect | Edit Distance | Tropical | Boolean |
|:-------|:-------------|:---------|:--------|
| Carrier set | N union {+inf} | R+ union {+inf} | {0, 1} |
| Weight interpretation | number of edits | abstract cost | reachable? |
| Idempotent | Yes | Yes | Yes |
| Edit-aware | Yes (by construction) | No (weights are opaque) | No |
| Error recovery | closest valid parse | cheapest parse | any valid parse |
| Integration | `liblevenshtein` automata | `compute_action_weight` | forward/backward reachability |

---

## 14. Product Semiring

### 14.1 Formal Construction

Given two semirings **S1 = (K1, ⊕1, ⊗1, 0̄1, 1̄1)** and
**S2 = (K2, ⊕2, ⊗2, 0̄2, 1̄2)**, the **product semiring** is:

```
S₁ x S₂  =  (K₁ x K₂, ⊕, ⊗, 0̄, 1̄)

K   =  K₁ x K₂  =  { (a, b) | a ∈ K₁, b ∈ K₂ }
(a₁, a₂) ⊕ (b₁, b₂)  =  (a₁ ⊕₁ b₁,  a₂ ⊕₂ b₂)    [componentwise ⊕]
(a₁, a₂) ⊗ (b₁, b₂)  =  (a₁ ⊗₁ b₁,  a₂ ⊗₂ b₂)    [componentwise ⊗]
0̄  =  (0̄₁, 0̄₂)
1̄  =  (1̄₁, 1̄₂)
```

### 14.2 Properties

- **Commutative** if and only if both S1 and S2 are commutative.
- **Idempotent** if and only if both S1 and S2 are idempotent.

The product construction is a semiring because each axiom holds componentwise:
associativity, commutativity, identity, distribution, and annihilation all
decompose into independent statements about S1 and S2.

PraTTaIL's `ProductWeight` implements lexicographic `Ord` (left component
first, then right component), enabling natural priority ordering when the
left semiring carries the primary objective.

### 14.3 Application 1: Tropical x Counting — Disambiguation with Confidence

Combining Tropical (best weight) with Counting (number of alternatives) gives
a product weight (w, n) where:

- **w** = the cost of the best parse (Tropical component).
- **n** = the number of distinct parses with that cost (Counting component).

This enables disambiguation *with confidence*: if the best parse has weight 2.5
and n = 1, the grammar is unambiguous at that point. If n = 3, the best weight
is achieved by three distinct parses, and additional disambiguation (lookahead,
priority, user annotation) is needed.

```
  Tropical x Counting Product Semiring
  ┌───────────────────────────────────────────────────────┐
  │                                                       │
  │  Product operations:                                  │
  │    (w₁, n₁) ⊕ (w₂, n₂) = (min(w₁,w₂), n₁+n₂)      │
  │    (w₁, n₁) ⊗ (w₂, n₂) = (w₁+w₂,     n₁xn₂)       │
  │                                                       │
  │  Example dispatch entry for (Proc, state 7, Ident):   │
  │                                                       │
  │    Rule Send:    weight 1.0  →  contributes (1.0, 1)  │
  │    Rule Lookup:  weight 0.5  →  contributes (0.5, 1)  │
  │    Rule Invoke:  weight 1.0  →  contributes (1.0, 1)  │
  │                                                       │
  │    Combined via ⊕:                                    │
  │      (1.0, 1) ⊕ (0.5, 1) = (min(1.0,0.5), 1+1)      │
  │                           = (0.5, 2)                  │
  │      (0.5, 2) ⊕ (1.0, 1) = (min(0.5,1.0), 2+1)      │
  │                           = (0.5, 3)                  │
  │                                                       │
  │    Result: (0.5, 3)                                   │
  │      → best weight = 0.5 (Lookup wins on cost)        │
  │      → count = 3 (but 3 rules compete; only 1 has     │
  │        the best weight — Lookup at 0.5)               │
  │                                                       │
  │  Note: the count component sums ALL alternatives,     │
  │  not just those with the best weight. To count only   │
  │  best-weight alternatives, a filtered product is      │
  │  needed (not shown here).                             │
  │                                                       │
  └───────────────────────────────────────────────────────┘
```

### 14.4 Application 2: Tropical x Edit — Parsing with Error Tolerance

Combining Tropical (parse cost) with Edit Distance (repair distance) gives
a product weight (w, d) where:

- **w** = the cost of the parse under the grammar's weight scheme.
- **d** = the number of edit operations needed to reach a valid parse.

This enables error-tolerant parsing where the parser simultaneously finds the
best parse *and* reports how much input repair was needed.

```
  Tropical x Edit Distance Product Semiring
  ┌───────────────────────────────────────────────────────┐
  │                                                       │
  │  Product operations:                                  │
  │    (w₁, d₁) ⊕ (w₂, d₂) = (min(w₁,w₂), min(d₁,d₂)) │
  │    (w₁, d₁) ⊗ (w₂, d₂) = (w₁+w₂,      d₁+d₂)      │
  │                                                       │
  │  Example: parsing "x +* y" (spurious '*')             │
  │                                                       │
  │    Path 1: delete '*'                                 │
  │      parse cost w = 1.0 + 0.5 = 1.5                  │
  │      edit distance d = 0 + 1 + 0 = 1                 │
  │      product weight: (1.5, 1)                        │
  │                                                       │
  │    Path 2: substitute '*' for another operator        │
  │      parse cost w = 1.0 + 2.0 = 3.0                  │
  │      edit distance d = 0 + 1 + 0 = 1                 │
  │      product weight: (3.0, 1)                        │
  │                                                       │
  │    Combined: (1.5, 1) ⊕ (3.0, 1) = (1.5, 1)         │
  │      → best parse cost 1.5 with 1 edit               │
  │      → the "delete '*'" repair is chosen              │
  │                                                       │
  └───────────────────────────────────────────────────────┘
```

### 14.5 Comparison with Other Semirings

| Aspect | Product | Tropical | Counting |
|:-------|:--------|:---------|:---------|
| Carrier set | K1 x K2 | R+ union {+inf} | N |
| Information per state | 2+ values | 1 value | 1 value |
| Multi-objective | Yes (by construction) | No (single objective) | No (single objective) |
| Computational cost | Sum of components | O(1) | O(1) |
| Flexibility | Arbitrary semiring pairs | Fixed (min, +) | Fixed (+, x) |

The product semiring's power lies in composability: any two semirings from this
catalog can be combined to answer two questions simultaneously in a single
forward pass over the lattice.

---

## 15. Rule Specificity Weights

### 15.1 Motivation

When PraTTaIL composes dispatch tables from grammar rules, it needs
a *default* weight strategy for rules that have no explicit priority annotation
and no trained weights. The strategy must satisfy three properties:

1. **More specific rules should have lower weight** (higher priority under
   Tropical ⊕ = min).
2. **The strategy must be deterministic** — the same grammar always produces
   the same weights.
3. **Weights must compose correctly** under Tropical ⊗ = addition, so that
   multi-step dispatch paths accumulate specificity naturally.

### 15.2 Specificity Formula

The specificity weight for a rule is:

```
weight(rule) = 1 / (1 + terminals + 0.5 x NTs)
```

where:
- **terminals** = the number of terminal symbols (keywords, operators,
  delimiters) in the rule's right-hand side.
- **NTs** = the number of non-terminal references in the rule's right-hand
  side.

Terminal symbols contribute full weight (1.0 each) because they are exact
matches — a rule with more terminals is strictly more specific about the
input it accepts. Non-terminal references contribute half weight (0.5 each)
because they are variable — any derivation of the non-terminal category can
fill that position.

The `1 +` in the denominator ensures the weight is always in (0, 1], with
1.0 for rules containing no symbols (epsilon productions) and values
approaching 0 for highly specific rules.

### 15.3 Comparison: Specificity vs Token Priority vs Trained Probabilities

| Strategy | Source | Advantages | Disadvantages |
|:---------|:-------|:-----------|:--------------|
| **Specificity** | Rule structure (automated) | Deterministic, requires no annotation, reasonable defaults | Does not capture semantic intent; purely structural |
| **Token priority** | `priority` annotation on tokens | Grammar author controls precedence explicitly | Requires manual annotation; does not scale to large grammars |
| **Trained probabilities** | Corpus-trained `TrainedModel` (feature `wfst-log`) | Data-driven, adapts to real usage patterns | Requires training corpus; non-deterministic across corpora |

Specificity weights serve as the **baseline** — the weights used when no other
information is available. Token priority *overrides* specificity for annotated
tokens. Trained probabilities *replace* specificity entirely when a trained
model is loaded. The three strategies form a hierarchy:

```
  Weight Strategy Hierarchy
  ┌─────────────────────────────────────────────┐
  │                                             │
  │  Trained probabilities  (highest fidelity)  │
  │    ↑ replaces                               │
  │  Token priority         (manual override)   │
  │    ↑ overrides                              │
  │  Specificity            (structural default)│
  │                                             │
  └─────────────────────────────────────────────┘
```

### 15.4 Composition Under Tropical ⊗

Under the tropical semiring, ⊗ = addition. When a parse path traverses
multiple dispatch entries, the specificity weights accumulate:

```
w(path) = w(rule₁) ⊗ w(rule₂) ⊗ ... ⊗ w(ruleₙ)
        = w(rule₁) + w(rule₂) + ... + w(ruleₙ)
```

Because each w(rule) is in (0, 1], the accumulated path weight grows
sub-linearly with path length, and paths through more-specific rules
accumulate lower total weight. This is correct: a parse path through
highly specific rules at every step should be preferred over a path through
generic fallback rules.

Consider two competing parse paths of length 2:

```
Path A: rule₁ (3 terminals, 1 NT) → rule₃ (2 terminals, 0 NTs)
  w₁ = 1/(1 + 3 + 0.5x1) = 1/4.5 ≈ 0.222
  w₃ = 1/(1 + 2 + 0) = 1/3 ≈ 0.333
  w(A) = 0.222 + 0.333 = 0.556

Path B: rule₂ (0 terminals, 2 NTs) → rule₄ (1 terminal, 1 NT)
  w₂ = 1/(1 + 0 + 0.5x2) = 1/2 = 0.500
  w₄ = 1/(1 + 1 + 0.5x1) = 1/2.5 = 0.400
  w(B) = 0.500 + 0.400 = 0.900

⊕ = min: w(A) < w(B), so Path A (more specific) is preferred.
```

### 15.5 Worked Example: Compare vs Var Dispatch

Consider the Rholang-inspired grammar fragment for category `Proc`:

```
rule Compare:  Proc ::= Expr "==" Expr       [2 NTs, 1 terminal ("==")]
rule Var:      Proc ::= name                  [0 NTs, 1 terminal (name)]
```

Note: `name` is treated as a terminal (it matches a single identifier token),
while `Expr` is a non-terminal reference.

Specificity weights:

```
  w(Compare) = 1 / (1 + 1 + 0.5 x 2)
             = 1 / (1 + 1 + 1)
             = 1 / 3
             ≈ 0.333

  w(Var)     = 1 / (1 + 1 + 0.5 x 0)
             = 1 / (1 + 1 + 0)
             = 1 / 2
             = 0.500
```

Under Tropical ⊕ = min:

```
  Dispatch for (Proc, Ident lookahead):
    Compare contributes weight 0.333
    Var     contributes weight 0.500

    ⊕ = min(0.333, 0.500) = 0.333  →  Compare wins
```

This is the correct disambiguation: when the lookahead is an identifier and
both Compare and Var are candidates, Compare is more specific because it
requires additional structure (`"=="` and a second `Expr`) beyond the initial
identifier. The specificity formula captures this structural difference
automatically.

```
  Composed Dispatch Table for Proc
  ┌───────────────────────────────────────────────────────────┐
  │  State   Token     Rule       Specificity   Selected     │
  │  ─────   ─────     ────       ───────────   ────────     │
  │    0     Ident     Compare    0.333         yes (min)    │
  │    0     Ident     Var        0.500         no           │
  │    0     Integer   NumLit     0.500         yes (only)   │
  │    0     LParen    Group      0.333         yes (only)   │
  └───────────────────────────────────────────────────────────┘
```

When only one rule matches a (state, token) pair (e.g., Integer->NumLit or
LParen->Group), the specificity weight is irrelevant — the sole candidate is
selected regardless. Specificity only matters for disambiguation among
competing alternatives, which is precisely the case where a principled default
weight strategy is most valuable.

### 15.6 Comparison with Other Semirings

| Aspect | Specificity Weights | Token Priority | Trained (LogWeight) |
|:-------|:-------------------|:---------------|:--------------------|
| Semiring | Tropical | Tropical | Log |
| Source | Automated from rule structure | Manual annotation | Corpus training |
| Range | (0, 1] | {0, ..., 10} mapped to [0, 10] | R+ union {+inf} |
| Composition | ⊗ = + (accumulates) | ⊗ = + (accumulates) | ⊗ = + (log-domain multiply) |
| Multi-rule paths | Lower total = more specific | Lower total = higher priority | Lower total = more probable |
| Requires user input | No | Yes (annotations) | Yes (training corpus) |
| Granularity | Per-rule | Per-token | Per-arc |
