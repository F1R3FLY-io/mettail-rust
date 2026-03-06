# EntropyWeight -- Design & Pipeline Integration

> **Date:** 2026-03-01

The expectation semiring `(R x R, plus, times, (inf, 0), (0, 0))` computes Shannon
entropy over parse dispatch distributions. It answers the question: "how uncertain
is the parser at this dispatch point?" A high-entropy dispatch token means many
rules compete with similar probability, signalling a grammar ambiguity hotspot
that benefits from wider beam search or grammar restructuring. A low-entropy
dispatch token means one rule dominates, and the parser can commit quickly with
minimal backtracking risk.

---

## Table of Contents

1. [Problem Statement](#1-problem-statement)
2. [Data Structure](#2-data-structure)
3. [The `from_arc_weight()` Constructor](#3-the-from_arc_weight-constructor)
4. [The `entropy_bits()` Conversion](#4-the-entropy_bits-conversion)
5. [Semiring Operations](#5-semiring-operations)
6. [Numerical Stability](#6-numerical-stability)
7. [Ordering](#7-ordering)
8. [Display Format](#8-display-format)
9. [Pipeline Integration](#9-pipeline-integration)
10. [Feature Gate: `wfst-log`](#10-feature-gate-wfst-log)
11. [ProductWeight Composition with TropicalWeight](#11-productweight-composition-with-tropicalweight)
12. [Worked Example: 3-Rule Dispatch Group](#12-worked-example-3-rule-dispatch-group)
13. [Test Coverage Summary](#13-test-coverage-summary)
14. [Source References](#14-source-references)
15. [Cross-References](#15-cross-references)

---

## 1. Problem Statement

CountingWeight tells us **how many** rules compete at a dispatch token.
ContextWeight tells us **which** rules compete. Neither tells us **how evenly**
the competition is distributed. Two dispatch points can both have 3-way ambiguity
(CountingWeight = 3) yet behave very differently at runtime:

```
Dispatch point A:  Rule R1 = 90%, R2 = 5%,  R3 = 5%    H = 0.57 bits
Dispatch point B:  Rule R1 = 33%, R2 = 33%, R3 = 33%    H = 1.58 bits
```

Point A has a clear winner -- beam pruning can safely discard R2 and R3 with
minimal risk. Point B is maximally uncertain -- all three rules are equally
likely, and aggressive pruning would discard valid parses with probability 2/3.

Shannon entropy `H = -sum(p_i * ln(p_i))` quantifies this distinction. It enables
three pipeline capabilities that counting alone cannot:

| Capability                  | Why Counting Is Insufficient                                    | What Entropy Provides                                               |
|-----------------------------|-----------------------------------------------------------------|---------------------------------------------------------------------|
| **Adaptive beam width**     | A count of 3 says nothing about whether pruning is safe         | H < 0.5 bits: narrow beam; H > 1.5 bits: wide beam                  |
| **Grammar design feedback** | "3-way ambiguity" is actionable but imprecise                   | "1.58 bits at Ident in Proc" pinpoints the hotspot and its severity |
| **Training convergence**    | No measure of how close the model is to a decisive distribution | When total H stabilizes across epochs, the model has converged      |

The expectation semiring computes Shannon entropy as a byproduct of the
forward-backward algorithm, requiring no separate pass over the WFST.

---

## 2. Data Structure

EntropyWeight is a pair of `f64` values (`semiring.rs:1120-1125`):

```rust
#[cfg(feature = "wfst-log")]
#[derive(Clone, Copy)]
pub struct EntropyWeight {
    /// Total weight in negative log-probability space.
    pub weight: f64,
    /// Accumulated expected value (entropy contribution).
    pub expectation: f64,
}
```

**Carrier set**: Pairs `(w, e)` where:

- `w` = total weight in negative log-probability space (like LogWeight).
  Lower `w` = higher probability: `p = exp(-w)`.
- `e` = accumulated expected value. When initialized for Shannon entropy
  computation, this tracks `E[-ln p] = sum(p_i * w_i)` -- the expected
  negative log-probability, which equals Shannon entropy H.

**Why two fields**: A single float cannot simultaneously track probability mass
and expected value. The pair `(w, e)` is the minimal representation that supports
both log-sum-exp combination of probabilities (via `w`) and probability-weighted
averaging of expectations (via `e`). This is the first-order expectation semiring
of Li & Eisner (2009).

**Copy semantics**: Both fields are `f64`, so EntropyWeight is `Copy` with no
heap allocation. This is critical for embedding in `ProductWeight<TropicalWeight,
EntropyWeight>` and for use in tight forward-backward loops.

**Memory layout**: 16 bytes (two 64-bit IEEE 754 doubles). No padding, no
indirection.

---

## 3. The `from_arc_weight()` Constructor

The key constructor for Shannon entropy computation (`semiring.rs:1135-1146`):

```rust
/// Create an EntropyWeight for a single arc with the given weight.
///
/// For Shannon entropy computation, set expectation = weight (the arc's
/// negative log-probability). This way, after forward-backward, the total
/// expectation gives H = -sum(p_i * ln(p_i)).
#[inline]
pub const fn from_arc_weight(weight: f64) -> Self {
    EntropyWeight {
        weight,
        expectation: weight,
    }
}
```

**Mathematical justification**: Shannon entropy is:

```
H = -sum_i p_i * ln(p_i) = sum_i p_i * w_i
```

where `w_i = -ln(p_i)` is the negative log-probability of arc `i`. Setting
`e_i = w_i` on each arc means the expectation component tracks exactly
`E[w] = sum(p_i * w_i) = H`.

After forward-backward, the expectation at the final state equals the total
entropy of the distribution over all paths.

**When to use `new()` instead**: The general constructor `new(weight, expectation)`
(`semiring.rs:1129-1133`) is used when `e` tracks something other than entropy --
for example, expected parse tree depth, expected rule application count, or any
other real-valued feature whose expectation under the path distribution is desired.

---

## 4. The `entropy_bits()` Conversion

The `entropy_bits()` method converts from natural units (nats) to bits
(`semiring.rs:1160-1164`):

```rust
/// Compute entropy in bits (divide by ln(2)).
#[inline]
pub fn entropy_bits(&self) -> f64 {
    self.expectation / std::f64::consts::LN_2
}
```

**Why nats internally**: The negative log-probability weights use the natural
logarithm (`ln`), which is the convention in information theory and numerical
optimization. The `exp` and `ln` functions in the log-sum-exp computation are
natural, so storing entropy in nats avoids a conversion factor in every
arithmetic operation.

**Why bits externally**: Grammar designers and parser diagnostics communicate in
bits because they map to intuitive yes/no questions. "2.0 bits of entropy at
Ident in Proc" means the parser needs approximately 2 binary decisions to resolve
the ambiguity -- roughly 4 equally likely alternatives. The conversion formula is:

```
H_bits = H_nats / ln(2) = H_nats / 0.6931...
```

**Example**: If the expectation component after forward-backward is `ln(4) =
1.3863` nats, then `entropy_bits()` returns `1.3863 / 0.6931 = 2.0` bits. This
matches the entropy of a uniform distribution over 4 outcomes.

---

## 5. Semiring Operations

EntropyWeight implements the semiring `(R x R, plus, times, (inf, 0), (0, 0))`
(`semiring.rs:1186-1298`):

### 5a. Identity Elements

| Element          | `weight` | `expectation` | Meaning                                      |
|------------------|----------|---------------|----------------------------------------------|
| **Zero** `0-bar` | `+inf`   | `0.0`         | No paths: zero probability, zero entropy     |
| **One** `1-bar`  | `0.0`    | `0.0`         | Single path with probability 1, zero entropy |

Zero represents the absence of any derivation. One represents a certain,
deterministic outcome (no uncertainty, hence zero entropy).

### 5b. Times (Sequencing)

```rust
fn times(&self, other: &Self) -> Self {
    EntropyWeight {
        weight: self.weight + other.weight,
        expectation: self.expectation + other.expectation,
    }
}
```

**Semantics**: Concatenating two path segments multiplies their probabilities
(adds their negative log-probabilities) and sums their expected values. This is
the chain rule of expectation: `E[X + Y] = E[X] + E[Y]` for independent segments.

**Complexity**: O(1), two floating-point additions.

### 5c. Plus (Combination)

Plus is the most complex operation (`semiring.rs:1215-1265`). It combines
parallel paths:

- **Weight**: `log-sum-exp(w_1, w_2) = -ln(exp(-w_1) + exp(-w_2))` -- combines
  probabilities in log space.
- **Expectation**: Probability-weighted mixture:
  `e_new = (p_1 * e_1 + p_2 * e_2) / (p_1 + p_2)` where `p_i = exp(-w_i)`.

The implementation factors out `exp(-w_min)` from numerator and denominator for
numerical stability (see section 6).

---

## 6. Numerical Stability

The plus operation uses three safeguards to prevent floating-point overflow and
underflow (`semiring.rs:1215-1265`):

### 6a. Infinity Short-Circuits

```rust
if self.weight == f64::INFINITY {
    return *other;
}
if other.weight == f64::INFINITY {
    return *self;
}
```

Adding zero probability (`w = +inf`) to any distribution leaves it unchanged.
This prevents `exp(-inf) = 0` from polluting the weighted average.

### 6b. Log-Sum-Exp with Min-Shift

The `log_sum_exp` helper (`semiring.rs:1166-1182`):

```rust
fn log_sum_exp(a: f64, b: f64) -> f64 {
    let min_val = a.min(b);
    let diff = (a - b).abs();
    if diff > 20.0 {
        min_val
    } else {
        min_val - (1.0 + (-diff).exp()).ln()
    }
}
```

Shifting by `min(a, b)` ensures the exponentiated difference `exp(-|a - b|)` is
always in `[0, 1]`, avoiding overflow. The threshold of 20.0 corresponds to a
probability ratio of `exp(-20) ~ 2 * 10^-9` -- below this, the smaller term
contributes less than double-precision epsilon and can be safely dropped.

### 6c. Expectation Mixture with Relative Probabilities

```rust
let diff_self = self.weight - w_min;    // >= 0
let diff_other = other.weight - w_min;  // >= 0

if diff_self > 20.0 {
    // other dominates
    ...
} else if diff_other > 20.0 {
    // self dominates
    ...
} else {
    let r_self = (-diff_self).exp();
    let r_other = (-diff_other).exp();
    let denom = r_self + r_other;
    let new_expectation =
        (r_self * self.expectation + r_other * other.expectation) / denom;
    ...
}
```

The relative probabilities `r_i = exp(-(w_i - w_min))` are always in `(0, 1]`,
so no individual `exp()` call can overflow. When one path dominates by more than
20 nats, its expectation is taken directly, skipping the division entirely.

---

## 7. Ordering

EntropyWeight uses a two-level comparison (`semiring.rs:1344-1352`):

```rust
impl Ord for EntropyWeight {
    fn cmp(&self, other: &Self) -> Ordering {
        self.weight
            .total_cmp(&other.weight)
            .then_with(|| self.expectation.total_cmp(&other.expectation))
    }
}
```

**Level 1: Weight** (negative log-probability). Lower weight = higher probability
= "better" in the Viterbi sense. This aligns with TropicalWeight ordering: the
most probable path sorts first.

**Level 2: Expectation** (deterministic tiebreaker). Among paths with equal
probability, lower expectation sorts first. This provides a total order for use
in BTreeMap keys and sorted output.

**`total_cmp`**: Uses IEEE 754 total ordering, which handles NaN, -0.0, and
+0.0 deterministically. This is essential for reproducible codegen output.

---

## 8. Display Format

Two display implementations (`semiring.rs:1301-1323`):

| Trait     | Zero Output             | Normal Output         | Example                         |
|-----------|-------------------------|-----------------------|---------------------------------|
| `Debug`   | `EntropyWeight(inf, 0)` | `EntropyWeight(w, e)` | `EntropyWeight(2.3000, 1.5000)` |
| `Display` | `(inf, 0)`              | `(w, e)`              | `(2.3000, 1.5000)`              |

Both use 4 decimal places for the non-zero case. The Display format is compact
for embedding in diagnostic messages:

```
info: category Proc at Token::Ident: entropy = (0.6931, 0.6931) = 1.00 bits
```

---

## 9. Pipeline Integration

### 9a. Where Entropy Is Computed

Entropy flows through the pipeline at three stages:

```
┌────────────────────────┐
│ WFST Construction      │
│ (pipeline.rs)          │
│                        │
│ For each (cat, tok):   │
│   w_i = TropicalWeight │
│   arc_i = from_arc_    │
│          weight(w_i)   │
└───────────┬────────────┘
            │
            ▼
┌────────────────────────┐
│ Forward-Backward       │
│ (forward_backward.rs)  │
│                        │
│ alpha = forward_       │
│         scores(edges)  │
│ H = alpha[final]       │
│     .expectation       │
└───────────┬────────────┘
            │
            ▼
┌────────────────────────┐
│ Diagnostic Output      │
│ (lint.rs, pipeline)    │
│                        │
│ H_bits = H.entropy_    │
│          bits()        │
│ Adaptive beam width    │
│ Grammar feedback       │
└────────────────────────┘
```

**Stage 1: Arc initialization**. During WFST construction, each dispatch arc's
TropicalWeight `w_i` is converted to an EntropyWeight via `from_arc_weight(w_i)`.
This sets `(weight, expectation) = (w_i, w_i)` -- the arc carries its own
negative log-probability as the quantity whose expectation we are computing.

**Stage 2: Forward-backward**. The generic `forward_scores()` function
(`forward_backward.rs:33-48`) accepts any `W: Semiring`, including EntropyWeight.
When run with EntropyWeight edges, `alpha[final_node].expectation` equals the
Shannon entropy `H = -sum(p_i * ln(p_i))` over all paths from start to final.

**Stage 3: Diagnostic consumption**. The resulting entropy feeds into:

- **Adaptive beam width**: The beam width for a category's dispatch can be
  adjusted based on its entropy. The mapping function is:

  ```
  beam_width(H) = base_beam * (1 + k * H_bits)
  ```

  where `base_beam` is the configured minimum beam width (e.g., 1.0) and `k` is
  a scaling factor (e.g., 0.5). At H = 0 bits (deterministic), the beam equals
  `base_beam`. At H = 2 bits (4-way uniform ambiguity), the beam widens to
  `base_beam * 2.0`, admitting more alternatives before pruning.

- **Grammar design feedback**: The lint layer (`lint.rs`) can emit diagnostics
  when entropy exceeds a threshold:

  ```
  warning[G05]: high dispatch entropy at (Proc, Ident): 2.3 bits
    → 5 rules compete with similar weights; consider refining lookahead
  ```

- **Training convergence**: During weight training (`training.rs`), total entropy
  across all dispatch points serves as a convergence criterion. When
  `|H_epoch_n - H_epoch_{n-1}| < epsilon`, the distribution has stabilized and
  training can stop.

### 9b. How Entropy Flows to Adaptive Beam Width

The beam width integration point is `PredictionWfst::predict_pruned()`
(`wfst.rs:214-226`). Currently, beam width is a static configuration
(`BeamWidthConfig::Explicit(f)` or `BeamWidthConfig::Auto`). EntropyWeight
enables a per-dispatch-token beam:

```
For each (category, token) in dispatch table:
    1. Build EntropyWeight edges from the WFST transitions for this token
    2. Run forward_scores() to get H at the final state
    3. Compute adaptive_beam = base_beam * (1 + k * H.entropy_bits())
    4. Store adaptive_beam in the WFST metadata for this token
    5. predict_pruned() uses the per-token beam instead of a global beam
```

This replaces the current uniform beam with a per-dispatch-point beam that is
tight where the grammar is unambiguous and wide where it is genuinely uncertain.

### 9c. Grammar Design Feedback

Entropy per dispatch point can be aggregated into a category-level report:

```
Category     Max H (bits)  Avg H (bits)  Hotspot Token
─────────────────────────────────────────────────────────
Proc         2.31          0.87          Ident
Expr         1.58          0.42          LParen
Name         0.00          0.00          (none)
```

This report identifies which categories would benefit most from additional
lookahead tokens, prefix factoring, or rule restructuring. A max entropy of
0.00 bits indicates fully deterministic dispatch.

---

## 10. Feature Gate: `wfst-log`

EntropyWeight is gated behind `#[cfg(feature = "wfst-log")]`
(`semiring.rs:1118`). Three reasons motivate this:

1. **Log-space dependency**: The plus operation requires `exp()` and `ln()` --
   transcendental functions that are relatively expensive compared to the `min`
   and `+` of TropicalWeight. Grammars that do not need entropy analysis should
   not pay for these computations even at compile time.

2. **Forward-backward dependency**: Computing entropy requires the
   forward-backward algorithm (`forward_backward.rs`), which is also gated behind
   `wfst-log`. EntropyWeight without forward-backward is usable only for manual
   semiring arithmetic, which is a testing/research use case.

3. **Training co-gating**: The training convergence use case
   (`training.rs:181-188`) requires both LogWeight (for loss computation) and
   EntropyWeight (for convergence monitoring). Both are `wfst-log` features,
   ensuring the entire training subsystem is gated consistently.

**When to enable**: Enable `wfst-log` when you need:
- Adaptive beam width based on dispatch entropy
- Grammar design feedback reports
- Training with convergence monitoring
- Forward-backward analysis for any purpose

**Default builds** (no `wfst-log`): EntropyWeight is not compiled. The pipeline
uses TropicalWeight + CountingWeight for dispatch, which is sufficient for
deterministic parsing with static beam widths.

---

## 11. ProductWeight Composition with TropicalWeight

### 11a. Type Alias

```rust
type EntropyDispatch = ProductWeight<TropicalWeight, EntropyWeight>;
```

This composition pairs the tropical priority (used for Viterbi path selection)
with the entropy measurement (used for adaptive beam and diagnostics).

### 11b. Operation Semantics

| Operation | Left (Tropical) | Right (Entropy)                  | Combined Semantics                             |
|-----------|-----------------|----------------------------------|------------------------------------------------|
| `plus`    | `min(w_a, w_b)` | `log-sum-exp + weighted mixture` | Best priority + entropy of merged alternatives |
| `times`   | `w_a + w_b`     | `(w_a + w_b, e_a + e_b)`         | Accumulated cost + accumulated expected value  |
| `zero`    | `+inf`          | `(+inf, 0.0)`                    | Unreachable, zero entropy                      |
| `one`     | `0.0`           | `(0.0, 0.0)`                     | Zero cost, zero entropy                        |

**Plus semantics**: When merging parallel dispatch alternatives, the tropical
component selects the best priority while the entropy component computes the
Shannon entropy of the merged distribution. The entropy component provides
strictly more information than the tropical component alone: it measures not
just the winner but the shape of the competition.

**Times semantics**: When sequencing path segments, both components add
independently. This is correct because tropical weight is additive along paths
(probabilities multiply, log-probabilities add) and expected values are additive
for independent segments.

### 11c. Viterbi Compatibility

EntropyWeight's `zero = (+inf, 0.0)` sorts as the largest value under `Ord`
(since `+inf` is the largest `f64`). This is correct for Viterbi: zero represents
an unreachable state, which should never be selected as the best path. The `Ord`
ordering ensures `zero` loses to any finite-weight path.

In `ProductWeight<TropicalWeight, EntropyWeight>`, the lexicographic ordering
compares TropicalWeight first, then EntropyWeight. Since both components have
zero as their largest element, the product zero is the largest product value,
making the product Viterbi-safe.

---

## 12. Worked Example: 3-Rule Dispatch Group

Consider category `Proc` with three rules dispatched by `Token::Ident`:

```
Rule PInput:    w = 0.5  (p = exp(-0.5) = 0.6065)
Rule POutput:   w = 1.0  (p = exp(-1.0) = 0.3679)
Rule PNew:      w = 3.0  (p = exp(-3.0) = 0.0498)
```

### Step 1: Initialize Arc Weights

```
e_input  = EntropyWeight::from_arc_weight(0.5)  = (0.5, 0.5)
e_output = EntropyWeight::from_arc_weight(1.0)  = (1.0, 1.0)
e_new    = EntropyWeight::from_arc_weight(3.0)  = (3.0, 3.0)
```

### Step 2: Combine via Plus (first two)

Combine `e_input` and `e_output`:

```
w_min = min(0.5, 1.0) = 0.5

Weight:
  log_sum_exp(0.5, 1.0)
  = 0.5 - ln(1 + exp(-(1.0 - 0.5)))
  = 0.5 - ln(1 + exp(-0.5))
  = 0.5 - ln(1 + 0.6065)
  = 0.5 - ln(1.6065)
  = 0.5 - 0.4741
  = 0.0259

Expectation:
  r_input  = exp(-(0.5 - 0.5)) = exp(0) = 1.0
  r_output = exp(-(1.0 - 0.5)) = exp(-0.5) = 0.6065
  denom = 1.0 + 0.6065 = 1.6065
  e_new = (1.0 * 0.5 + 0.6065 * 1.0) / 1.6065
        = (0.5 + 0.6065) / 1.6065
        = 1.1065 / 1.6065
        = 0.6887

Result: e_12 = (0.0259, 0.6887)
```

### Step 3: Combine with Third Rule

Combine `e_12 = (0.0259, 0.6887)` with `e_new = (3.0, 3.0)`:

```
w_min = min(0.0259, 3.0) = 0.0259

Weight:
  diff = |0.0259 - 3.0| = 2.9741
  log_sum_exp(0.0259, 3.0) = 0.0259 - ln(1 + exp(-2.9741))
                            = 0.0259 - ln(1 + 0.0511)
                            = 0.0259 - ln(1.0511)
                            = 0.0259 - 0.0498
                            = -0.0239

Expectation:
  r_12  = exp(-(0.0259 - 0.0259)) = 1.0
  r_new = exp(-(3.0 - 0.0259))    = exp(-2.9741) = 0.0511
  denom = 1.0 + 0.0511 = 1.0511
  e_final = (1.0 * 0.6887 + 0.0511 * 3.0) / 1.0511
          = (0.6887 + 0.1533) / 1.0511
          = 0.8420 / 1.0511
          = 0.8011

Result: e_final = (-0.0239, 0.8011)
```

### Step 4: Convert to Bits

```
H_nats = e_final.expectation = 0.8011 nats
H_bits = 0.8011 / ln(2) = 0.8011 / 0.6931 = 1.156 bits
```

### Interpretation

```
┌──────────────────────────────────────────────────┐
│ Dispatch Point: (Proc, Token::Ident)             │
│                                                  │
│ Rules:                                           │
│   PInput   w=0.5   p=59.2%  ████████████████░░░░ │
│   POutput  w=1.0   p=35.9%  ██████████░░░░░░░░░░ │
│   PNew     w=3.0   p= 4.9%  █░░░░░░░░░░░░░░░░░░░ │
│                                                  │
│ Shannon entropy: H = 1.156 bits                  │
│ Maximum possible (uniform 3-way): 1.585 bits     │
│ Normalized entropy: 1.156 / 1.585 = 72.9%        │
│                                                  │
│ Recommendation: moderate ambiguity; widen beam   │
│   from default 1.0 to 1.0 * (1 + 0.5 * 1.156)    │
│   = 1.578                                        │
└──────────────────────────────────────────────────┘
```

The entropy of 1.156 bits (out of a maximum 1.585 for uniform 3-way) indicates
substantial but not maximal ambiguity. PInput is the clear favorite (59.2%), but
POutput (35.9%) is competitive enough that aggressive pruning could cause
incorrect parses. The adaptive beam formula widens the search from 1.0 to 1.578,
keeping POutput in the beam while still pruning PNew (4.9%).

---

## 13. Test Coverage Summary

Thirteen tests in `semiring.rs:2468-2637` cover EntropyWeight:

| #  | Test                                        | Lines     | What It Verifies                                                                                          |
|----|---------------------------------------------|-----------|-----------------------------------------------------------------------------------------------------------|
| 1  | `test_entropy_weight_semiring_laws`         | 2472-2489 | Zero/one identity, zero annihilation                                                                      |
| 2  | `test_entropy_weight_times_is_addition`     | 2492-2498 | Times adds both components: `(2+3, 1.5+2.0) = (5, 3.5)`                                                   |
| 3  | `test_entropy_weight_plus_equal_weights`    | 2501-2520 | Equal weights: `log_sum_exp(1,1) = 1 - ln(2)`, expectations average to `(2+4)/2 = 3.0`                    |
| 4  | `test_entropy_weight_plus_unequal_weights`  | 2523-2534 | Dominant path (w=0.1) overwhelms minor path (w=10.0); expectation stays near 5.0                          |
| 5  | `test_entropy_weight_plus_commutativity`    | 2537-2543 | `a.plus(&b) approx_eq b.plus(&a)` -- plus is commutative                                                  |
| 6  | `test_entropy_weight_from_arc_weight`       | 2546-2550 | `from_arc_weight(2.5)` sets both components to 2.5                                                        |
| 7  | `test_entropy_weight_entropy_bits`          | 2553-2561 | `expectation = ln(4)` nats converts to `2.0` bits                                                         |
| 8  | `test_entropy_weight_plus_large_diff`       | 2564-2575 | Weight difference > 20.0 triggers the numerical stability fast path                                       |
| 9  | `test_entropy_weight_distributivity_approx` | 2578-2593 | `a * (b + c) approx_eq (a * b) + (a * c)` -- distributivity holds                                         |
| 10 | `test_entropy_weight_ordering`              | 2596-2602 | `(1.0, 0.5) < (5.0, 0.5) < zero` -- lower weight = better                                                 |
| 11 | `test_entropy_weight_display`               | 2605-2609 | Format: `"(1.5000, 2.3000)"` for normal, `"(inf, 0)"` for zero                                            |
| 12 | `test_entropy_weight_hash`                  | 2613-2619 | HashSet membership via `to_bits()` hashing                                                                |
| 13 | `test_entropy_weight_product_with_tropical` | 2622-2637 | `ProductWeight<TropicalWeight, EntropyWeight>`: plus = `(min, entropy_plus)`, times = `(add, (add, add))` |

**Coverage analysis**:

- **Semiring axioms**: Tests 1, 5, 9 cover identity, commutativity, distributivity
- **Plus edge cases**: Tests 3, 4, 8 cover equal weights, dominant paths, large differences
- **Constructors**: Tests 1, 6 cover `new()`, `from_arc_weight()`, `zero()`, `one()`
- **Conversion**: Test 7 covers `entropy_bits()`
- **Trait impls**: Tests 10, 11, 12 cover `Ord`, `Display`, `Hash`
- **Composition**: Test 13 covers `ProductWeight` integration

---

## 14. Source References

| Component                                                            | File                  | Lines     |
|----------------------------------------------------------------------|-----------------------|-----------|
| Module header & doc comment                                          | `semiring.rs`         | 1085-1117 |
| Struct definition                                                    | `semiring.rs`         | 1118-1125 |
| `new()`, `from_arc_weight()`, `weight()`, `expectation()`            | `semiring.rs`         | 1128-1158 |
| `entropy_bits()`                                                     | `semiring.rs`         | 1160-1164 |
| `log_sum_exp()`                                                      | `semiring.rs`         | 1166-1182 |
| `Semiring` impl (zero, one, plus, times, is_zero, is_one, approx_eq) | `semiring.rs`         | 1186-1298 |
| `Debug` impl                                                         | `semiring.rs`         | 1301-1313 |
| `Display` impl                                                       | `semiring.rs`         | 1316-1323 |
| `PartialEq` / `Eq` impl                                              | `semiring.rs`         | 1327-1335 |
| `PartialOrd` / `Ord` impl                                            | `semiring.rs`         | 1338-1352 |
| `Hash` impl                                                          | `semiring.rs`         | 1355-1360 |
| `Default` impl                                                       | `semiring.rs`         | 1363-1367 |
| Tests (13 EntropyWeight)                                             | `semiring.rs`         | 2468-2637 |
| Forward-backward algorithm                                           | `forward_backward.rs` | 33-88     |
| Training convergence (loss computation)                              | `training.rs`         | 93-101    |
| Adaptive beam width integration point                                | `wfst.rs`             | 214-226   |
| Ambiguity detection (CountingWeight analog)                          | `prediction.rs`       | 1544-1577 |

---

## 15. Cross-References

- **Theory**: `prattail/docs/theory/wfst/semirings.md` -- semiring framework and axioms
- **Li & Eisner (2009)**: "First- and Second-Order Expectation Semirings with Applications to Minimum-Risk Training on Translation Forests" -- the foundational paper for the expectation semiring construction
- **Product semiring**: `product-weight.md` -- generic `ProductWeight<L, R>` composition framework
- **Tropical semiring**: `tropical-weight.md` -- the priority semiring used as the left component in `ProductWeight<TropicalWeight, EntropyWeight>`
- **Log semiring**: `log-weight.md` -- shares the log-sum-exp machinery; EntropyWeight extends LogWeight with an expectation component
- **Counting semiring**: `counting-weight.md` -- the cardinality-only alternative; entropy provides strictly more information
- **Context semiring**: `context-weight.md` -- the set-valued alternative; orthogonal to entropy (tracks which rules, not how uncertain)
- **Forward-backward**: `prattail/docs/theory/wfst/viterbi-and-forward-backward.md` -- the algorithm that computes entropy as a semiring accumulation
- **Beam pruning**: `prattail/docs/theory/wfst/cascade-suppression.md` -- the pruning mechanism that entropy would adaptively control
- **Lint layer**: `prattail/docs/design/lint-layer.md` -- the diagnostic framework that would emit entropy-based grammar feedback
