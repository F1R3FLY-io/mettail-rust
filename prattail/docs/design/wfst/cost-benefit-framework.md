# Cost-Benefit Meta-Optimization Framework

**Date:** 2026-03-01

---

## Table of Contents

1. [Problem Statement](#1-problem-statement)
2. [Formal Definition via Product Semiring](#2-formal-definition-via-product-semiring)
3. [GrammarProfile: Feature Extraction](#3-grammarprofile-feature-extraction)
4. [Decision Table](#4-decision-table)
5. [Pipeline Integration](#5-pipeline-integration)
6. [Worked Example: Calculator Grammar](#6-worked-example-calculator-grammar)
7. [Theoretical Properties](#7-theoretical-properties)
8. [Source Reference](#8-source-reference)

---

## 1. Problem Statement

PraTTaIL's compilation pipeline has accumulated 17+ optimization passes
over the course of development: left-factoring of shared prefixes,
hot/cold dispatch splitting, dead-code elimination, multi-token
lookahead, WFST minimization, spillover pruning, early termination, and
others.  Each optimization has a runtime benefit (speedup to generated
parser performance or reduction in generated code volume) and a
compile-time cost (analysis time, code complexity, and potential
interactions with other passes).

### The meta-optimization problem

Applying **all** optimizations unconditionally is suboptimal:

1. **Small grammars** (e.g., a 4-category calculator with ~20 rules)
   incur measurable compile overhead from passes whose benefit is
   negligible.  For instance, multi-token lookahead adds O(k * |A|)
   analysis cost per ambiguous token set A with lookahead depth k, but
   if there are zero ambiguous tokens, the entire pass is wasted.

2. **Interactions between passes** can be counterproductive.  Spillover
   pruning and early termination address opposite ends of the
   disambiguation spectrum (one for NFA-ambiguous categories, the other
   for deterministic ones).  Enabling both is never harmful, but the
   overhead of spillover pruning's beam-width checking is meaningless
   when no category requires NFA spillover buffers.

3. **The grammar author has no feedback** about which optimizations
   actually fired.  A grammar that happens to trigger zero applicable
   optimizations silently pays the analysis cost of evaluating all 10+
   candidates.

### Goals of the framework

The cost-benefit meta-optimization framework (designated **D1** in the
pipeline) addresses these issues:

- **Quantify** each optimization's benefit and cost as semiring weights.
- **Rank** candidates using the existing `ProductWeight` lexicographic
  ordering so that among equally beneficial optimizations, the cheaper
  one is preferred.
- **Report** recommendations to the grammar author via `eprintln` with
  info severity, following the same Rust-compiler-style output as the
  lint layer.
- **Remain advisory** -- the framework does not block compilation or
  silently alter behaviour.  It produces a ranked recommendation list
  that the pipeline (and future automation) can consult.

---

## 2. Formal Definition via Product Semiring

### Encoding optimization candidates as weights

Each optimization candidate is assigned a score in the product semiring:

```
Score = ProductWeight<TropicalWeight, TropicalWeight>
```

where:

- **Left component** (speedup): estimated runtime improvement.
  Tropical semiring semantics: lower value = greater benefit.
  A value of 0.0 represents maximum possible benefit; `+inf`
  represents no benefit at all (zero = additive identity = worst).

- **Right component** (compile cost): estimated compile-time overhead.
  Same tropical semantics: lower value = cheaper to apply.

### Why ProductWeight works here

`ProductWeight<TropicalWeight, TropicalWeight>` is already implemented
in `semiring.rs:492-620` with lexicographic `Ord` (`semiring.rs:586-594`):

```rust
impl<S1: Semiring + Ord, S2: Semiring + Ord> Ord for ProductWeight<S1, S2> {
    fn cmp(&self, other: &Self) -> Ordering {
        self.left.cmp(&other.left)
            .then_with(|| self.right.cmp(&other.right))
    }
}
```

This gives exactly the desired ordering:

1. **Primary**: prefer the optimization with the greatest speedup
   (lowest tropical weight in the left component).
2. **Tiebreaker**: among optimizations with equal speedup, prefer the
   one with the lowest compile cost (lowest tropical weight in the right
   component).

### Semiring interpretation

The product semiring's `plus` (component-wise min) and `times`
(component-wise addition) are not directly used by the framework --
D1 computes scores independently for each candidate and sorts them.
Only the `Ord` implementation matters.  This is analogous to how
`viterbi_generic()` in `lattice.rs` uses `Ord` for path comparison
while `plus` defines the algebraic structure.

### Diagram: Score space

```
compile cost (right component)
     ▲
     │
  1.0│    A1                       B3
     │    (0.40, 0.40)             (-ln(s), 0.15)
     │
  0.5│         B1
     │         (-ln(a), a_count*0.5)
     │
  0.1│  A2          B2        F1
     │  (-ln(c), 0.05)  (0.3, 0.1) (0.2, 0.01)
     │
  0.0└─────────────────────────────────────────▶ speedup (left)
     0.0   0.1   0.2   0.3   0.5   1.0    +inf
     ◂── better                     worse ──▸
```

Candidates in the lower-left corner are the best: high benefit, low
cost.  Candidates near `(+inf, *)` are inapplicable (no benefit).

---

## 3. GrammarProfile: Feature Extraction

The `GrammarProfile` struct captures quantitative properties of the
grammar after WFST construction.  It is computed once by
`build_grammar_profile()` and passed to `evaluate_optimizations()`.

### Fields

| Field                      | Type    | Source                                                    | Description                                                                                                                                                                                           |
|----------------------------|---------|-----------------------------------------------------------|-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
| `shared_prefix_ratio`      | `f64`   | `nfa_spillover_cats.len() / category_count`               | Fraction of categories requiring NFA spillover -- a proxy for prefix sharing potential. Higher ratio means more categories have multiple rules sharing dispatch tokens.                               |
| `cold_fraction`            | `f64`   | Actions with `weight.value() >= 1.0` / total actions      | Fraction of WFST dispatch actions that are "cold" (low priority / high tropical weight). High cold fraction indicates many dispatch arms that are rarely taken, making hot/cold splitting beneficial. |
| `ambiguous_fraction`       | `f64`   | Tokens with `predict().len() > 1` / total dispatch tokens | Fraction of dispatch tokens that resolve to multiple actions. Measures overall grammar ambiguity at the single-token lookahead level.                                                                 |
| `ambiguous_count`          | `usize` | Count of ambiguous tokens                                 | Absolute count of ambiguous dispatch tokens across all categories. Used to gate passes whose cost scales with ambiguity count (e.g., multi-token lookahead).                                          |
| `category_count`           | `usize` | `prediction_wfsts.len()`                                  | Number of grammar categories. Directly reflects grammar size.                                                                                                                                         |
| `rule_count`               | `usize` | `bundle.rule_infos.len()`                                 | Total number of rules across all categories.                                                                                                                                                          |
| `nfa_spillover_categories` | `usize` | `categories_needing_nfa_spillover()`                      | Number of categories with NFA-ambiguous prefix groups requiring thread-local spillover buffers and forced-prefix replay.                                                                              |
| `has_beam_width`           | `bool`  | `bundle.beam_width.is_enabled()`                          | Whether beam pruning is configured (via `BeamWidthConfig::Explicit` or auto).                                                                                                                         |
| `total_wfst_states`        | `usize` | `sum(wfst.states.len())`                                  | Total number of WFST states across all categories. Proxy for WFST complexity and minimization benefit.                                                                                                |

### Data flow

```
pipeline.rs:generate_parser_code()
  │
  ├── compute_first_sets()          ──→ first_sets: HashMap<String, FirstSet>
  ├── build_prediction_wfsts()      ──→ prediction_wfsts: HashMap<String, PredictionWfst>
  ├── categories_needing_nfa_spillover() ──→ nfa_spillover_categories: HashSet<String>
  │
  └── build_grammar_profile(        ◂── cost_benefit.rs:build_grammar_profile()
  │       &prediction_wfsts,
  │       &first_sets,
  │       &nfa_spillover_categories,
  │       rule_count,
  │       has_beam_width,
  │   ) ──→ GrammarProfile
  │
  └── evaluate_optimizations(&profile) ──→ Vec<OptimizationCandidate>
```

All inputs are computed by earlier pipeline stages.  `GrammarProfile`
construction adds no new analysis -- it merely aggregates existing data
into a flat struct for the decision engine.

### Source: `cost_benefit.rs:build_grammar_profile()`

```rust
pub fn build_grammar_profile(
    prediction_wfsts: &HashMap<String, PredictionWfst>,
    first_sets: &HashMap<String, FirstSet>,
    nfa_spillover_cats: &std::collections::HashSet<String>,
    rule_count: usize,
    has_beam_width: bool,
) -> GrammarProfile {
    let category_count = prediction_wfsts.len();

    // Count ambiguous dispatch tokens
    let mut total_dispatch_tokens = 0usize;
    let mut ambiguous_tokens = 0usize;
    for (cat, wfst) in prediction_wfsts {
        if let Some(first_set) = first_sets.get(cat) {
            for token in &first_set.tokens {
                total_dispatch_tokens += 1;
                if wfst.predict(token).len() > 1 {
                    ambiguous_tokens += 1;
                }
            }
        }
    }

    // Cold fraction: actions with weight >= 1.0
    let mut total_actions = 0usize;
    let mut cold_actions = 0usize;
    for wfst in prediction_wfsts.values() {
        for action in &wfst.actions {
            total_actions += 1;
            if action.weight.value() >= 1.0 {
                cold_actions += 1;
            }
        }
    }

    // ... ratios computed from counts ...
    GrammarProfile { shared_prefix_ratio, cold_fraction, ambiguous_fraction, ... }
}
```

### Design decisions

**Shared prefix ratio as NFA spillover proxy.** The true shared-prefix
ratio would require pairwise comparison of all rule prefixes within each
category.  Instead, the framework uses the NFA spillover count as a
proxy: a category requires NFA spillover if and only if it has multiple
rules sharing a dispatch token prefix, which is precisely the condition
that left-factoring addresses.  This avoids O(r^2) analysis where r is
the number of rules per category.

**Cold threshold at weight >= 1.0.** The tropical weight 1.0 corresponds
to `TropicalWeight::from_priority(9)` -- the second-lowest priority
level (only priority 10 maps to weight 0.0).  Actions at or above this
weight are taken only when no higher-priority alternative matches.
Separating these into a cold dispatch path reduces I-cache pressure on
the hot path.

---

## 4. Decision Table

The framework evaluates 10 optimization candidates.  Each has a speedup
formula, a compile cost formula, and an applicability predicate.

### Optimization roster

| ID | Optimization                  | Description                                                           |
|----|-------------------------------|-----------------------------------------------------------------------|
| A1 | `LeftFactoring`               | Grammar left-factoring via shared prefix extraction                   |
| A2 | `HotColdSplitting`            | Separate hot (low-weight) and cold (high-weight) dispatch arms        |
| A4 | `EnhancedDeadCodeElimination` | Full dispatch graph analysis to remove unreachable codegen            |
| A5 | `AmbiguityTargeting`          | CountingWeight-guided identification of ambiguous dispatch points     |
| B1 | `MultiTokenLookahead`         | Extended PredictionWfst with k-token lookahead for ambiguous tokens   |
| B2 | `AdaptiveRecovery`            | Runtime weight accumulation for error recovery cost tuning            |
| B3 | `WfstMinimization`            | State reduction on PredictionWfst via Hopcroft-style minimization     |
| F1 | `SpilloverPruning`            | Weight-based pruning of NFA spillover alternatives below beam width   |
| F2 | `EarlyTermination`            | Short-circuit dispatch on deterministic (single-prediction) token hit |
| F3 | `LazySpillover`               | Demand-driven replay of NFA alternatives (defer until needed)         |

### Scoring formulas

| Opt | Speedup (left)             | Cost (right)            | Apply When                                              |
|-----|----------------------------|-------------------------|---------------------------------------------------------|
| A1  | `-ln(shared_prefix_ratio)` | `category_count * 0.1`  | `shared_prefix_ratio > 0.3`                             |
| A2  | `-ln(cold_fraction)`       | `0.05` (fixed)          | `cold_fraction > 0.4`                                   |
| A4  | `0.5` (fixed)              | `0.2` (fixed)           | `rule_count > 5`                                        |
| A5  | `-ln(ambiguous_fraction)`  | `0.1` (fixed)           | `ambiguous_fraction > 0.1`                              |
| B1  | `-ln(ambiguous_fraction)`  | `ambiguous_count * 0.5` | `ambiguous_fraction > 0.1 AND ambiguous_count < 10`     |
| B2  | `0.3` (fixed)              | `0.1` (fixed)           | always                                                  |
| B3  | `-ln(total_wfst_states)`   | `0.15` (fixed)          | `total_wfst_states > 20`                                |
| F1  | `0.2` (fixed)              | `0.01` (fixed)          | `has_beam_width AND nfa_spillover_categories > 0`       |
| F2  | `0.1` (fixed)              | `0.01` (fixed)          | `nfa_spillover_categories == 0 AND ambiguous_count > 0` |
| F3  | `0.3` (fixed)              | `0.3` (fixed)           | `nfa_spillover_categories > 0`                          |

### Interpretation of `-ln(x)` speedup

For grammar-dependent optimizations (A1, A2, A5, B1, B3), the speedup
is modeled as `-ln(x)` where `x` is the relevant profile ratio or count:

```
  x close to 0  =>  -ln(x) -> +inf  =>  poor speedup (no benefit)
  x close to 1  =>  -ln(x) -> 0.0   =>  excellent speedup (maximum benefit)
```

This mapping is natural for tropical semiring semantics: lower weight =
better.  As the relevant grammar property (shared prefixes, cold arms,
ambiguity) increases toward 1.0, the optimization becomes more
beneficial and its speedup weight decreases toward 0.0.

Special case: when `x == 0.0` (e.g., zero ambiguity), the speedup is
set to `f64::INFINITY` (tropical zero), meaning the optimization is
completely inapplicable.  This aligns with the applicability predicate
which also returns `false` in such cases.

### Applicability predicates: rationale

| Predicate                        | Rationale                                                                                                                          |
|----------------------------------|------------------------------------------------------------------------------------------------------------------------------------|
| `shared_prefix_ratio > 0.3`      | Below 30% NFA spillover, left-factoring saves negligible dispatch work                                                             |
| `cold_fraction > 0.4`            | Below 40% cold arms, hot/cold splitting adds a branch with no measurable I-cache benefit                                           |
| `rule_count > 5`                 | Trivial grammars cannot have meaningful dead code                                                                                  |
| `ambiguous_fraction > 0.1`       | Below 10% ambiguity, lookahead overhead exceeds disambiguation benefit                                                             |
| `ambiguous_count < 10`           | With 10+ ambiguous tokens, lookahead cost grows linearly and may dominate                                                          |
| always (B2)                      | Adaptive recovery has zero overhead on the happy path (separate `_recovering` functions)                                           |
| `total_wfst_states > 20`         | Below 20 states, WFST minimization's Hopcroft pass is more expensive than the potential state reduction                            |
| `beam AND spillover > 0`         | Pruning requires both beam width configuration and spillover to exist                                                              |
| `no spillover AND ambiguity > 0` | Early termination is only meaningful when all dispatch is deterministic (no NFA) but some tokens are ambiguous at the weight level |
| `spillover > 0`                  | Lazy spillover defers NFA replay; without spillover, there is nothing to defer                                                     |

---

## 5. Pipeline Integration

### Position in the pipeline

The D1 cost-benefit analysis runs immediately after the lint layer and
before parser codegen:

```
generate_parser_code()
  1. FIRST/FOLLOW set computation
  2. Cross-category overlap analysis
  3. Build prediction WFSTs + beam width
  4. Build recovery WFSTs
  5. lint::run_lints(&ctx)                ◂── unified lint layer
  6. cost_benefit::build_grammar_profile() ◂── D1 profiling
     cost_benefit::recommended_optimizations()
  7. Write parser helpers
  8. Trampolined parsers per category
  9. Dispatch wrappers + recovery
 10. Concatenate + parse into TokenStream
```

### Integration code: `pipeline.rs` (lines 963-991)

```rust
// ── D1: Cost-benefit optimization analysis ─────────────────────────
// Profile the grammar and evaluate which optimizations are beneficial.
// Results are logged for diagnostics; the pipeline consults this data
// when deciding which compile-time passes to enable.
{
    let grammar_profile = crate::cost_benefit::build_grammar_profile(
        &prediction_wfsts,
        &first_sets,
        &nfa_spillover_categories,
        bundle.rule_infos.len(),
        bundle.beam_width.is_enabled(),
    );
    let recommended = crate::cost_benefit::recommended_optimizations(&grammar_profile);
    if !recommended.is_empty() {
        eprintln!(
            "  \x1b[36minfo\x1b[0m: D1 cost-benefit analysis recommends {} optimization(s):",
            recommended.len()
        );
        for candidate in &recommended {
            eprintln!(
                "         {} (speedup={:.2}, cost={:.2}): {}",
                candidate.optimization,
                candidate.speedup.value(),
                candidate.compile_cost.value(),
                candidate.reason
            );
        }
    }
}
```

### Output format

The output follows the Rust-compiler-style convention established by
the lint layer, using ANSI cyan for "info" severity:

```
  info: D1 cost-benefit analysis recommends 3 optimization(s):
         A4:EnhancedDCE (speedup=0.50, cost=0.20): rule_count=20 (threshold: >5)
         B2:AdaptiveRecovery (speedup=0.30, cost=0.10): always applicable (zero happy-path overhead)
         F2:EarlyTermination (speedup=0.10, cost=0.01): nfa_spillover_categories=0, ambiguous_count=3
```

### Advisory, not blocking

The framework does **not** gate compilation on its results.  All
optimizations that are structurally present in the pipeline continue
to run regardless of D1's recommendations.  The output serves two
purposes:

1. **Grammar author feedback**: highlights which optimizations are
   relevant for the current grammar, guiding manual tuning decisions.

2. **Environment-variable override**: the `PRATTAIL_AUTO_OPTIMIZE`
   environment variable lets users selectively enable or disable
   optimization passes, overriding the cost-benefit recommendations.

   **Supported values:**
   - `PRATTAIL_AUTO_OPTIMIZE=all` — enable every optimization gate.
   - `PRATTAIL_AUTO_OPTIMIZE=none` — disable every optimization gate.
   - `PRATTAIL_AUTO_OPTIMIZE=A1,B2,F3` — enable only the listed passes
     (comma-separated; accepts short codes like `A1`, full names like
     `LeftFactoring`, or display format `A1:LeftFactoring`).

   When the variable is unset, the pipeline falls back to the D1
   cost-benefit recommendations as before.  When an override is active,
   a warning is emitted to stderr:

   ```
   warning[<grammar>]: PRATTAIL_AUTO_OPTIMIZE override active — 3 gate(s) enabled
   ```

   **Implementation:** `OptimizationGates::from_env_or_recommendations()`
   in `cost_benefit.rs`, called from the pipeline's Generate phase.

---

## 6. Worked Example: Calculator Grammar

### Grammar profile

A typical calculator grammar with 4 categories (`Expr`, `Int`, `Float`,
`Bool`), approximately 20 rules, and modest ambiguity:

```rust
GrammarProfile {
    shared_prefix_ratio: 0.0,      // no NFA spillover categories
    cold_fraction: 0.30,           // 30% of dispatch actions are cold
    ambiguous_fraction: 0.15,      // 15% of dispatch tokens are ambiguous
    ambiguous_count: 3,            // 3 specific ambiguous tokens
    category_count: 4,
    rule_count: 20,
    nfa_spillover_categories: 0,   // no prefix sharing
    has_beam_width: false,         // no beam pruning configured
    total_wfst_states: 12,         // small WFSTs
}
```

### Evaluation

Each optimization is scored against this profile:

| Opt | Speedup            | Cost             | Score (left, right) | Applicable? | Reason                                           |
|-----|--------------------|------------------|---------------------|-------------|--------------------------------------------------|
| A1  | `+inf` (ratio=0.0) | `4 * 0.1 = 0.4`  | `(+inf, 0.4)`       | No          | `shared_prefix_ratio=0.00 <= 0.3`                |
| A2  | `-ln(0.3) = 1.20`  | `0.05`           | `(1.20, 0.05)`      | No          | `cold_fraction=0.30 <= 0.4`                      |
| A4  | `0.50`             | `0.20`           | `(0.50, 0.20)`      | Yes         | `rule_count=20 > 5`                              |
| A5  | `-ln(0.15) = 1.90` | `0.10`           | `(1.90, 0.10)`      | Yes         | `ambiguous_fraction=0.15 > 0.1`                  |
| B1  | `-ln(0.15) = 1.90` | `3 * 0.5 = 1.50` | `(1.90, 1.50)`      | Yes         | `ambiguous_fraction=0.15 > 0.1 AND count=3 < 10` |
| B2  | `0.30`             | `0.10`           | `(0.30, 0.10)`      | Yes         | always applicable                                |
| B3  | `+inf` (states=12) | `0.15`           | `(+inf, 0.15)`      | No          | `total_wfst_states=12 <= 20`                     |
| F1  | `0.20`             | `0.01`           | `(0.20, 0.01)`      | No          | `has_beam_width=false`                           |
| F2  | `0.10`             | `0.01`           | `(0.10, 0.01)`      | Yes         | `nfa_spillover=0 AND ambiguous_count=3 > 0`      |
| F3  | `0.30`             | `0.30`           | `(0.30, 0.30)`      | No          | `nfa_spillover_categories=0`                     |

### Sorted recommendation list

After filtering to applicable candidates and sorting by
`ProductWeight` lexicographic ordering (lower is better):

| Rank | Optimization           | Score          | Reason                               |
|------|------------------------|----------------|--------------------------------------|
| 1    | F2:EarlyTermination    | `(0.10, 0.01)` | Best speedup, trivial cost           |
| 2    | B2:AdaptiveRecovery    | `(0.30, 0.10)` | Always-on, zero happy-path overhead  |
| 3    | A4:EnhancedDCE         | `(0.50, 0.20)` | Moderate benefit for 20-rule grammar |
| 4    | A5:AmbiguityTargeting  | `(1.90, 0.10)` | Modest benefit (low ambiguity)       |
| 5    | B1:MultiTokenLookahead | `(1.90, 1.50)` | Same speedup as A5, but 15x the cost |

### Analysis

- **F2 (Early Termination)** ranks first because `(0.10, 0.01)` is
  the smallest score in lexicographic order.  This makes sense: with
  zero NFA spillover and 3 ambiguous tokens, deterministic dispatch
  hits can short-circuit immediately, saving dispatch overhead on the
  85% of tokens that are unambiguous.

- **B1 (MultiTokenLookahead)** and **A5 (AmbiguityTargeting)** have
  identical speedup (`-ln(0.15) = 1.90`) but B1 costs 15x more
  (`1.50` vs `0.10`).  The lexicographic tiebreaker correctly prefers
  A5 (rank 4) over B1 (rank 5), demonstrating the value of the product
  semiring encoding over a single-metric comparison.

- **A1, A2, B3, F1, F3** are all inapplicable for this grammar.
  Their speedup weights are either `+inf` (indicating zero-denominator
  in the `-ln(x)` formula) or their predicates fail.  They appear in
  the full `evaluate_optimizations()` output with `applicable: false`
  but are excluded from `recommended_optimizations()`.

### Output to stderr

```
  info: D1 cost-benefit analysis recommends 5 optimization(s):
         F2:EarlyTermination (speedup=0.10, cost=0.01): nfa_spillover_categories=0, ambiguous_count=3
         B2:AdaptiveRecovery (speedup=0.30, cost=0.10): always applicable (zero happy-path overhead)
         A4:EnhancedDCE (speedup=0.50, cost=0.20): rule_count=20 (threshold: >5)
         A5:AmbiguityTargeting (speedup=1.90, cost=0.10): ambiguous_fraction=0.15 (threshold: >0.1)
         B1:MultiTokenLookahead (speedup=1.90, cost=1.50): ambiguous_fraction=0.15, ambiguous_count=3 (thresholds: >0.1, <10)
```

---

## 7. Theoretical Properties

### 7.1 Monotonicity

For optimizations with `-ln(x)` speedup, the score decreases
monotonically as the relevant profile metric `x` increases toward 1.0.
This means:

- As a grammar becomes **more** ambiguous, the ambiguity-related
  optimizations (A5, B1) become **more** beneficial (lower score).
- As a grammar becomes **less** ambiguous, these optimizations become
  **less** beneficial (higher score) and eventually fall below the
  applicability threshold.

This monotonicity ensures that the framework's recommendations track
smoothly with grammar complexity rather than exhibiting discontinuous
jumps.

### 7.2 Threshold alignment with the `-ln` function

The applicability thresholds are chosen to align with meaningful points
on the `-ln(x)` curve:

| Threshold | `-ln(threshold)`  | Interpretation                                               |
|-----------|-------------------|--------------------------------------------------------------|
| `x > 0.1` | `-ln(0.1) = 2.30` | High speedup weight -- only apply if analysis cost is low    |
| `x > 0.3` | `-ln(0.3) = 1.20` | Moderate speedup -- apply when prefix sharing is substantial |
| `x > 0.4` | `-ln(0.4) = 0.92` | Good speedup -- apply when nearly half of dispatch is cold   |

Optimizations with thresholds at `x > 0.1` produce large speedup
weights (~2.3), meaning they are ranked lower than fixed-speedup
optimizations like F2 (0.10) and B2 (0.30).  This is intentional:
grammar-dependent optimizations are inherently less certain in their
benefit than structural optimizations.

### 7.3 Completeness

Every grammar will receive at least two recommendations:

1. **B2 (AdaptiveRecovery)** is always applicable (predicate: `true`).
2. **A4 (EnhancedDCE)** is applicable for any grammar with more than
   5 rules (predicate: `rule_count > 5`).

For grammars with 5 or fewer rules, B2 is the sole recommendation.
This minimum floor ensures the framework always produces output,
making it clear that the analysis ran successfully even for trivial
grammars.

### 7.4 Soundness of the advisory model

Because the framework is purely advisory:

- **No false positives in codegen**: recommending an optimization that
  would not actually help does not affect the generated parser.  The
  worst case is unnecessary `eprintln` output.
- **No false negatives in correctness**: failing to recommend a
  beneficial optimization does not introduce bugs.  The generated
  parser is identical regardless of D1's output.

The advisory model can be upgraded to an automated model in the future
by gating pipeline passes on `applicable == true`, but this requires
validation that the scoring formulas are well-calibrated across a
corpus of grammars.

---

## 8. Source Reference

| Component                                  | Location                  |
|--------------------------------------------|---------------------------|
| `GrammarProfile` struct                    | `cost_benefit.rs:109-129` |
| `build_grammar_profile()`                  | `cost_benefit.rs:135-206` |
| `Optimization` enum (10 variants)          | `cost_benefit.rs:26-48`   |
| `OptimizationCandidate` struct             | `cost_benefit.rs:68-103`  |
| `evaluate_optimizations()`                 | `cost_benefit.rs:213-357` |
| `recommended_optimizations()`              | `cost_benefit.rs:360-365` |
| Pipeline integration block                 | `pipeline.rs:963-991`     |
| `ProductWeight` type + lexicographic `Ord` | `semiring.rs:492-594`     |
| `TropicalWeight` semiring                  | `semiring.rs:57-198`      |
| Unit tests (7 tests)                       | `cost_benefit.rs:372-508` |

### See also

- `semirings/product-weight.md` -- ProductWeight design and Viterbi integration
- `semirings/tropical-weight.md` -- TropicalWeight semiring definition
- `lint-layer.md` -- Unified lint layer (runs immediately before D1)
- `dead-rule-detection.md` -- Five-tier dead-rule analysis (used by A4:EnhancedDCE)
