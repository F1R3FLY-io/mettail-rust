# A5: CountingWeight-Guided Ambiguity Targeting

**Date:** 2026-03-01

---

## Table of Contents

1. [Problem Statement](#1-problem-statement)
2. [Mechanism](#2-mechanism)
3. [Data Structures](#3-data-structures)
4. [Analysis Function](#4-analysis-function)
5. [Pipeline Integration](#5-pipeline-integration)
6. [Worked Example](#6-worked-example)
7. [NFA Buffer Pre-sizing](#7-nfa-buffer-pre-sizing)
8. [Source References](#8-source-references)

---

## 1. Problem Statement

PraTTaIL's NFA disambiguation (Layer 2.5) resolves ambiguity when
multiple grammar rules within the same category share a dispatch token.
The parser tries all N alternatives, selects the best by WFST weight,
and spills the remaining N-1 into a thread-local buffer for
forced-prefix replay.  However, the current architecture treats
ambiguity as a **per-category** property: either a category has NFA
spillover or it does not.

This binary classification misses important per-token structure:

### Heterogeneous ambiguity within a category

Within a single category, dispatch tokens frequently have wildly
different ambiguity profiles.  Consider a `Proc` category with 8
dispatch tokens:

| Token       | Alternatives | Rules               |
|-------------|-------------|---------------------|
| `Ident`     | 3           | PInput, POutput, PVar |
| `KwNew`     | 2           | PNew, PNewChannel   |
| `LParen`    | 1           | PGroup              |
| `LBrace`    | 1           | PBlock              |
| `KwFor`     | 1           | PFor                |
| `KwMatch`   | 1           | PMatch              |
| `KwIf`      | 1           | PIf                 |
| `Star`      | 1           | PStar               |

Only 2 of the 8 tokens (25%) are ambiguous.  Yet the entire category
is flagged for NFA spillover because at least one token has multiple
alternatives.  The remaining 6 tokens pay zero runtime cost for
disambiguation -- they dispatch directly -- but the pipeline has no
per-token visibility into this distribution.

### Consequences of per-category-only analysis

1. **NFA spillover buffers are uniformly sized.**  The thread-local
   `NFA_PREFIX_SPILL_CAT` vector is allocated with a default capacity
   that does not reflect the actual maximum number of spilled
   alternatives.  A category where the worst-case token has 3
   alternatives (2 spilled) gets the same buffer as a category where
   the worst case is 6 alternatives (5 spilled).

2. **Multi-token lookahead (B1) candidates are not identified.**
   Tokens with high ambiguity (3+ alternatives) are prime candidates
   for multi-token lookahead, which can resolve ambiguity at compile
   time by inspecting the second or third token.  Without per-token
   analysis, the pipeline cannot distinguish tokens that would benefit
   from B1 from those that are already unambiguous.

3. **Composed dispatch table pre-computation lacks targeting.**
   Pre-computing dispatch tables is beneficial for highly ambiguous
   tokens but unnecessary overhead for unambiguous ones.  Per-token
   ambiguity data allows selective pre-computation.

### Goal

A5 provides **per-token ambiguity analysis** using `CountingWeight`
from the counting semiring.  For each dispatch token in every
category, it computes the exact number of alternatives, identifies
B1 multi-token lookahead candidates, and determines per-category
maximum ambiguity for NFA buffer pre-sizing.  The analysis is purely
diagnostic -- it does not alter codegen -- but produces structured
data that downstream optimizations (B1, F3) and grammar authors can
consume.

---

## 2. Mechanism

A5 operates at **compile time** within the pipeline, after WFST
construction and D1 cost-benefit analysis.  It uses the existing
`predict_with_confidence()` method on `PredictionWfst` to obtain
`CountingWeight`-annotated predictions for every dispatch token.

### CountingWeight as ambiguity metric

The counting semiring (N, +, x, 0, 1) counts distinct derivation
paths through the automaton.  `predict_with_confidence()` annotates
each action with a `CountingWeight` whose value equals the total
number of actions returned by `predict()` for that token:

```rust
pub fn predict_with_confidence(&self, token_name: &str)
    -> Vec<(&WeightedAction, CountingWeight)>
{
    let actions = self.predict(token_name);
    let count = CountingWeight::new(actions.len() as u64);
    actions.into_iter().map(|a| (a, count)).collect()
}
```

The `CountingWeight` value directly encodes the ambiguity level:

| Count | Interpretation |
|-------|----------------|
| 0     | Token not in FIRST set (unreachable) |
| 1     | Unambiguous -- single dispatch target |
| 2     | Binary ambiguity -- NFA try-two suffices |
| 3+    | High ambiguity -- B1 candidate |

### Three outputs

A5 produces three categories of output from a single pass over all
prediction WFSTs:

```
                    ┌────────────────────────────────┐
                    │  analyze_ambiguity_targets()   │
                    │                                │
                    │  Input:                        │
                    │    prediction_wfsts             │
                    │    first_sets                  │
                    │    ambiguity_threshold          │
                    └────────┬─────────┬──────┬──────┘
                             │         │      │
                   ┌─────────▼───┐  ┌──▼───┐  ▼
                   │  Per-token  │  │ B1   │  Per-category
                   │  ambiguity  │  │ cand │  max ambiguity
                   │  info       │  │ list │  for buffer
                   │             │  │      │  pre-sizing
                   └─────────────┘  └──────┘
```

1. **Per-token ambiguity info:** `TokenAmbiguityInfo` structs for
   every ambiguous dispatch token (count > 1), including the rule
   labels that compete for that token.

2. **B1 candidate identification:** Tokens with `alternative_count`
   exceeding the configurable `ambiguity_threshold` are flagged with
   `lookahead_candidate = true`.  These are the tokens where
   multi-token lookahead would provide the greatest disambiguation
   benefit.

3. **Per-category maximum ambiguity:** For each category with at
   least one ambiguous token, the maximum `CountingWeight` value
   observed across all tokens.  This determines the NFA spillover
   buffer pre-size (see Section 7).

### Deterministic iteration order

The analysis iterates over tokens via `first_set.sorted_tokens()`,
which returns tokens sorted alphabetically.  This ensures that:

- Diagnostic output is reproducible across runs.
- The `ambiguous_tokens` vector in the result has a deterministic
  ordering suitable for snapshot testing.
- The same token always appears at the same position in logs,
  regardless of `HashMap` iteration order.

---

## 3. Data Structures

### TokenAmbiguityInfo

Per-token ambiguity record for a single dispatch token within a single
category:

```rust
pub struct TokenAmbiguityInfo {
    /// Category this token belongs to (e.g., "Proc", "Int").
    pub category: String,

    /// Token variant name (e.g., "Ident", "LParen").
    pub token: String,

    /// Number of dispatch alternatives for this token.
    /// This is the CountingWeight value from predict_with_confidence().
    pub alternative_count: u64,

    /// Rule labels that match this token (e.g., ["PInput", "POutput"]).
    pub rule_labels: Vec<String>,

    /// Whether this token is a candidate for multi-token lookahead (B1).
    /// True when alternative_count > ambiguity_threshold.
    pub lookahead_candidate: bool,
}
```

The `alternative_count` field directly stores the `CountingWeight`
value.  Using `u64` rather than the semiring type itself avoids
coupling the diagnostic struct to the semiring module.  The
`rule_labels` field provides human-readable identification of the
competing rules, sourced from `WeightedAction::action.rule_label()`.

### AmbiguityTargetingResult

Aggregate result of A5 analysis across all categories:

```rust
pub struct AmbiguityTargetingResult {
    /// All ambiguous tokens across all categories.
    /// Each entry has alternative_count > 1.
    pub ambiguous_tokens: Vec<TokenAmbiguityInfo>,

    /// Total number of unambiguous tokens (alternative_count <= 1).
    pub unambiguous_count: usize,

    /// Maximum ambiguity count observed across all tokens in all categories.
    pub max_ambiguity: u64,

    /// Categories where NFA spillover buffer should be pre-sized.
    /// Each entry is (category_name, buffer_size) where
    /// buffer_size = max_ambiguity_in_category - 1.
    pub presized_categories: Vec<(String, usize)>,
}
```

The `presized_categories` field is derived from the per-category
maximum ambiguity map: for each category with ambiguity, the buffer
pre-size is `max - 1` because the primary result is returned directly
(not spilled).  See Section 7 for details.

### Relationship between structures

```
AmbiguityTargetingResult
  │
  ├── ambiguous_tokens: Vec<TokenAmbiguityInfo>
  │     │
  │     ├── [0] Proc::Ident  (count=3, [PInput, POutput, PVar], B1=true)
  │     ├── [1] Proc::KwNew  (count=2, [PNew, PNewChannel], B1=false)
  │     └── [2] Float::Ident (count=2, [FloatId, IntToFloat], B1=false)
  │
  ├── unambiguous_count: 14
  │
  ├── max_ambiguity: 3
  │
  └── presized_categories: [("Proc", 2), ("Float", 1)]
```

---

## 4. Analysis Function

### Signature

```rust
pub fn analyze_ambiguity_targets(
    prediction_wfsts: &HashMap<String, PredictionWfst>,
    first_sets: &HashMap<String, FirstSet>,
    ambiguity_threshold: u64,
) -> AmbiguityTargetingResult
```

### Parameters

| Parameter | Type | Description |
|---|---|---|
| `prediction_wfsts` | `&HashMap<String, PredictionWfst>` | One WFST per category, built by `build_prediction_wfsts()` |
| `first_sets` | `&HashMap<String, FirstSet>` | FIRST sets for each category, computed by `compute_first_sets()` |
| `ambiguity_threshold` | `u64` | Tokens with `alternative_count > threshold` are flagged as B1 candidates. Pipeline passes `1`, meaning any token with 2+ alternatives is a candidate. |

### Algorithm

```
FUNCTION analyze_ambiguity_targets(wfsts, first_sets, threshold):
    ambiguous_tokens  := []
    unambiguous_count := 0
    max_ambiguity     := 0
    cat_max_ambiguity := {}   // HashMap<String, usize>

    FOR (cat, wfst) IN wfsts:
        first_set := first_sets[cat]
        IF first_set IS NONE: CONTINUE
        cat_max := 0

        FOR token IN first_set.sorted_tokens():       // deterministic order
            predictions := wfst.predict_with_confidence(token)
            count := predictions[0].counting_weight.count()

            IF count > 1:
                rule_labels := predictions.map(|p| p.action.rule_label())
                is_b1       := count > threshold

                ambiguous_tokens.push(TokenAmbiguityInfo {
                    category: cat,
                    token: token,
                    alternative_count: count,
                    rule_labels: rule_labels,
                    lookahead_candidate: is_b1,
                })

                max_ambiguity := max(max_ambiguity, count)
                cat_max       := max(cat_max, count)
            ELSE:
                unambiguous_count += 1

        IF cat_max > 0:
            cat_max_ambiguity[cat] := cat_max

    // Derive pre-sizing from per-category maxima
    presized := cat_max_ambiguity
        .map(|(cat, max)| (cat, max - 1))   // N-1 alternatives spilled

    RETURN AmbiguityTargetingResult {
        ambiguous_tokens,
        unambiguous_count,
        max_ambiguity,
        presized_categories: presized,
    }
```

### Key implementation details

1. **`predict_with_confidence()` returns uniform `CountingWeight`.**
   Every action for a given token receives the same `CountingWeight`
   value (the total action count for that token).  The function reads
   the count from the first entry: `predictions.first().map_or(0, |(_, cw)| cw.count())`.

2. **`sorted_tokens()` ensures determinism.**  `FirstSet::sorted_tokens()`
   returns `Vec<&str>` sorted alphabetically via `sort_unstable()`.
   This guarantees reproducible iteration order despite `HashMap`
   non-determinism in the prediction WFST and first set maps.

3. **Threshold semantics.**  The `lookahead_candidate` flag is set
   when `count > ambiguity_threshold`, not `count >= ambiguity_threshold`.
   With the pipeline's default threshold of 1, a token with exactly 2
   alternatives is flagged (2 > 1).  A threshold of 2 would require 3+
   alternatives.

4. **`saturating_sub(1)` for pre-sizing.**  The buffer pre-size
   computation uses `max.saturating_sub(1)` to avoid underflow when
   `max == 0` (which cannot occur because entries only exist when
   `cat_max > 0`, but the saturating subtraction is defensive).

### Complexity

| Operation | Cost |
|-----------|------|
| Outer loop (categories) | O(C) where C = number of categories |
| Inner loop (tokens) | O(T_c) per category, T_c = tokens in FIRST set |
| `predict_with_confidence()` | O(A) per token, A = number of actions |
| `sorted_tokens()` | O(T_c log T_c) per category |
| Total | O(sum_c(T_c log T_c + T_c * A_max)) |

For typical grammars (4-10 categories, 5-20 tokens per category,
1-6 actions per token), the total cost is negligible relative to
WFST construction and codegen.

---

## 5. Pipeline Integration

### Position in the pipeline

A5 runs immediately after D1 cost-benefit analysis and before parser
codegen:

```
generate_parser_code()
  1. FIRST/FOLLOW set computation
  2. Cross-category overlap analysis
  3. Build prediction WFSTs + beam width
  4. Build recovery WFSTs
  5. lint::run_lints(&ctx)                     <-- unified lint layer
  6. cost_benefit::build_grammar_profile()     <-- D1 profiling
     cost_benefit::recommended_optimizations()
  7. cost_benefit::analyze_ambiguity_targets() <-- A5 analysis
  8. Write parser helpers
  9. Trampolined parsers per category
 10. Dispatch wrappers + recovery
 11. Concatenate + parse into TokenStream
```

### Integration code: `pipeline.rs` (lines 1121-1159)

```rust
// -- A5: Ambiguity targeting analysis ----------------------------------------
// Identify per-token ambiguity for downstream optimizations (B1, buffer
// pre-sizing). The threshold=1 means any token with >1 alternative is
// flagged as a candidate for multi-token lookahead.
{
    let ambiguity_result = crate::cost_benefit::analyze_ambiguity_targets(
        &prediction_wfsts,
        &first_sets,
        1, // threshold: flag tokens with >1 alternative
    );
    if !ambiguity_result.ambiguous_tokens.is_empty() {
        eprintln!(
            "  \x1b[36minfo\x1b[0m: A5 ambiguity targeting: \
             {} ambiguous token(s), {} unambiguous, max ambiguity={}",
            ambiguity_result.ambiguous_tokens.len(),
            ambiguity_result.unambiguous_count,
            ambiguity_result.max_ambiguity
        );
        for info in &ambiguity_result.ambiguous_tokens {
            eprintln!(
                "         {}::{} -- {} alternative(s): [{}]{}",
                info.category,
                info.token,
                info.alternative_count,
                info.rule_labels.join(", "),
                if info.lookahead_candidate { " <-- B1 candidate" } else { "" }
            );
        }
        if !ambiguity_result.presized_categories.is_empty() {
            eprintln!(
                "         NFA spillover pre-sizing: {}",
                ambiguity_result.presized_categories
                    .iter()
                    .map(|(cat, sz)| format!("{}={}", cat, sz))
                    .collect::<Vec<_>>()
                    .join(", ")
            );
        }
    }
}
```

### Output format

The output follows the Rust-compiler-style convention established by
the lint layer, using ANSI cyan for "info" severity:

```
  info: A5 ambiguity targeting: 3 ambiguous token(s), 14 unambiguous, max ambiguity=3
         Proc::Ident -- 3 alternative(s): [PInput, POutput, PVar] <-- B1 candidate
         Proc::KwNew -- 2 alternative(s): [PNew, PNewChannel]
         Float::Ident -- 2 alternative(s): [FloatId, IntToFloat]
         NFA spillover pre-sizing: Proc=2, Float=1
```

### Downstream consumers

| Consumer | What it reads | Purpose |
|----------|---------------|---------|
| B1 (multi-token lookahead) | `ambiguous_tokens` with `lookahead_candidate == true` | Identifies which tokens need extended WFSTs with k-token lookahead depth |
| F3 (lazy spillover) | `presized_categories` | Pre-sizes demand-driven replay buffers to avoid reallocation |
| Grammar author | Diagnostic output | Identifies which tokens cause dispatch ambiguity and which rules compete |
| D1 (cost-benefit) | `ambiguous_fraction`, `ambiguous_count` (from `GrammarProfile`) | Evaluates whether A5 and B1 are applicable (A5 feeds D1 indirectly via shared profile data) |

### Advisory, not blocking

Like D1, A5 is purely advisory.  It does not gate compilation, alter
codegen, or suppress any downstream pass.  The `AmbiguityTargetingResult`
is consumed only by diagnostic output (today) and can be threaded to
future optimization passes (B1, F3) when they are implemented.

---

## 6. Worked Example

### Grammar

Consider a simplified rhocalc-like grammar with a `Proc` category and
an `Int` category:

```
category Proc {
    rule PInput  { Ident "!" "(" Proc ")" }
    rule POutput { Ident "!" "(" Proc ")" }
    rule PSend   { "(" Proc ")" }
    rule PVar    { Ident }
}

category Int {
    rule IntLit  { Integer }
    rule IntAdd  { Int "+" Int }
}
```

### FIRST sets

```
FIRST(Proc) = { Ident, LParen }
FIRST(Int)  = { Integer }
```

### Prediction WFST queries

```
Proc.predict_with_confidence("Ident"):
  [(&PInput,  CountingWeight(3)),
   (&POutput, CountingWeight(3)),
   (&PVar,    CountingWeight(3))]

Proc.predict_with_confidence("LParen"):
  [(&PSend,   CountingWeight(1))]

Int.predict_with_confidence("Integer"):
  [(&IntLit,  CountingWeight(1))]
```

### Analysis (threshold = 1)

Iterating over all categories and tokens in sorted order:

| Category | Token     | Count | > 1? | > threshold? | Action |
|----------|-----------|-------|------|--------------|--------|
| Int      | Integer   | 1     | No   | --           | unambiguous_count++ |
| Proc     | Ident     | 3     | Yes  | Yes (3 > 1)  | Push TokenAmbiguityInfo, flag B1 |
| Proc     | LParen    | 1     | No   | --           | unambiguous_count++ |

### Result

```rust
AmbiguityTargetingResult {
    ambiguous_tokens: [
        TokenAmbiguityInfo {
            category: "Proc",
            token: "Ident",
            alternative_count: 3,
            rule_labels: ["PInput", "POutput", "PVar"],
            lookahead_candidate: true,   // 3 > 1
        },
    ],
    unambiguous_count: 2,    // Integer, LParen
    max_ambiguity: 3,
    presized_categories: [("Proc", 2)],   // 3-1 = 2 spilled
}
```

### Diagnostic output

```
  info: A5 ambiguity targeting: 1 ambiguous token(s), 2 unambiguous, max ambiguity=3
         Proc::Ident -- 3 alternative(s): [PInput, POutput, PVar] <-- B1 candidate
         NFA spillover pre-sizing: Proc=2
```

### Interpretation

- **Proc::Ident** is the only ambiguous dispatch point.  Three rules
  (PInput, POutput, PVar) all begin with an `Ident` token.  The NFA
  try-all loop must evaluate all three, and the 2 non-primary results
  are spilled for forced-prefix replay.

- **B1 candidate:** Because `Ident` has 3 alternatives (exceeding
  the threshold of 1), it is flagged for multi-token lookahead.
  Inspecting the second token after `Ident` would reveal:
  - `!` following `Ident` implies PInput or POutput (further
    disambiguation needed at the third token or semantically).
  - Any non-`!` token implies PVar (variable capture).
  This is exactly the kind of token where B1 can resolve ambiguity
  at compile time rather than relying on NFA replay.

- **Proc::LParen** and **Int::Integer** are unambiguous (single
  dispatch target each).  They incur zero disambiguation overhead
  and need no further optimization.

- **Pre-sizing:** The Proc category's NFA spillover buffer should be
  pre-allocated with capacity 2 (the maximum number of spilled
  alternatives for any token in that category).

---

## 7. NFA Buffer Pre-sizing

### Problem

The NFA spillover buffer `NFA_PREFIX_SPILL_CAT` is a thread-local
`Cell<Vec<(Cat, usize, f64)>>` that holds spilled alternatives during
forced-prefix replay.  Without pre-sizing, the `Vec` starts empty
and grows dynamically as alternatives are spilled, incurring
reallocation on the first ambiguous parse of each category.

### Pre-size formula

For each category with ambiguous tokens, the maximum number of spilled
alternatives is:

```
buffer_size = max_ambiguity_in_category - 1
```

The `-1` accounts for the primary result, which is returned directly
from the NFA try-all phase and never enters the spillover buffer.

### Derivation

Let A(t) denote the `CountingWeight` (alternative count) for token t
in category C.  The NFA try-all loop evaluates all A(t) alternatives
for the dispatched token, selects the best (index 0), and spills the
remaining A(t) - 1 into the buffer.  The worst-case buffer usage
across all tokens in C is:

```
max_spill(C) = max{A(t) - 1 | t in FIRST(C), A(t) > 1}
             = max{A(t) | t in FIRST(C)} - 1
             = max_ambiguity(C) - 1
```

### Example

From Section 6:

| Category | Token   | A(t) | Spilled |
|----------|---------|------|---------|
| Proc     | Ident   | 3    | 2       |
| Proc     | LParen  | 1    | 0       |

`max_spill(Proc) = max(2, 0) = 2`.

The `presized_categories` output: `[("Proc", 2)]`.

### Generated code (future)

Pre-sizing would modify the thread-local initialization in generated
code from:

```rust
thread_local! {
    static NFA_PREFIX_SPILL_PROC: Cell<Vec<(Proc, usize, f64)>> =
        Cell::new(Vec::new());
}
```

to:

```rust
thread_local! {
    static NFA_PREFIX_SPILL_PROC: Cell<Vec<(Proc, usize, f64)>> =
        Cell::new(Vec::with_capacity(2));
}
```

This eliminates the first reallocation on the happy path for ambiguous
tokens.  The pre-size is a compile-time constant derived from A5's
analysis, so there is no runtime overhead.

### Edge cases

| Case | Pre-size | Rationale |
|------|----------|-----------|
| No ambiguous tokens in category | Not in `presized_categories` | No spillover occurs; default `Vec::new()` is optimal |
| All tokens have A(t) = 2 | 1 | Single spilled alternative; capacity 1 avoids one reallocation |
| One token has A(t) = 10 | 9 | Worst-case token dominates; 9 spilled alternatives |
| Category not in `first_sets` | Skipped | Category has no dispatch tokens; cannot have ambiguity |

---

## 8. Source References

| Component | Location | Description |
|---|---|---|
| `TokenAmbiguityInfo` struct | `cost_benefit.rs:378-392` | Per-token ambiguity record |
| `AmbiguityTargetingResult` struct | `cost_benefit.rs:394-405` | Aggregate analysis result |
| `analyze_ambiguity_targets()` | `cost_benefit.rs:416-478` | A5 analysis function |
| `predict_with_confidence()` | `wfst.rs:169-173` | CountingWeight-annotated WFST query |
| `CountingWeight` semiring | `semiring.rs:204-281` | Counting semiring (N, +, x, 0, 1) |
| `FirstSet::sorted_tokens()` | `prediction.rs:66-70` | Deterministic token iteration |
| Pipeline integration (A5 block) | `pipeline.rs:1121-1159` | Diagnostic output and analysis invocation |
| D1 integration (GrammarProfile) | `cost_benefit.rs:109-206` | Profile extraction feeding A5 scoring |
| Unit test: empty input | `cost_benefit.rs:606-614` | Verifies empty WFST/first-set handling |
| Unit test: structured result | `cost_benefit.rs:616-682` | Verifies per-token analysis with PredictionWfstBuilder |

### See also

- `cost-benefit-framework.md` -- D1 meta-optimization framework (A5 scoring)
- `spillover-pruning.md` -- F1 weight-based spillover pruning (consumes buffer pre-sizing)
- `early-termination.md` -- F2 deterministic-hit short-circuit (complementary to A5)
- `nfa-disambiguation.md` -- NFA try-all architecture (disambiguation that A5 analyzes)
- `semirings/counting-weight.md` -- CountingWeight semiring definition and properties
