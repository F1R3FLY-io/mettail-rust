# PR01-DCE: Probabilistic Dead Code Elimination

Advanced Automata Codegen Optimization — M7 Probabilistic → Dead Rules

## 1. Quick Start

**What it does**: Eliminates grammar rules with selectivity < 1% in trained
probabilistic analysis. These rules fire so rarely that removing them has
minimal impact on parse outcomes.

**When it activates**: When the `probabilistic` feature is enabled,
`ProbabilisticAnalysis.is_normalized == true`, and `low_selectivity_rules`
is non-empty.

**Feature gate**: `probabilistic`

**Optimization gate**: `probabilistic_dce` (env: `PRATTAIL_OPT_PROBABILISTIC_DCE`)

**Status**: `OptimizationStatus::Auto`

## 2. Intuition

After training on a corpus of 10,000 programs:

```
rule common_add:  Expr "+" Expr     selectivity: 0.45 (45%)
rule common_mul:  Expr "*" Expr     selectivity: 0.30 (30%)
rule rare_xor:    Expr "^^" Expr    selectivity: 0.008 (0.8%)
```

Rule `rare_xor` fires less than 1% of the time. In the generated parser,
it still generates match arms, participates in fixpoint iteration, and
consumes compilation resources. PR01-DCE marks it as effectively dead.

**Important**: This is a *statistical heuristic*, not a formal proof of
deadness. The rule could still fire on unusual inputs outside the training
corpus. The `is_normalized` guard ensures this optimization only activates
after real corpus training — default uniform weights produce no eliminations.

## 3. Algorithm

```
Input:  ProbabilisticAnalysis from Phase 7B
Output: Labels added to dead_rule_labels

if probabilistic_result.is_normalized:
    for label in probabilistic_result.low_selectivity_rules:
        dead_rule_labels.insert(label)
```

The selectivity threshold (ε = 0.01) is computed during
`analyze_from_bundle()` using the forward algorithm over the PA.

## 4. Safety

The `is_normalized` guard is critical: it prevents dead-rule elimination
when the PA has default uniform weights (no training data). With uniform
weights, `is_normalized = false` and `low_selectivity_rules` is empty.

Users who encounter issues with rare-input parsing can disable this
optimization via:
- Gate: `probabilistic_dce = false`
- Environment: `PRATTAIL_OPT_PROBABILISTIC_DCE=0`

See [codegen-soundness.md](../theory/optimization/codegen-soundness.md) §3.

## 5. Diagnostics

- **PR01** (low-selectivity-rule): Emitted when a rule has selectivity below
  the threshold. Fires independently of the codegen optimization.

## 6. Related

- [SYM01-DCE](SYM01-DCE.md) — Symbolic dead-rule elimination (exact)
- [PR01-WEIGHT](PR01-WEIGHT.md) — Probabilistic weight blending
- [Probabilistic Automata Design](../design/probabilistic-automata.md) — Full M7 module design
