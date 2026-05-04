# W14: walker-fork-tight-margin

**Severity:** Note

**Category:** WFST (W)

**Stage 10c (2026-05-04) repurpose** — W14 was previously
`wpds-confirmed-ambiguity` (which depended on `nfa_spillover_categories`).
After Stage 10b excised the NFA spillover infrastructure from
`parse_preserving_vars`, the old W14 had no enforcement target. The ID is
retained but now lints a different concern: **Walker Fork lex-min margin
under-confidence.**

## What it detects

For each prediction-WFST entry where multiple actions match a single dispatch
token, W14 fires when the top-2 actions' primary-weight margin is below
`TIGHT_MARGIN_THRESHOLD` (= 0.1).

```text
margin = actions[1].weight - actions[0].weight   (where weights are sorted ascending; lower = better in tropical semiring)
```

When this margin is small, the Walker's runtime `WpdsState::AmbiguityFanout`
resolves the Fork via lex-min over `LexicographicWeight (primary, src_idx,
rule_idx)` (`prattail/src/wpds_walker.rs:44, 364`). Tight margins mean the
primary weight is no longer load-bearing — the lex-min winner is decided by
`src_idx`/`rule_idx` tiebreaks, which are codegen-ordering artifacts rather
than principled WFST weight assignments.

## Why it matters

Brittle Fork resolution. A small reordering of rule declarations in the
`language! { ... }` macro DSL can flip the Fork winner without any
intentional semantic change. Grammars with W14 emissions are sensitive to
codegen ordering — a fragile state for any production grammar.

## Symmetric to W04

| Lint | Threshold | What it means                                      |
|------|-----------|----------------------------------------------------|
| W04  | gap > 5.0 | Near-deterministic; one action dominates clearly   |
| W14  | gap < 0.1 | Under-confident; lex-min relies on tiebreaks       |

W04 and W14 cover both extremes of the prediction-WFST gap distribution.
A category whose dispatch token gaps span (0.1, 5.0) is in the "healthy"
zone — fork resolution is principled (driven by primary weight) without
being trivially singleton.

## How to fix

1. **Increase weight specificity.** Add per-rule weight hints in
   `weights { ... }` or revise `cost_benefit.rs::training_target` to bias
   toward the intended winner.
2. **Audit codegen ordering.** Verify the rule declared first in the DSL
   is the intended Fork winner — `src_idx` increments in declaration order.
   If the intended winner is declared second, consider reordering.
3. **Suppress at the call site.** If the ambiguity is genuine and
   intentional (e.g., user error message context), suppress W14 for the
   specific category.

## Example diagnostic

```text
Note [W14] walker-fork-tight-margin in MyLang at category `Expr`, token `Plus`:
  top-2 actions (`AddExpr` vs `ConcatExpr`) have primary-weight margin 0.050
  (Walker lex-min Fork resolution will be src_idx/rule_idx-dependent)
  hint: consider increasing weight specificity for one of the rules, or
        audit codegen ordering — current Fork resolution depends on rule_idx
        tiebreak rather than principled weight order
```

## See also

- [W04: weight-gap-anomaly](W04-weight-gap-anomaly.md) — symmetric (wide-gap)
- [W02: nfa-ambiguous-prefix](W02-nfa-ambiguous-prefix.md) — exact-tie variant
- [Walker Fork resolution architecture](../../design/wfst/wpds-analysis.md)
