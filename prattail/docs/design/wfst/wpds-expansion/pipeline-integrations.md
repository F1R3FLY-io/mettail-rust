# WPDS Pipeline Integrations

**Date:** 2026-03-07

## Overview

The WPDS layer expansion adds 5 pipeline integration points and 1 trampoline
integration, positioned after NFA spillover detection (step 5g) and before the
unified lint layer. These integrations consume the `WpdsAnalysis` struct and refine
prediction weights, confirm dead rules, reduce NFA spillover, and pre-size frame pools.

---

## Pipeline Sequence

```
  generate_parser_code()
  |
  +-- 5a. build_dispatch_action_tables()
  +-- 5b. build_prediction_wfsts()
  +-- 5c. TransducerCascade optimization
  +-- 5d. TokenIdMap::from_names()
  +-- 5e. build_recovery_wfsts()
  +-- 5f. detect_dead_rules() (five-tier)
  +-- 5g. NFA spillover detection
  |
  |  +============================================+
  |  |  WPDS Layer Expansion (steps 5h-5l)       |
  |  +============================================+
  |  |                                            |
  +-- | 5h. build_wpds() + analyze_wpds()         |
  |  |     -> WpdsAnalysis struct                 |
  |  |     P05: wall-clock timing                 |
  |  |                                            |
  +-- | 5i. INT-01: weight refinement             |
  |  |     wpds_refine_prediction_weights()       |
  |  |                                            |
  +-- | 5j. COMP-07: trie confirmation            |
  |  |     wpds_confirm_trie_dead_rules()         |
  |  |                                            |
  +-- | 5k. INT-02: dead-rule recording           |
  |  |     HashSet<String> for codegen            |
  |  |                                            |
  +-- | 5l. INT-03: NFA spillover reduction       |
  |  |     Remove WPDS-dead from spillover groups |
  |  +============================================+
  |
  +-- Lint layer (W13, D14, D15, P05, W14, W16, COMP-08)
  +-- 6. resolve_dispatch_winners()
  +-- 7-11. codegen
```

---

## INT-01: WPDS PredictionWfst Weight Refinement

### Purpose

For rules with equal WFST weights sharing a dispatch token, use WPDS poststar weights
as tiebreaker to improve dispatch ordering.

### Algorithm

```
wpds_refine_prediction_weights(prediction_wfsts, analysis):
  for (cat, wfst) in prediction_wfsts:
    wpds_weight := analysis.category_weights[cat]
    if wpds_weight is available:
      for action group sharing same dispatch token:
        if all actions have equal weight:
          rank by WPDS category weight (lower = better)
          offset := 0.001 per rank position
          adjust action weights: action.weight += offset * rank
```

### Effect

Breaks ties among same-token rules without changing the relative order of rules with
different WFST weights. The 0.001 offset is small enough to not affect inter-token
comparisons.

---

## COMP-07: WPDS x Trie Dead-Rule Confirmation

### Purpose

Cross-reference WPDS-unreachable rules with their presence in the PathMap decision tree.
Rules present in the trie but WPDS-unreachable are "phantom entries" -- they exist in the
dispatch data structure but can never be selected during parsing.

### Algorithm

```
wpds_confirm_trie_dead_rules(decision_trees, analysis):
  phantom_entries := []
  for unreachable in analysis.unreachable_rules:
    for (cat, tree) in decision_trees:
      if cat == unreachable.category:
        tree_labels := tree.rule_labels()
        if unreachable.rule_label in tree_labels:
          phantom_entries.push((unreachable.rule_label, cat))
  return phantom_entries
```

### Effect

Phantom entries are logged for INT-02 and can be used by codegen to skip generating
match arms for rules that are confirmed dead across both WFST and WPDS analysis layers.

---

## INT-02: Dead-Rule Recording for Codegen

### Purpose

Collect WPDS-confirmed phantom entries into a `HashSet<String>` for downstream codegen
suppression. The PathMap trie structure is immutable, but codegen can skip `Ambiguous`
candidates that are WPDS-unreachable.

### Implementation

```rust
let wpds_dead_rule_labels: HashSet<String> = wpds_phantom_entries
    .iter()
    .map(|(label, _)| label.clone())
    .collect();
```

---

## INT-03: NFA Spillover Reduction

### Purpose

Remove WPDS-unreachable rules from NFA spillover groups. If all ambiguous groups in a
category become singletons after removing dead rules, eliminate the category from
`nfa_spillover_categories` entirely.

### Algorithm

```
// In pipeline.rs after WPDS analysis:
dead_labels := { r.rule_label for r in analysis.unreachable_rules }
if dead_labels is not empty:
  nfa_spillover_categories.retain(|cat| {
    groups := group_rd_by_dispatch_token(rd_rules, cat)
    groups.any(|(token, rules)| {
      live_count := rules.filter(|r| r.label not in dead_labels).count()
      live_count > 1  // Still ambiguous after removing dead rules
    })
  })
```

### Effect

Categories where WPDS dead-rule removal eliminates all NFA ambiguity no longer need
spillover buffers, thread-local declarations, or save/restore codegen. This can
significantly reduce generated code size for grammars with many orphan categories.

---

## RT-01: Frame Pool Pre-Sizing

### Purpose

Use G34 depth bounds to pre-size the trampoline frame pool TLS with
`Vec::with_capacity(N)` instead of `Vec::new()`.

### Integration Point

In `trampoline.rs`, `TrampolineConfig` includes:

```rust
pub frame_pool_capacity: Option<usize>,
```

When `Some(n)`, the generated code initializes the TLS pool with capacity `n`:

```rust
// Generated code (with RT-01):
thread_local! {
    static FRAME_POOL_CAT: Cell<Vec<Frame_Cat>> =
        Cell::new(Vec::with_capacity(3));  // max_depth + 1
}

// Generated code (without RT-01):
thread_local! {
    static FRAME_POOL_CAT: Cell<Vec<Frame_Cat>> =
        Cell::new(Vec::new());
}
```

### Depth Computation

```
max_bounded_depth := max(db.max_depth.unwrap() for db in depth_bounds.values()
                         where db.max_depth.is_some())
frame_pool_capacity := max_bounded_depth + 1
```

---

## Data Flow Trace

```
WpdsAnalysis
     |
     +-- INT-01: category_weights -> prediction_wfsts (weight tiebreak)
     |
     +-- COMP-07: unreachable_rules x decision_trees -> phantom_entries
     |     |
     |     +-- INT-02: phantom_entries -> wpds_dead_rule_labels (HashSet)
     |
     +-- INT-03: unreachable_rules x nfa_spillover_categories -> reduced set
     |
     +-- RT-01: depth_bounds -> TrampolineConfig.frame_pool_capacity
     |
     +-- Lint layer:
          +-- W13: unreachable_rules -> diagnostics
          +-- D14: num_symbols, num_rules, call_graph, cycles, depth_bounds
          +-- D15: call_graph -> witness traces (sub-diagnostic of W13)
          +-- P05: wpds_elapsed -> timing diagnostic
          +-- W14: reachable_categories x nfa_spillover -> ambiguity status
          +-- W16: category_weights x prediction_wfsts -> inversion check
          +-- COMP-08: call_graph, cycles -> refactoring suggestions
```

## Cross-References

- [WPDS Analysis Layer](../wpds-analysis.md) -- Parent design document
- [Pipeline Integration](../../../architecture/wfst/pipeline-integration.md) -- Full pipeline data flow
- [Diagnostic Reference](../../../diagnostics/README.md) -- All lint diagnostics
