# Context-Sensitive Analysis (G36, CS-01, CS-04, CS-05)

**Date:** 2026-03-07

## Overview

G36 computes calling contexts per category. CS-01 builds context-sensitive rule
tables. CS-04 analyzes cross-category binding power modulation. CS-05 determines
per-category context ambiguity status. Together they provide the structural
framework for context-aware dispatch optimizations.

---

## G36: Calling Context Analysis

### Data Structure

```rust
pub struct CallingContext {
    pub caller_category: String,   // Who calls this category
    pub caller_rule: String,       // Which rule contains the call
    pub caller_position: u32,      // Position within the rule (0=prefix)
    pub weight: f64,               // 0.0 if zero-weight, 1.0 otherwise
}
```

### Algorithm: `compute_calling_contexts()`

```
compute_calling_contexts(wpds):
  contexts := {}
  for rule in wpds.rules:
    if rule is Push { from_gamma, to_gamma_top, weight, .. }:
      callee := to_gamma_top.category
      contexts[callee].push(CallingContext {
        caller_category: from_gamma.category,
        caller_rule: from_gamma.rule_label,
        caller_position: from_gamma.position,
        weight: if weight.is_zero() then 0.0 else 1.0
      })
  return contexts
```

### Semantics

Each entry answers: "Category X is called from category Y, in rule Z, at position P."
This is the WPDS-precise version of "who calls me" -- it respects the Push-rule
structure and includes weight information.

---

## CS-01: Context-Sensitive Rule Tables

### Data Structures

```rust
pub struct ContextEntry {
    pub context_tag: String,       // Caller category name or "top-level"
    pub valid_rules: Vec<String>,  // Rule labels valid in this context
}

pub struct ContextRuleTable {
    pub category: String,
    pub entries: Vec<ContextEntry>,
    pub is_nontrivial: bool,       // Some context has fewer rules than total
    pub singleton_contexts: usize, // Contexts with exactly 1 valid rule
}
```

### Algorithm: `build_context_rule_tables()`

```
build_context_rule_tables(calling_contexts, reachable, all_rules):
  tables := {}
  rules_by_cat := group all_rules by category

  for (cat, contexts) in calling_contexts:
    if cat not in reachable or contexts is empty: continue
    all_rules_for_cat := rules_by_cat[cat]

    // Group contexts by caller category
    contexts_by_caller := group contexts by caller_category

    entries := []
    for (caller_cat, caller_contexts) in contexts_by_caller:
      valid := all_rules_for_cat  // Full filtering requires per-rule poststar
      if |valid| < |all_rules_for_cat|: is_nontrivial = true
      if |valid| == 1: singleton_count += 1
      entries.push(ContextEntry { caller_cat, valid })

    // Add "top-level" entry for primary category
    entries.push(ContextEntry { "top-level", all_rules_for_cat })

    tables[cat] := ContextRuleTable { cat, entries, is_nontrivial, singletons }
```

### Current Status

The current implementation records the structural framework but does not yet perform
per-rule-per-context poststar reachability filtering. All rules are currently valid in
all contexts. Full context-sensitive filtering is deferred to a future sprint that adds
per-rule poststar queries.

---

## CS-04: Cross-Category BP Modulation

### Purpose

Record per-call-site binding power hints from WPDS Push rules. Different callers may
invoke the same category at different binding power levels:

- **Position 0** (prefix context): `min_bp` typically 0
- **Position > 0** (infix/continuation): `min_bp` may be > 0

### Algorithm: `analyze_cross_category_bp()`

```
analyze_cross_category_bp(wpds):
  bp_map := {}
  for Push rule in wpds.rules:
    caller := from_gamma.category
    callee := to_gamma_top.category
    if caller != callee:
      bp_hint := if from_gamma.position == 0 then 0 else 1
      bp_map[(caller, callee)].push(bp_hint)

  // Deduplicate per edge
  for values in bp_map.values_mut():
    sort and dedup values
  return bp_map
```

### Worked Example

Grammar: `Expr -> "(" Type ")" Expr | Type Expr`

Call edges from Expr to Type:
- Cast rule at position 0 -> `bp_hint = 0` (prefix)
- Annotation rule at position 1 -> `bp_hint = 1` (non-prefix)

Result: `cross_category_bp[("Expr", "Type")] = [0, 1]`

When CS-04 detects multiple BP hints for the same edge, downstream codegen can thread
the caller-specific BP through cross-category dispatch instead of hardcoding 0.

---

## CS-05: Context-Aware Ambiguity Resolution

### Purpose

Determine whether a category is "context-unambiguous" -- called from at most one unique
category. For such categories, NFA try-all can commit to the first success without
save/restore, because there is no stack-context-dependent ambiguity.

### Algorithm: `analyze_context_ambiguity()`

```
analyze_context_ambiguity(calling_contexts, reachable_categories):
  result := {}
  for cat in reachable_categories:
    unique_callers := |{ ctx.caller_category for ctx in calling_contexts[cat] }|
    result[cat] := (unique_callers <= 1)
  return result
```

### Interpretation

| `unique_callers` | `is_unambiguous` | Meaning |
|---|---|---|
| 0 | true | Top-level only (primary category or orphan) |
| 1 | true | Called from exactly one category -- deterministic context |
| >= 2 | false | Multiple callers -- stack context affects dispatch |

### Current Status

CS-05 provides structural information. Actual NFA dispatch optimization based on
context unambiguity is deferred to a future sprint.

## Cross-References

- [Call Graph Analysis](call-graph-analysis.md) -- G33 provides the call edges consumed by G36
- [Pipeline Integrations](pipeline-integrations.md) -- INT-03 uses CS-05 for spillover reduction
- [WPDS Analysis Layer](../wpds-analysis.md) -- Parent design document
