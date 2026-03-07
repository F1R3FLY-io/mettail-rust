# D05: decision-tree-summary

**Date:** 2026-03-06
**Updated:** 2026-03-06
**Severity:** Note
**Category:** Decision Tree

## 1 Description

Emits a per-category summary of the decision tree's structural metrics during
pipeline construction. D05 provides a compact view of trie complexity: total
states, deterministic vs. ambiguous node counts, maximum depth, minimum
lookahead, nonterminal boundary count, shared-prefix savings, and the ratio of
deterministic rules to total rules.

This diagnostic is **informational** (Note severity, emitted at Info level in the
pipeline). It requires no action from the grammar author but serves as a quick
health check: a high `ambiguous_nodes` count or a large `min_lookahead` value
signals that the grammar may benefit from restructuring.

## 2 Trigger Conditions

A D05 diagnostic is emitted when **all** of the following hold:

1. `DecisionTreeBuilder::build_all()` has been called for the grammar.
2. The category has a non-empty decision tree (`tree.stats.total_states > 0`).
3. The pipeline iterates over `category_names` and calls `complexity_metrics()`
   (or directly formats `tree.stats`) for each qualifying category.

One D05 diagnostic is emitted per category that has at least one trie entry.

## 3 TreeStats Fields

The `TreeStats` struct (defined in `prattail/src/decision_tree.rs`) carries the
following fields:

```
┌──────────────────────────────────────────────────────────────────┐
│ TreeStats                                                        │
│ ──────────────────────────────────────────────────────────────── │
│ total_states          usize   All trie nodes with values         │
│ deterministic_nodes   usize   Commit-action nodes (single rule)  │
│ ambiguous_nodes       usize   Ambiguous-action nodes (2+ rules)  │
│ max_depth             usize   Longest path from root to leaf     │
│ min_lookahead         usize   Min tokens for deterministic       │
│                               dispatch (1 if no ambiguity)       │
│ nonterminal_boundaries usize  NT boundary nodes in the trie      │
│ shared_prefix_savings usize   States saved by prefix sharing     │
│ total_rules           usize   Distinct rule labels in the trie   │
│ deterministic_rules   usize   Rules reachable only via Commit    │
└──────────────────────────────────────────────────────────────────┘
```

### 3.1 Field Semantics

- **total_states** -- Each `(path, action)` pair in the trie counts as one
  state. This is the sum of `deterministic_nodes`, `ambiguous_nodes`, and
  `nonterminal_boundaries`.

- **deterministic_nodes** -- Nodes where `DecisionAction::Commit` is stored: a
  single rule is committed without backtracking.

- **ambiguous_nodes** -- Nodes where `DecisionAction::Ambiguous` is stored: two
  or more rules share the prefix, requiring NFA try-all at runtime.

- **max_depth** -- The maximum `path.len()` across all entries. Correlates with
  the longest shared terminal prefix chain.

- **min_lookahead** -- If `ambiguous_nodes == 0`, this is `1` (the grammar is
  LL(1) w.r.t. the trie). Otherwise, it equals `max_depth` (worst-case tokens
  needed to resolve all dispatch).

- **nonterminal_boundaries** -- Count of `DecisionAction::NonterminalBoundary`
  nodes, where the trie splits into continuation segments after a nonterminal
  parse.

- **shared_prefix_savings** -- `total_states - total_rules` when
  `total_states > total_rules` (more entries than unique rules means prefix
  sharing reduced the entry count). Otherwise `0`.

- **total_rules** -- Number of unique `rule_label` strings appearing in any
  action across all segments.

- **deterministic_rules** -- Number of unique `rule_label` strings appearing
  exclusively in `Commit` actions (never in an `Ambiguous` group).

## 4 Output Format

### 4.1 Display Implementation

The `TreeStats` type implements `fmt::Display`:

```
{total_states} states ({deterministic_nodes} deterministic, {ambiguous_nodes} ambiguous), \
max depth {max_depth}, min lookahead {min_lookahead}, \
{nonterminal_boundaries} NT boundaries, {shared_prefix_savings} shared-prefix savings, \
{deterministic_rules}/{total_rules} rules deterministic
```

### 4.2 Pipeline Message

The pipeline prepends the category name:

```
info[D05] (GrammarName): CatName: <TreeStats Display output>
```

### 4.3 Example: Fully Deterministic Grammar

A simple calculator with two categories (`Int`, `Float`), each having distinct
leading terminals:

```
info[D05] (Calc): Int: 5 states (5 deterministic, 0 ambiguous), max depth 3, \
min lookahead 1, 0 NT boundaries, 3 shared-prefix savings, 5/5 rules deterministic
```

Interpretation:
- 5 trie entries, all `Commit` -- every prefix rule dispatches deterministically.
- `min_lookahead = 1` -- a single token peek resolves all dispatch (LL(1)).
- 3 shared-prefix savings -- 3 rules share at least one prefix byte with another
  rule.

### 4.4 Example: Grammar With Ambiguity

A language where `Float` has two rules sharing `float(`:

```
info[D05] (MyLang): Float: 8 states (6 deterministic, 2 ambiguous), max depth 4, \
min lookahead 4, 1 NT boundaries, 2 shared-prefix savings, 5/7 rules deterministic
```

Interpretation:
- 2 ambiguous nodes -- two prefix paths have overlapping rules (see D01).
- `min_lookahead = 4` -- worst-case 4 tokens to resolve dispatch.
- `5/7 rules deterministic` -- 2 rules participate in at least one ambiguity.

### 4.5 Example: Grammar With Nonterminal Boundaries

A language with rules like `"if" Expr "then" Expr "else" Expr`:

```
info[D05] (Rho): Proc: 12 states (10 deterministic, 0 ambiguous), max depth 3, \
min lookahead 1, 3 NT boundaries, 5 shared-prefix savings, 12/12 rules deterministic
```

Interpretation:
- 3 NT boundaries -- three rules have nonterminal parse positions that split
  the trie into continuation segments.
- Fully deterministic despite the boundaries -- FIRST-set expansion at each
  boundary yields disjoint token sets.

## 5 Decision Tree Visualization

The following diagram shows how `TreeStats` fields map to the trie structure:

```
    root (depth 0)
     │
     ├── KwIf ─── KwThen ─── KwElse        max_depth = 3
     │             │                        deterministic_nodes += 1
     │             └── NT:Expr (boundary)   nonterminal_boundaries += 1
     │
     ├── KwLet ─── Eq ─── KwIn             deterministic_nodes += 1
     │
     ├── KwFloat ─── LParen                ambiguous_nodes += 1
     │                │                     (FloatId and IntToFloat share this path)
     │                ├── [Ident]  ──▶ FloatId
     │                └── [NT:Int] ──▶ IntToFloat
     │
     └── Integer                            deterministic_nodes += 1

     total_states = deterministic + ambiguous + boundaries
     shared_prefix_savings = total_states - total_rules
```

## 6 Source

**Function:** `complexity_metrics()` in `prattail/src/decision_tree.rs`

The function constructs a `TreeDiagnostic` whose message is
`format!("decision tree: {}", tree.stats)`.

**Pipeline call site:** `prattail/src/pipeline.rs`, inside the decision tree
construction block:

```rust
// Emit decision tree diagnostics (D05: complexity metrics per category)
for cat_name in &category_names {
    if let Some(tree) = dt_builder.get_tree(cat_name) {
        if tree.stats.total_states > 0 {
            pipeline_diagnostic(
                &bundle.grammar_name, "D05", "decision-tree-summary",
                crate::lint::LintSeverity::Info,
                format!("{}: {}", cat_name, tree.stats),
                None,
            );
        }
    }
}
```

**Statistics computation:** `compute_statistics()` in
`prattail/src/decision_tree.rs` walks all segments via `PathMap::iter()`,
accumulating fields into a `TreeStats` struct. Called by
`DecisionTreeBuilder::build_all()` after all rules are inserted.

## 7 Interpreting the Summary

| Indicator                           | Healthy                   | Review Recommended            |
|-------------------------------------|---------------------------|-------------------------------|
| `ambiguous_nodes`                   | 0                         | > 0 (check D01 for details)   |
| `min_lookahead`                     | 1 (LL(1))                 | > 2 (deep lookahead)          |
| `deterministic_rules / total_rules` | 100%                      | < 80%                         |
| `shared_prefix_savings`             | > 0 (good prefix sharing) | 0 (all rules unique)          |
| `nonterminal_boundaries`            | low                       | high (many NT-split segments) |

## 8 Related Lints

- [D01](D01-precision-ambiguity.md) -- Per-node ambiguity detail; the
  `ambiguous_nodes` count in D05 is the total number of D01 diagnostics.
- [D04](README.md) -- `min-lookahead-depth` provides a per-category narrative
  interpretation of the `min_lookahead` field.
- [D06](D06-wfst-trie-inconsistency.md) -- WFST/trie consistency; a high
  `ambiguous_nodes` count combined with D06 warnings suggests the WFST model
  may be out of sync with the grammar.
- [P04](../../../prattail/docs/diagnostics/performance/P04-many-alternatives.md)
  -- Runtime performance lint for tokens dispatching to many rules; correlates
  with high `ambiguous_nodes`.
