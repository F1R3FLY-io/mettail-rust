# D03: trie-unreachable-rule

**Date:** 2026-03-06
**Updated:** 2026-03-06
**Severity:** Warning
**Category:** Decision Tree

## 1 Description

Reports a rule that has no path from any trie root in its category's PathMap
decision tree. When a rule is present in the grammar but absent from all trie
segments, it means the rule is **shadowed** by higher-priority rules that
consume all inputs matching its terminal prefix. The shadowed rule can never be
dispatched to via the trie and is effectively dead code in the dispatch layer.

This diagnostic is a **Warning** because an unreachable rule represents wasted
grammar complexity: it contributes to compile-time overhead (rule processing,
WFST weight computation, Ascent relation generation) without ever participating
in runtime dispatch. It may also indicate an unintentional grammar design error
where the author expected the rule to be reachable.

## 2 Trigger Conditions

A D03 diagnostic is emitted when **all** of the following hold:

1. The category has a non-empty decision tree (built by
   `DecisionTreeBuilder::build_all()`).
2. The set of **eligible RD rule labels** for the category is computed by
   filtering `bundle.rd_rules` to include only rules that:
   - Belong to the category (`r.category == cat_name`).
   - Are not collection rules (`!r.is_collection`).
   - Have no prefix binding power (`r.prefix_bp.is_none()`).
   - Do not start with a nonterminal or ident capture (first item is a
     terminal).
3. The function `unreachable_rule_detection()` computes the set difference
   between the eligible rule labels and the labels found in the trie (across all
   segments, in both `Commit` and `Ambiguous` actions).
4. Any rule label in the difference set triggers a D03 diagnostic.

### 2.1 Excluded Rule Types

The following rule types are intentionally excluded from the eligible set and
will **not** trigger D03, even if absent from the trie:

- **Collection rules** (`is_collection = true`) -- dispatched via dedicated
  collection parsing, not the decision trie.
- **Unary prefix rules** (`prefix_bp.is_some()`) -- dispatched via the Pratt
  prefix handler, not the decision trie.
- **NT-leading rules** (first item is `NonTerminal`) -- not inserted into the
  trie because the leading nonterminal requires FIRST-set expansion, not
  terminal matching.
- **Ident-leading rules** (first item is `IdentCapture`) -- not inserted into
  the trie because ident captures match any identifier token.

## 3 Output Format

### 3.1 Message Structure

```
warning[D03] (GrammarName): rule <label> is unreachable in trie dispatch — shadowed by higher-priority paths
  = hint: check for duplicate prefix patterns or conflicting priorities
```

### 3.2 Example: Shadowed Rule

Given a grammar where two rules in the same category share an identical terminal
prefix, but one is consumed entirely by the other:

```
language! {
    name: MyLang;
    primary: Proc;

    category Proc {
        native_type: Proc;

        Send      = "send" "(" Proc ")";
        SendAsync = "send" "(" Proc "," "async" ")";
    }
}
```

If the trie construction inserts `Send` first (higher priority) and its prefix
`[KwSend, LParen]` fully covers the dispatch path, `SendAsync` may be shadowed
if the trie's `pjoin` merges them into an `Ambiguous` node that references only
`Send` (e.g., because `SendAsync`'s distinguishing suffix `"," "async"` is
beyond the terminal lookahead depth). In the more common case, both rules appear
in the `Ambiguous` node and D03 does not fire. D03 fires only when a rule is
**completely absent** from all trie actions:

```
warning[D03] (MyLang): rule SendAsync is unreachable in trie dispatch — shadowed by higher-priority paths
  = hint: check for duplicate prefix patterns or conflicting priorities
```

### 3.3 Example: Multiple Unreachable Rules

When several rules are shadowed in the same category, one diagnostic is emitted
per rule:

```
warning[D03] (Rho): rule MatchBind is unreachable in trie dispatch — shadowed by higher-priority paths
  = hint: check for duplicate prefix patterns or conflicting priorities

warning[D03] (Rho): rule MatchCase is unreachable in trie dispatch — shadowed by higher-priority paths
  = hint: check for duplicate prefix patterns or conflicting priorities
```

## 4 Shadowing Mechanism

The following diagram shows how shadowing arises in the trie:

```
    root
     │
     ├── 0x0A (KwSend)
     │    │
     │    └── 0x01 (LParen)
     │         │
     │         └─ [node value] ──▶ Commit: Send (w=0.00)
     │                              │
     │                              └── SendAsync never inserted
     │                                  (same prefix, lower priority,
     │                                   fully consumed by Send's Commit)
     │
     ├── 0x0B (KwRecv) ──▶ Commit: Recv
     │
     └── 0x0C (KwIf) ──▶ Commit: IfThenElse
```

The eligible rule set is `{Send, SendAsync, Recv, IfThenElse}`. The trie
contains `{Send, Recv, IfThenElse}`. The set difference is `{SendAsync}`, so
D03 fires for `SendAsync`.

## 5 Source

**Function:** `unreachable_rule_detection()` in
`prattail/src/decision_tree.rs`

```rust
pub fn unreachable_rule_detection(
    tree: &CategoryDecisionTree,
    all_rule_labels: &HashSet<String>,
) -> Vec<TreeDiagnostic>
```

The function:
1. Iterates all segments in the tree, collecting every `rule_label` that appears
   in a `Commit` action or as a candidate in an `Ambiguous` action into a
   `HashSet<String>` called `in_trie`.
2. Computes the set difference `all_rule_labels - in_trie`.
3. For each label in the difference, constructs a `TreeDiagnostic` with lint ID
   `"D03"` and severity `Warning`.

**Pipeline call site:** `prattail/src/pipeline.rs`, inside the decision tree
construction block:

```rust
// D03: Unreachable rule detection (trie-based)
for cat_name in &category_names {
    if let Some(tree) = dt_builder.get_tree(cat_name) {
        // Collect all RD rule labels for this category (excluding collections/prefix)
        let all_labels: std::collections::HashSet<String> = bundle.rd_rules
            .iter()
            .filter(|r| r.category == *cat_name && !r.is_collection && r.prefix_bp.is_none())
            .filter(|r| !matches!(
                r.items.first(),
                Some(crate::recursive::RDSyntaxItem::NonTerminal { .. }) |
                Some(crate::recursive::RDSyntaxItem::IdentCapture { .. })
            ))
            .map(|r| r.label.clone())
            .collect();
        for diag in crate::decision_tree::unreachable_rule_detection(tree, &all_labels) {
            pipeline_diagnostic(
                &bundle.grammar_name, diag.lint_id, "trie-unreachable-rule",
                diag.severity,
                diag.message,
                diag.hint,
            );
        }
    }
}
```

Note: the eligible label set is computed at the call site, not inside
`unreachable_rule_detection()`. This keeps the detection function generic --
it operates on any `HashSet<String>` of expected labels.

## 6 Resolution

1. **Remove the shadowed rule.** If the rule is intentionally unreachable (e.g.,
   an earlier draft that was superseded), delete it from the grammar to reduce
   compile-time overhead.

2. **Add a distinguishing terminal.** Insert a unique keyword or symbol at the
   beginning of the shadowed rule so the trie can dispatch to it independently:
   ```
   Send      = "send" "(" Proc ")";
   SendAsync = "send_async" "(" Proc "," "async" ")";
   ```

3. **Adjust rule priority.** If both rules should be reachable, ensure the trie
   construction inserts both. Check for priority annotations or ordering in the
   grammar definition that may cause one to shadow the other.

4. **Factor the common prefix.** Extract the shared prefix into a helper rule so
   both original rules are reachable via nonterminal boundary dispatch:
   ```
   SendOpen  = "send" "(";
   Send      = SendOpen Proc ")";
   SendAsync = SendOpen Proc "," "async" ")";
   ```

5. **Verify rule type.** If the rule is intended to be a collection, prefix, or
   NT-leading rule, annotate it correctly so it is excluded from the eligible
   set and does not trigger D03.

## 7 Related Lints

- [D01](D01-precision-ambiguity.md) -- Precision ambiguity; a rule that appears
  in an `Ambiguous` action is **not** unreachable (it participates in NFA
  try-all), so it does not trigger D03.
- [D05](D05-decision-tree-summary.md) -- The `deterministic_rules / total_rules`
  ratio reflects how many rules have clean dispatch; unreachable rules reduce
  `total_rules` when removed.
- [D06](D06-wfst-trie-inconsistency.md) -- WFST/trie inconsistency; a D03 rule
  that the WFST still predicts dispatch for would also trigger D06.
- [W01](../../../prattail/docs/diagnostics/wfst/W01-dead-rule.md) -- WFST dead
  rule detection; W01 detects rules unreachable via WFST analysis, while D03
  detects rules unreachable via trie analysis. Both firing for the same rule
  provides strong evidence of genuine unreachability.
