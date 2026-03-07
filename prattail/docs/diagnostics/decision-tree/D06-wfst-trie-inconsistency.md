# D06: wfst-trie-inconsistency

**Date:** 2026-03-06
**Updated:** 2026-03-06
**Severity:** Warning
**Category:** Decision Tree

## 1 Description

Cross-references the prediction WFST's token-to-rule mappings against the
PathMap decision trie's reachability for each category. A D06 warning fires when
the two representations disagree: the WFST believes a token can dispatch to one
or more rules in the category, but the trie has no corresponding path, or vice
versa. Such mismatches indicate that either the WFST weights are stale (computed
from an older grammar revision), a rule was added or removed without
regenerating the WFST, or a bug in the trie construction omitted a valid rule
prefix.

This diagnostic is a **Warning** because a WFST/trie mismatch can cause silent
parse failures: the WFST may guide the parser toward a rule that the trie-based
dispatch cannot reach, or the trie may attempt a dispatch that the WFST would
have pruned. Resolving D06 ensures that compile-time predictions and runtime
dispatch are aligned.

## 2 Trigger Conditions

A D06 diagnostic is emitted when **any** of the following mismatch patterns is
detected:

### 2.1 WFST Predicts, Trie Missing

For each token `t` in the WFST's token map:
1. `wfst.predict(t)` returns a non-empty set of `WeightedAction` entries.
2. The token is resolved to a byte ID via `token_ids.get(variant)` (must be in
   the terminal range `0x00..0x7F`).
3. The trie's root segment is queried with `segment.contains(&[byte])`.
4. If the trie does **not** contain a path starting with this byte, a D06
   warning fires.

This is the currently implemented check.

### 2.2 Trie Deterministic, WFST High-Ambiguity (Future)

A planned extension will also check:
1. The trie proves a token's dispatch is fully deterministic (single `Commit`
   action at depth 1).
2. The WFST assigns near-equal weights to 3+ rules for the same token.
3. If the WFST ambiguity count exceeds the trie's deterministic resolution, a
   D06 note fires to flag the discrepancy.

This check is infrastructure-ready but not yet wired into the pipeline.

## 3 Output Format

### 3.1 Message Structure

```
warning[D06] (GrammarName): WFST predicts dispatch for token <token> but trie has no path for it
  = in category `<category>`
  = hint: WFST weights may be stale or the rule was removed
```

### 3.2 Example: Missing Trie Path

A grammar where the WFST was trained with a `"render"` token dispatching to
`StrRender` in the `Str` category, but the rule was subsequently removed without
regenerating the WFST:

```
warning[D06] (MyLang): WFST predicts dispatch for token render but trie has no path for it
  = in category `Str`
  = hint: WFST weights may be stale or the rule was removed
```

### 3.3 Example: Multiple Missing Paths

When several tokens are affected (e.g., after a grammar refactoring), one
diagnostic is emitted per token:

```
warning[D06] (Rho): WFST predicts dispatch for token eval but trie has no path for it
  = in category `Proc`
  = hint: WFST weights may be stale or the rule was removed

warning[D06] (Rho): WFST predicts dispatch for token spawn but trie has no path for it
  = in category `Proc`
  = hint: WFST weights may be stale or the rule was removed
```

## 4 Cross-Reference Architecture

The consistency check bridges two independent data structures:

```
  ┌─────────────────────────┐       ┌──────────────────────────────┐
  │ PredictionWfst          │       │ CategoryDecisionTree         │
  │ ──────────────────────  │       │ ──────────────────────────── │
  │ token_map:              │       │ segments[0] (root PathMap):  │
  │   "float" → tok_id 5    │       │   [0x05]         → Commit    │
  │   "if"    → tok_id 12   │◄─────▶│   [0x0C]         → Commit    │
  │   "render"→ tok_id 20   │  ??   │   (no 0x14 path) → MISSING   │
  │                         │       │                              │
  │ predict("render"):      │       │ contains(&[0x14]):           │
  │   → [{StrRender, 0.8}]  │       │   → false                    │
  │                         │       │                              │
  │ predict("float"):       │       │ contains(&[0x05]):           │
  │   → [{FloatLit, 0.6}]   │       │   → true                     │
  └─────────────────────────┘       └──────────────────────────────┘
           │                                      │
           └──────────┬───────────────────────────┘
                      │
                      ▼
              D06 fires for "render"
              (WFST predicts, trie missing)
```

The check iterates the WFST's `token_map` (all registered tokens), not the
trie's entries. This direction catches "phantom" WFST entries that have no trie
backing. The reverse direction (trie entries with no WFST prediction) is not
currently checked because the trie is built from the grammar's rules
directly -- any trie entry that exists was derived from a live rule.

## 5 Source

**Function:** `wfst_consistency_check()` in `prattail/src/decision_tree.rs`

```rust
pub fn wfst_consistency_check(
    tree: &CategoryDecisionTree,
    wfst: &PredictionWfst,
    token_ids: &TokenIdMap,
) -> Vec<TreeDiagnostic>
```

The function:
1. Iterates `wfst.token_map.iter()` to get all `(token_name, tok_id)` pairs.
2. Calls `wfst.predict(token_name)` -- skips tokens with no predictions.
3. Resolves to a byte ID via `terminal_to_variant_name()` + `token_ids.get()`.
4. Checks `tree.segments[0].contains(&[byte])`.
5. If unreachable, pushes a `TreeDiagnostic` with lint ID `"D06"` and severity
   `Warning`.

**Pipeline call site:** `prattail/src/pipeline.rs`, inside the decision tree
construction block:

```rust
// D06: WFST-trie consistency check
for cat_name in &category_names {
    if let (Some(tree), Some(wfst)) = (
        dt_builder.get_tree(cat_name),
        prediction_wfsts.get(cat_name),
    ) {
        for diag in decision_tree::wfst_consistency_check(tree, wfst, &token_id_map) {
            pipeline_diagnostic(
                &bundle.grammar_name, diag.lint_id, "wfst-trie-inconsistency",
                diag.severity, diag.message, diag.hint,
            );
        }
    }
}
```

Note: the check requires both a `CategoryDecisionTree` and a `PredictionWfst`
to be available for the category. Categories without a WFST (e.g., because the
`wfst-log` feature is disabled and no default WFST was built) are silently
skipped.

## 6 Resolution

1. **Regenerate the WFST.** If the grammar changed since the WFST was last
   trained, rebuild it. PraTTaIL rebuilds WFSTs automatically during each
   pipeline run, so D06 warnings in normal builds indicate a construction order
   issue (the WFST was built before the trie, or from different rule data).

2. **Remove stale rules.** If the WFST references a rule that was intentionally
   removed, confirm the rule is no longer in the grammar's `terms` block. The
   WFST should drop the rule on the next rebuild.

3. **Check for trie construction gaps.** Some rule types are excluded from the
   decision tree by design:
   - Collection rules (`is_collection = true`)
   - Unary prefix rules (`prefix_bp.is_some()`)
   - Rules starting with a nonterminal or ident capture
   - Dead rules (in the `dead_rules` set)

   If the WFST predicts dispatch for a token that leads exclusively to one of
   these excluded rule types, the D06 warning is expected. The resolution is to
   suppress or annotate the rule appropriately.

4. **Investigate encoding overflow.** Terminal token IDs must fit in the range
   `0x00..0x7F` (128 terminals). Grammars with more than 128 terminal variants
   will have some tokens unrepresentable in the trie, causing D06 warnings for
   those tokens. The resolution is to reduce the terminal count or extend the
   encoding range.

## 7 Related Lints

- [D01](D01-precision-ambiguity.md) -- Precision ambiguity within the trie; D06
  detects disagreement *between* the WFST and the trie, while D01 detects
  ambiguity *within* the trie alone.
- [D05](D05-decision-tree-summary.md) -- The summary's `total_states` field
  reflects how many trie entries exist for the WFST to cross-reference against.
- [W01](../../../prattail/docs/diagnostics/wfst/W01-dead-rule.md) -- Dead rule
  detection via the WFST; a rule flagged by W01 (WFST-unreachable) that still
  appears in the trie would be the inverse of a D06 warning.
- [W03](../../../prattail/docs/diagnostics/wfst/W03-high-ambiguity-token.md) --
  High-ambiguity token in the WFST; when combined with D06, it may indicate
  that the WFST's ambiguity model is not reflected in the trie's dispatch
  structure.
