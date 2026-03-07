# D02: unresolvable-ambiguity

**Date:** 2026-03-06
**Updated:** 2026-03-06
**Severity:** Warning
**Category:** Decision Tree

## 1 Description

Reports an ambiguity in the PathMap decision trie that **cannot** be resolved by
additional lookahead. A D02 warning fires when an `Ambiguous` trie node sits at
a leaf position -- no deeper terminal children exist beyond it. Because the trie
has exhausted all available terminal tokens along this path, no finite amount of
lookahead can disambiguate the competing rules. The conflict is inherent to the
grammar structure itself.

This diagnostic is a **Warning** (stronger than the D01 Note) because
unresolvable ambiguities represent a fundamental grammar design issue. While the
NFA try-all dispatcher handles them correctly at runtime, every unresolvable
ambiguity forces a full backtracking trial over all candidates for every input
matching the shared prefix. Unlike D01 ambiguities -- which deeper lookahead
might resolve in a future grammar revision -- D02 ambiguities require structural
grammar changes.

## 2 Trigger Conditions

A D02 diagnostic is emitted when **all** of the following hold:

1. The category has a non-empty decision tree (built by
   `DecisionTreeBuilder::build_all()`).
2. Iterating the root segment (`segments[0]`) via `PathMap::iter()` yields a
   `(path, DecisionAction::Ambiguous { candidates })` entry.
3. The `candidates` vector contains two or more `AmbiguousCandidate` structs
   with distinct `rule_label` values.
4. **No other entry** in the root segment has a path that strictly extends this
   path (i.e., `other.len() > path.len() && other.starts_with(path)` is false
   for all other entries). This confirms the ambiguous node is a **leaf**.

The leaf check distinguishes D02 from D01: a D01 ambiguity at an internal node
may be resolvable by inspecting deeper terminal children. A D02 ambiguity at a
leaf has no such recourse.

## 3 Output Format

### 3.1 Message Structure

```
warning[D02] (GrammarName): unresolvable ambiguity at [<path>] between <rule_a> and <rule_b> — no finite lookahead can disambiguate
  = hint: this is an inherent grammar conflict; consider adding a distinguishing
          terminal, reordering via WFST weights, or factoring the grammar
```

### 3.2 Example: Two-Rule Leaf Ambiguity

Given a grammar where two rules share an identical terminal prefix and diverge
only at a nonterminal boundary with no further terminals:

```
language! {
    name: MyLang;
    primary: Expr;

    category Expr {
        native_type: Expr;

        ApplyInt   = "apply" "(" Expr "," Int  ")";
        ApplyFloat = "apply" "(" Expr "," Float ")";
    }
}
```

Both rules encode the terminal prefix `[KwApply, LParen]`. After `LParen`, both
expect a nonterminal `Expr` followed by `Comma`, then diverge at another
nonterminal (`Int` vs `Float`). If the trie encodes only terminals, the path
`[KwApply, LParen]` is a leaf and the node is `Ambiguous`:

```
warning[D02] (MyLang): unresolvable ambiguity at [KwApply, LParen] between ApplyInt and ApplyFloat — no finite lookahead can disambiguate
  = hint: this is an inherent grammar conflict; consider adding a distinguishing
          terminal, reordering via WFST weights, or factoring the grammar
```

### 3.3 Example: Multi-Rule Leaf Ambiguity

When three rules all terminate at the same leaf prefix:

```
warning[D02] (Rho): unresolvable ambiguity at [KwNew] between NewChannel, NewContract, and NewBundle — no finite lookahead can disambiguate
  = hint: this is an inherent grammar conflict; consider adding a distinguishing
          terminal, reordering via WFST weights, or factoring the grammar
```

### 3.4 Example: Root-Level Ambiguity

When the ambiguous node is at the trie root (empty path), the path is rendered
as `<root>`:

```
warning[D02] (Calc): unresolvable ambiguity at [<root>] between ExprStmt and DeclStmt — no finite lookahead can disambiguate
  = hint: this is an inherent grammar conflict; consider adding a distinguishing
          terminal, reordering via WFST weights, or factoring the grammar
```

## 4 Leaf Detection in the Trie

The following diagram illustrates how leaf vs. internal ambiguity is determined:

```
    root
     │
     ├── 0x00 (KwApply)
     │    │
     │    └── 0x01 (LParen)
     │         │
     │         └─ [node value] ──▶ Ambiguous { ApplyInt, ApplyFloat }
     │              │
     │              └── (no deeper children) ← LEAF: D02 fires
     │
     ├── 0x05 (KwFloat)
     │    │
     │    └── 0x01 (LParen)
     │         │
     │         ├─ [node value] ──▶ Ambiguous { FloatId, IntToFloat }
     │         │
     │         ├── 0x80 (IDENT_CAPTURE) ──▶ Commit: FloatId
     │         │
     │         └── 0x82 (NT:Float) ──▶ Commit: IntToFloat
     │              │
     │              └── (has deeper children) ← INTERNAL: D01 fires, not D02
     │
     └── 0x0C (KwIf) ──▶ Commit: IfThenElse (deterministic, no ambiguity)
```

At path `[0x00, 0x01]`, the ambiguous node has no children extending it -- it is
a leaf. D02 fires. At path `[0x05, 0x01]`, deeper children exist (`0x80`,
`0x82`), so the ambiguity is potentially resolvable -- only D01 fires.

## 5 Source

**Function:** `unresolvable_ambiguity_reports()` in
`prattail/src/decision_tree.rs`

```rust
pub fn unresolvable_ambiguity_reports(
    tree: &CategoryDecisionTree,
    token_ids: &TokenIdMap,
) -> Vec<TreeDiagnostic>
```

The function:
1. Collects all `(path, action)` entries from `tree.segments[0]`.
2. For each `Ambiguous` entry, checks if any other entry's path strictly
   extends it (longer path with the same prefix).
3. If no extension exists (the node is a leaf), constructs a `TreeDiagnostic`
   with lint ID `"D02"` and severity `Warning`.
4. Decodes the byte path back to token variant names using `TokenIdMap::name()`.
   Bytes in the terminal range (`<= MAX_TERMINAL_ID`) are resolved to names;
   bytes outside that range are rendered in hexadecimal.

**Pipeline call site:** `prattail/src/pipeline.rs`, inside the decision tree
construction block:

```rust
// D02: Unresolvable ambiguity reports
for cat_name in &category_names {
    if let Some(tree) = dt_builder.get_tree(cat_name) {
        for diag in crate::decision_tree::unresolvable_ambiguity_reports(tree, &token_id_map) {
            pipeline_diagnostic(
                &bundle.grammar_name, diag.lint_id, "unresolvable-ambiguity",
                diag.severity,
                diag.message,
                diag.hint,
            );
        }
    }
}
```

## 6 Resolution

There are four strategies to eliminate a D02 unresolvable ambiguity:

1. **Add a distinguishing terminal.** Insert a unique keyword or symbol at or
   after the shared prefix so the trie can split deterministically. For example,
   change `ApplyFloat` to `"apply_f" "(" Expr "," Float ")"` so the first token
   differs.

2. **Factor the common prefix.** Extract the shared prefix into a helper rule
   and use a nonterminal boundary to dispatch based on FIRST-set analysis:
   ```
   ApplyOpen  = "apply" "(";
   ApplyInt   = ApplyOpen Expr "," Int   ")";
   ApplyFloat = ApplyOpen Expr "," Float ")";
   ```
   If `Int` and `Float` have disjoint FIRST sets, the nonterminal boundary
   resolves the ambiguity.

3. **Reorder via WFST weights.** Assign distinct WFST weights to the candidates
   so that the runtime try-all dispatcher prefers the higher-weight rule first,
   reducing average backtracking cost. This does not eliminate the ambiguity but
   optimizes the common case.

4. **Accept the ambiguity.** If the grammar intentionally allows overlapping
   syntax (e.g., for overloaded operators), the NFA try-all dispatch handles it
   correctly at runtime. The D02 warning makes the performance cost visible so
   the grammar author can make an informed decision.

## 7 Relationship to D01

D01 and D02 both report ambiguities in the decision trie but differ in
severity and actionability:

| Aspect                   | D01                              | D02                     |
|--------------------------|----------------------------------|-------------------------|
| Severity                 | Note                             | Warning                 |
| Node position            | Any (internal or leaf)           | Leaf only               |
| Resolvable by lookahead? | Possibly (deeper children exist) | No (no deeper children) |
| Grammar action needed?   | Optional                         | Recommended             |

D02 is a strict subset of D01: every D02-triggering node also triggers D01, but
not every D01 node triggers D02. When both fire for the same node, D02 takes
precedence in terms of actionability.

## 8 Related Lints

- [D01](D01-precision-ambiguity.md) -- Per-node ambiguity detail (Note
  severity); D02 is the leaf-restricted, Warning-severity refinement.
- [D05](D05-decision-tree-summary.md) -- The `ambiguous_nodes` count includes
  both D01 and D02 nodes.
- [D08](D08-optimization-suggestion.md) -- Optimization suggestions for each
  ambiguous node; D08 fires for both D01 and D02 nodes.
- [D09](D09-conflict-resolution-guide.md) -- Conflict resolution strategies;
  particularly relevant for D02 nodes where the conflict is inherent.
