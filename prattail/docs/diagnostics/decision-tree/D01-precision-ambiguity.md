# D01: precision-ambiguity

**Date:** 2026-03-06
**Updated:** 2026-03-06
**Severity:** Note
**Category:** Decision Tree

## 1 Description

Reports a precise ambiguity at a specific node in a category's PathMap decision
trie. When two or more rules share an identical byte-encoded token prefix and
the trie cannot deterministically choose between them, the node is marked
`DecisionAction::Ambiguous`. D01 fires once for each such node, providing the
exact token path that leads to the conflict, the competing rule labels, their
WFST weights, and -- for two-candidate conflicts -- a resolution hint.

This diagnostic is **informational** (Note severity) because the parser handles
ambiguous dispatch at runtime via NFA try-all on the minimal candidate set. D01
exists to surface these runtime costs at compile time so the grammar author can
decide whether to restructure the grammar for deterministic dispatch.

## 2 Trigger Conditions

A D01 diagnostic is emitted when **all** of the following hold:

1. The category has a non-empty decision tree (built by
   `DecisionTreeBuilder::build_all()`).
2. Iterating the root segment (`segments[0]`) via `PathMap::iter()` yields a
   `(path, DecisionAction::Ambiguous { candidates })` entry.
3. The `candidates` vector contains two or more `AmbiguousCandidate` structs
   with distinct `rule_label` values.

The analysis function `precision_ambiguity_reports()` performs this iteration and
constructs one `TreeDiagnostic` per ambiguous node.

## 3 Output Format

The diagnostic message includes:

- **Token prefix path** -- the byte-encoded trie path decoded back to token
  variant names (e.g., `KwFloat`, `LParen`) using the `TokenIdMap`. Bytes in the
  terminal range `0x00..0x7F` are decoded to their registered variant name; bytes
  outside this range are rendered in hexadecimal (`0x80`, `0x82`, etc.).
- **Conflicting rule labels** -- the `rule_label` field of each candidate,
  joined with "and".
- **Weights** -- the WFST weight of each candidate (default `0.0` when no WFST
  data is available).
- **Resolution hint** -- for exactly two candidates, a suggestion to add a
  distinguishing terminal before the divergence point.

### 3.1 Message Structure

```
note[D01] (GrammarName): ambiguity at [<path>] between <rule_a> and <rule_b>
  = N candidates at path [<hex_bytes>]: <label_1>, <label_2>, ...
  = hint: adding a distinguishing terminal before the divergence point
          would resolve the ambiguity between <rule_a> and <rule_b>
```

### 3.2 Example

Given a grammar with two Float rules that both start with `float(`:

```
language! {
    name: MyLang;
    primary: Float;

    category Float {
        native_type: Float;

        FloatId    = "float" "(" <ident> ")";
        IntToFloat = "float" "(" Float  ")";
    }
}
```

Both rules encode to the terminal prefix `[KwFloat, LParen]` (bytes `[0x00,
0x01]` assuming those are the first two registered tokens). After `LParen`, one
rule expects an `IDENT_CAPTURE` (`0x80`) and the other expects a nonterminal
(`0x82+`). Because the trie cannot distinguish these at the terminal prefix
level, the node at `[0x00, 0x01]` is `Ambiguous`.

Output:

```
note[D01] (MyLang): ambiguity at [KwFloat, LParen] between FloatId and IntToFloat
  = 2 candidates at path [0x00, 0x01]: FloatId, IntToFloat
  = hint: adding a distinguishing terminal before the divergence point
          would resolve the ambiguity between FloatId and IntToFloat
```

### 3.3 Multi-Candidate Example

When three or more rules share a prefix, no hint is emitted (the resolution is
grammar-specific):

```
note[D01] (Expr): ambiguity at [KwLet] between LetIn, LetRec, and LetMut
  = 3 candidates at path [0x0F]: LetIn, LetRec, LetMut
```

## 4 Decision Trie Context

The following diagram shows how an ambiguous node arises in the trie:

```
    root
     │
     ├── 0x00 (KwFloat)
     │    │
     │    └── 0x01 (LParen)
     │         │
     │         ├── 0x80 (IDENT_CAPTURE) ──▶ Commit: FloatId  (w=0.00)
     │         │
     │         └── 0x82 (NT:Float)       ──▶ Commit: IntToFloat (w=0.00)
     │         │
     │         └─ [node value] ──────────▶ Ambiguous { FloatId, IntToFloat }
     │
     ├── 0x0C (KwIf) ──▶ Commit: IfThenElse (deterministic)
     │
     └── 0x0F (KwLet) ──▶ Commit: LetIn (deterministic)
```

At the path `[0x00, 0x01]`, two rules converge. The trie's `pjoin` lattice
operation merges them into a single `Ambiguous` action. D01 reports this node.

## 5 Source

**Function:** `precision_ambiguity_reports()` in `prattail/src/decision_tree.rs`

**Pipeline call site:** `prattail/src/pipeline.rs`, inside the decision tree
construction block, after `build_all()`:

```rust
// D01: Precision ambiguity reports
for cat_name in &category_names {
    if let Some(tree) = dt_builder.get_tree(cat_name) {
        for diag in decision_tree::precision_ambiguity_reports(tree, &token_id_map) {
            pipeline_diagnostic(
                &bundle.grammar_name, diag.lint_id, "precision-ambiguity",
                diag.severity, diag.message, diag.hint,
            );
        }
    }
}
```

## 6 Resolution

There are three strategies to eliminate a D01 ambiguity:

1. **Add a distinguishing terminal.** Insert a unique keyword or symbol before
   the point where the rules diverge. For example, change `IntToFloat` to
   `"float" "(" "int" Float ")"` so the trie splits deterministically at
   `[KwFloat, LParen, KwInt]` vs `[KwFloat, LParen, Ident]`.

2. **Factor the common prefix.** Extract the shared `"float" "("` prefix into a
   helper rule and use a nonterminal boundary to dispatch:
   ```
   FloatOpen = "float" "(";
   FloatId    = FloatOpen <ident> ")";
   IntToFloat = FloatOpen Float  ")";
   ```
   After factoring, the trie has a single `Commit` at the `FloatOpen` prefix,
   and the nonterminal boundary resolves via FIRST-set analysis.

3. **Accept the ambiguity.** If the grammar intentionally allows overlapping
   prefixes (e.g., for overloaded syntax), the NFA try-all dispatch handles it
   correctly at runtime. The D01 note simply makes the cost visible.

## 7 Related Lints

- [D05](D05-decision-tree-summary.md) -- The `ambiguous_nodes` field in the
  summary reports the total count of D01-triggering nodes.
- [D08](README.md) -- `optimization-suggestion` provides automated guidance for
  resolving two-candidate ambiguities.
- [D09](README.md) -- `conflict-resolution-guide` enumerates general strategies
  for genuine conflicts (including multi-candidate cases).
- [G03](../../../prattail/docs/diagnostics/grammar/G03-ambiguous-prefix.md) --
  Grammar-level ambiguous prefix detection; D01 is its trie-level refinement.
- [W02](../../../prattail/docs/diagnostics/wfst/W02-nfa-ambiguous-prefix.md) --
  WFST-level NFA ambiguous prefix; D01 provides the precise trie path.
