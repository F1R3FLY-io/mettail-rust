# D08: optimization-suggestion

**Date:** 2026-03-06
**Updated:** 2026-03-06
**Severity:** Note
**Category:** Decision Tree

## 1 Description

For each `Ambiguous` node in the PathMap decision trie, suggests concrete
grammar modifications to resolve the ambiguity and eliminate backtracking. D08
provides actionable guidance tailored to the number of competing candidates:

- **Two candidates:** Suggests adding a distinguishing terminal before the
  divergence point to split the trie deterministically.
- **Three or more candidates:** Suggests factoring the common prefix into a
  shared helper rule so all candidates dispatch via nonterminal boundaries.

This diagnostic is **informational** (Note severity). It does not indicate a
bug -- the parser handles ambiguous dispatch correctly via NFA try-all at
runtime. D08 exists to help the grammar author optimize dispatch by eliminating
unnecessary backtracking.

## 2 Trigger Conditions

A D08 diagnostic is emitted when **any** of the following hold:

### 2.1 Two-Candidate Ambiguity

1. A trie node has `DecisionAction::Ambiguous { candidates }`.
2. `candidates.len() == 2`.
3. A D08 diagnostic is emitted suggesting a distinguishing terminal.

### 2.2 Multi-Candidate Ambiguity

1. A trie node has `DecisionAction::Ambiguous { candidates }`.
2. `candidates.len() > 2`.
3. A D08 diagnostic is emitted suggesting prefix factoring.

D08 iterates **all segments** of the trie (not just the root), so ambiguities
at nonterminal boundary continuation segments are also covered.

## 3 Output Format

### 3.1 Two-Candidate Message

```
note[D08] (GrammarName): rules <rule_a> and <rule_b> have ambiguous prefix — adding a distinguishing terminal would eliminate backtracking
  = hint: consider inserting a keyword before the divergence point
```

### 3.2 Multi-Candidate Message

```
note[D08] (GrammarName): <N> rules share an ambiguous prefix: [<label_1>, <label_2>, ...] — consider factoring the common prefix into a shared rule
```

(No hint is emitted for multi-candidate ambiguities because the resolution is
grammar-specific.)

### 3.3 Example: Two-Candidate Suggestion

Given two rules sharing `"float" "("`:

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

Output:

```
note[D08] (MyLang): rules FloatId and IntToFloat have ambiguous prefix — adding a distinguishing terminal would eliminate backtracking
  = hint: consider inserting a keyword before the divergence point
```

Concrete resolution: change `IntToFloat` to `"float" "(" "int" Float ")"` so
the trie splits at `[KwFloat, LParen, KwInt]` vs `[KwFloat, LParen, Ident]`.

### 3.4 Example: Multi-Candidate Suggestion

Given three rules sharing `"new"`:

```
language! {
    name: Rho;
    primary: Proc;

    category Proc {
        native_type: Proc;

        NewChannel  = "new" <ident> "in" Proc;
        NewContract = "new" "contract" <ident> Proc;
        NewBundle   = "new" "bundle" Proc;
    }
}
```

If all three encode to the prefix `[KwNew]` and the trie cannot distinguish them
at depth 1 (e.g., the second tokens are nonterminals or ident captures):

```
note[D08] (Rho): 3 rules share an ambiguous prefix: [NewChannel, NewContract, NewBundle] — consider factoring the common prefix into a shared rule
```

Resolution: factor `"new"` into a helper:
```
NewOpen     = "new";
NewChannel  = NewOpen <ident> "in" Proc;
NewContract = NewOpen "contract" <ident> Proc;
NewBundle   = NewOpen "bundle" Proc;
```

With the helper in place, the continuation tokens (`Ident`, `KwContract`,
`KwBundle`) can be used for deterministic dispatch via FIRST-set expansion at
the nonterminal boundary.

### 3.5 Example: Multiple D08 Diagnostics

When a grammar has several ambiguous nodes, one D08 diagnostic is emitted per
node:

```
note[D08] (MyLang): rules FloatId and IntToFloat have ambiguous prefix — adding a distinguishing terminal would eliminate backtracking
  = hint: consider inserting a keyword before the divergence point

note[D08] (MyLang): rules LetIn and LetRec have ambiguous prefix — adding a distinguishing terminal would eliminate backtracking
  = hint: consider inserting a keyword before the divergence point

note[D08] (MyLang): 4 rules share an ambiguous prefix: [MatchInt, MatchFloat, MatchStr, MatchBool] — consider factoring the common prefix into a shared rule
```

## 4 Suggestion Strategy

The two suggestion strategies correspond to different grammar restructuring
patterns:

### 4.1 Distinguishing Terminal (2 candidates)

```
    Before:                              After:
    root                                 root
     │                                    │
     └── KwFloat ── LParen               └── KwFloat ── LParen
          │                                   │
          └── Ambiguous                       ├── KwInt ──▶ Commit: IntToFloat
              {FloatId, IntToFloat}           │
                                              └── Ident ──▶ Commit: FloatId
```

Adding `"int"` after `LParen` in `IntToFloat` creates a deterministic split.

### 4.2 Prefix Factoring (3+ candidates)

```
    Before:                              After:
    root                                 root
     │                                    │
     └── KwNew                           └── KwNew ──▶ NonterminalBoundary
          │                                             │
          └── Ambiguous                                 ├── FIRST(Ident) ──▶ NewChannel
              {NewChannel,                              ├── FIRST(KwContract) ──▶ NewContract
               NewContract,                             └── FIRST(KwBundle) ──▶ NewBundle
               NewBundle}
```

Factoring `"new"` into a helper rule converts the ambiguous node into a
nonterminal boundary, where FIRST-set expansion resolves dispatch.

## 5 Source

**Function:** `optimization_suggestions()` in `prattail/src/decision_tree.rs`

```rust
pub fn optimization_suggestions(tree: &CategoryDecisionTree) -> Vec<TreeDiagnostic>
```

The function:
1. Iterates all segments in the tree.
2. For each `Ambiguous` action with 2 candidates, emits a D08 diagnostic
   suggesting a distinguishing terminal, with a hint.
3. For each `Ambiguous` action with 3+ candidates, emits a D08 diagnostic
   suggesting prefix factoring, without a hint.
4. Returns all collected diagnostics.

**Pipeline call site:** `prattail/src/pipeline.rs`, inside the decision tree
construction block:

```rust
// D08: Optimization suggestions
for cat_name in &category_names {
    if let Some(tree) = dt_builder.get_tree(cat_name) {
        for diag in crate::decision_tree::optimization_suggestions(tree) {
            pipeline_diagnostic(
                &bundle.grammar_name, diag.lint_id, "optimization-suggestion",
                diag.severity,
                diag.message,
                diag.hint,
            );
        }
    }
}
```

## 6 Resolution

D08 diagnostics are suggestions, not errors. The grammar author can:

1. **Apply the suggestion.** Modify the grammar as described in the diagnostic
   to eliminate the ambiguity.

2. **Ignore the suggestion.** If the ambiguity is intentional or the
   backtracking cost is acceptable, no action is needed. The NFA try-all
   dispatcher handles the ambiguity correctly at runtime.

3. **Use WFST weights.** Instead of restructuring the grammar, assign distinct
   WFST weights to the candidates so the runtime dispatcher tries the most
   likely rule first, reducing average backtracking cost.

## 7 Related Lints

- [D01](D01-precision-ambiguity.md) -- Precision ambiguity detail; D08 provides
  optimization guidance for the same ambiguous nodes reported by D01.
- [D02](D02-unresolvable-ambiguity.md) -- Unresolvable ambiguity; D08 fires
  for both resolvable (D01-only) and unresolvable (D02) ambiguities.
- [D04](D04-min-lookahead-depth.md) -- Minimum lookahead depth; applying D08
  suggestions reduces `min_lookahead` toward 1 (LL(1)).
- [D09](D09-conflict-resolution-guide.md) -- Conflict resolution guide; D09
  enumerates all resolution strategies, while D08 focuses on the most likely
  effective one for each ambiguity pattern.
