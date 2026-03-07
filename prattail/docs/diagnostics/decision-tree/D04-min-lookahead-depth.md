# D04: min-lookahead-depth

**Date:** 2026-03-06
**Updated:** 2026-03-06
**Severity:** Note
**Category:** Decision Tree

## 1 Description

Reports the minimum number of lookahead tokens required for deterministic
dispatch in a category's PathMap decision trie. D04 provides a per-category
classification of the grammar's dispatch complexity:

- **LL(1)** -- A single token peek resolves all dispatch. The trie has zero
  ambiguous nodes and `min_lookahead = 1`.
- **LL(k)** -- Multiple tokens must be examined to resolve dispatch. The trie
  has one or more ambiguous nodes, and `min_lookahead` equals the maximum trie
  depth (`max_depth`), representing the worst-case tokens needed.

This diagnostic is **informational** (Note severity). It requires no action from
the grammar author but provides a quick gauge of dispatch efficiency: LL(1)
grammars have zero-backtracking dispatch, while LL(k) grammars incur
progressively more lookahead overhead.

## 2 Trigger Conditions

A D04 diagnostic is emitted when **all** of the following hold:

1. `DecisionTreeBuilder::build_all()` has been called for the grammar.
2. The category has a non-empty decision tree (`tree.stats.total_states > 0`).
3. The pipeline calls `min_lookahead_report(tree)` for each qualifying category.

One D04 diagnostic is emitted per category that has at least one trie entry.
The diagnostic always fires -- it is not conditional on ambiguity.

## 3 Lookahead Computation

The `min_lookahead` field in `TreeStats` is computed as follows:

- If `ambiguous_nodes == 0`: `min_lookahead = 1`. No ambiguity exists, so a
  single token at any dispatch point uniquely identifies the target rule.
- If `ambiguous_nodes > 0`: `min_lookahead = max_depth`. The worst-case
  scenario requires examining tokens up to the maximum trie depth to attempt
  disambiguation. (In practice, most dispatch points resolve earlier, but the
  minimum guarantee is the worst case.)

### 3.1 LL(1) vs LL(k) Classification

| `min_lookahead` | Classification | Meaning                                         |
|-----------------|----------------|-------------------------------------------------|
| 1               | LL(1)          | All dispatch is deterministic with 1-token peek |
| 2               | LL(2)          | Some paths require 2-token lookahead            |
| 3+              | LL(k)          | Deep shared prefixes require k-token lookahead  |

The classification is a property of the grammar's terminal prefix structure, not
of the full grammar. A grammar may be LL(1) in the trie but still require
backtracking at nonterminal boundaries (handled by FIRST-set expansion and NFA
try-all).

## 4 Output Format

### 4.1 Message Structure

For LL(1) categories:

```
note[D04] (GrammarName): category <CatName> is fully deterministic at depth 1 (LL(1))
```

For LL(k) categories:

```
note[D04] (GrammarName): category <CatName> requires minimum <k>-token lookahead for deterministic dispatch
```

### 4.2 Example: LL(1) Category

A simple calculator where every rule starts with a distinct terminal:

```
language! {
    name: Calc;
    primary: Expr;

    category Expr {
        native_type: Expr;

        IfExpr  = "if" Expr "then" Expr "else" Expr;
        LetExpr = "let" <ident> "=" Expr "in" Expr;
        NumLit  = <integer>;
    }
}
```

Each rule starts with a unique token (`"if"`, `"let"`, `<integer>`). The trie
dispatches deterministically at depth 1:

```
note[D04] (Calc): category Expr is fully deterministic at depth 1 (LL(1))
```

### 4.3 Example: LL(2) Category

A grammar where two rules share a leading terminal but diverge at the second
token:

```
language! {
    name: TypeLang;
    primary: Type;

    category Type {
        native_type: Type;

        TypeRef = "type" <ident>;
        TypeDef = "type" "{" Type "}";
    }
}
```

Both rules start with `"type"`, but diverge at position 2 (`<ident>` vs `"{"`).
If both tokens are terminals in the trie, dispatch requires 2-token lookahead:

```
note[D04] (TypeLang): category Type requires minimum 2-token lookahead for deterministic dispatch
```

### 4.4 Example: LL(k) Category

A grammar with deeply shared prefixes:

```
note[D04] (Rho): category Proc requires minimum 4-token lookahead for deterministic dispatch
```

This indicates the Proc category has rules sharing up to 4 terminal tokens
before diverging.

## 5 Decision Trie Context

The following diagram shows how lookahead depth relates to trie structure:

```
    root (depth 0)              min_lookahead = 1 if no ambiguity
     │
     ├── KwIf ──▶ Commit        ← resolved at depth 1
     │
     ├── KwLet ──▶ Commit       ← resolved at depth 1
     │
     ├── KwType                  ← ambiguous at depth 1
     │    │
     │    ├── Ident ──▶ Commit   ← resolved at depth 2
     │    │
     │    └── LBrace ──▶ Commit  ← resolved at depth 2
     │
     └── Integer ──▶ Commit     ← resolved at depth 1

     max_depth = 2
     ambiguous_nodes = 1 (at KwType)
     min_lookahead = 2 (LL(2))
```

If the `KwType` node had no deeper children (making it a leaf ambiguity), the
`min_lookahead` would still be `max_depth = 2`, but D02 would also fire to
flag the unresolvable nature of the ambiguity.

## 6 Source

**Function:** `min_lookahead_report()` in `prattail/src/decision_tree.rs`

```rust
pub fn min_lookahead_report(tree: &CategoryDecisionTree) -> TreeDiagnostic {
    let depth = tree.stats.min_lookahead;
    TreeDiagnostic {
        lint_id: "D04",
        severity: crate::lint::LintSeverity::Note,
        category: tree.category.clone(),
        message: if depth <= 1 {
            format!(
                "category {} is fully deterministic at depth 1 (LL(1))",
                tree.category,
            )
        } else {
            format!(
                "category {} requires minimum {}-token lookahead for deterministic dispatch",
                tree.category, depth,
            )
        },
        hint: None,
    }
}
```

The function reads `tree.stats.min_lookahead` directly -- no additional
computation is performed. The `TreeStats` struct is populated during
`compute_statistics()`, called by `DecisionTreeBuilder::build_all()`.

**Pipeline call site:** `prattail/src/pipeline.rs`, inside the decision tree
construction block:

```rust
// D04: Minimum lookahead depth report
for cat_name in &category_names {
    if let Some(tree) = dt_builder.get_tree(cat_name) {
        if tree.stats.total_states > 0 {
            let diag = crate::decision_tree::min_lookahead_report(tree);
            pipeline_diagnostic(
                &bundle.grammar_name, diag.lint_id, "min-lookahead-depth",
                diag.severity,
                diag.message,
                diag.hint,
            );
        }
    }
}
```

## 7 Interpreting the Report

| `min_lookahead` | Performance                            | Action                                       |
|-----------------|----------------------------------------|----------------------------------------------|
| 1               | Optimal -- O(1) dispatch per token     | None needed                                  |
| 2               | Good -- O(2) dispatch, modest overhead | Consider if the shared prefix is intentional |
| 3-4             | Acceptable -- moderate lookahead       | Review D01/D02 for ambiguity details         |
| 5+              | Expensive -- deep shared prefixes      | Strongly consider factoring the grammar      |

### 7.1 Reducing Lookahead Depth

To move from LL(k) to LL(1):

1. **Ensure distinct leading terminals.** Each rule in a category should start
   with a unique terminal token. This immediately achieves LL(1).

2. **Factor shared prefixes.** Extract common prefix sequences into helper rules:
   ```
   TypeOpen = "type";
   TypeRef  = TypeOpen <ident>;
   TypeDef  = TypeOpen "{" Type "}";
   ```
   If the helper rule's continuation has disjoint FIRST sets, the nonterminal
   boundary resolves dispatch without additional terminal lookahead.

3. **Introduce disambiguating keywords.** Add a keyword after the shared prefix:
   ```
   TypeRef = "type" "ref" <ident>;
   TypeDef = "type" "def" "{" Type "}";
   ```

## 8 Related Lints

- [D01](D01-precision-ambiguity.md) -- Per-node ambiguity detail; each
  ambiguous node contributes to the `min_lookahead` depth.
- [D02](D02-unresolvable-ambiguity.md) -- Unresolvable ambiguity at leaf
  nodes; these nodes drive `min_lookahead` to `max_depth`.
- [D05](D05-decision-tree-summary.md) -- The summary's `min_lookahead` field
  is the same value reported by D04, but D05 presents it alongside other
  metrics while D04 provides a narrative interpretation.
- [D08](D08-optimization-suggestion.md) -- Optimization suggestions for
  reducing ambiguity, which indirectly reduces `min_lookahead`.
