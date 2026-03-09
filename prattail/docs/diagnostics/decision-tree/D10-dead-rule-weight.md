# D10: lookahead-waste

**Severity:** Note
**Category:** decision-tree
**Feature Gate:** None (always enabled)

## Description

Detects when a category's decision tree has a maximum lookahead depth
significantly deeper than necessary for the majority of its dispatch points.
Specifically, D10 fires when the tree's `max_depth` exceeds 2 but 80% or more
of the dispatch tokens can be resolved at depth 1 (single-token lookahead).

A decision tree with maximum depth k means the parser may need to inspect up to
k tokens before determining which rule to apply. When the vast majority of
tokens need only a single token of lookahead, the remaining deep-lookahead
tokens are the true source of parser complexity. D10 highlights this imbalance,
suggesting that a small number of tokens are responsible for the grammar's
lookahead requirements.

```
  Lookahead depth distribution:

  depth 1:  ████████████████████████████████  92%  (23/25 tokens)
  depth 2:  ██                                4%  (1/25 tokens)
  depth 3:  ██                                4%  (1/25 tokens)

  max_depth = 3, but 92% resolve at depth 1
  ⟹ D10 fires: the 2 deep-lookahead tokens are candidates for left-factoring
```

The diagnostic reports the category name, the max lookahead depth, and the
percentage of dispatch points that resolve at depth 1, along with a hint that
the few deep-lookahead tokens may benefit from left-factoring.

## Trigger Conditions

All of the following must hold:

- The category has a non-empty decision tree (`total_states > 0`).
- The decision tree's `max_depth` exceeds 2.
- At least 80% of the category's dispatch tokens resolve at depth 1:
  - `DispatchStrategy::Singleton` tokens count as depth 1.
  - `DispatchStrategy::DisjointSuffix` tokens with `shared_prefix_len == 0`
    count as depth 1.
  - All other strategies (fallback, ambiguous) count as requiring deeper
    lookahead.

One diagnostic is emitted per affected category.

## Example

### Grammar

```rust
language! {
    name: ExprLang,
    types {
        ![i32] as Expr
    },
    terms {
        Num    . n:Expr |- n           : Expr;
        Add    . a:Expr, b:Expr |- a "+" b : Expr;
        Sub    . a:Expr, b:Expr |- a "-" b : Expr;
        Mul    . a:Expr, b:Expr |- a "*" b : Expr;
        Div    . a:Expr, b:Expr |- a "/" b : Expr;
        // These two rules share the "let" prefix token:
        Let    . |- "let" Ident "=" Expr     : Expr;
        LetRec . |- "let" "rec" Ident "=" Expr : Expr;
    },
}
```

### Output

```
note[D10] (ExprLang): category `Expr`: 4-token max lookahead generated but 1-token suffices for 83% (5/6) of dispatch points
  = hint: the few deep-lookahead tokens may be candidates for left-factoring
```

## Resolution

1. **Left-factor shared prefixes.** When two rules share a leading token
   sequence (e.g., `"let"` in both `Let` and `LetRec`), refactor them so the
   common prefix is parsed once and the disambiguation happens at the first
   point of divergence. This reduces the max lookahead depth.

2. **Split ambiguous tokens into separate categories.** If the deep-lookahead
   tokens correspond to a distinct sublanguage, factor them into a dedicated
   category with its own dispatch tree, keeping the primary category's
   lookahead shallow.

3. **Accept the deep lookahead.** If the grammar inherently requires
   multi-token lookahead for a small number of constructs, this diagnostic
   is informational only. The parser's overall performance is dominated by
   the 80%+ of tokens that resolve at depth 1.

## Hint Explanation

The hint **"the few deep-lookahead tokens may be candidates for left-factoring"**
identifies the standard grammar transformation for reducing lookahead depth.
Left-factoring extracts the shared prefix of two or more rules into a single
rule that parses the common tokens, then dispatches to the suffix rules at the
point of divergence. This is the PraTTaIL analog of the classic LL(1)
transformation for removing FIRST set conflicts.

## Related Lints

- [D01](D01-precision-ambiguity.md) -- Precision ambiguity in the decision
  tree. Deep lookahead often coincides with ambiguous dispatch points.
- [D04](D04-min-lookahead-depth.md) -- Minimum lookahead depth report. Shows
  the theoretical minimum lookahead required per category.
- [D05](D05-decision-tree-summary.md) -- Decision tree summary statistics.
  Provides the full depth distribution that D10 summarizes.
- [D13](D13-sync-depth-ranking.md) -- Parsed-but-unrewritten constructors.
  Orphan rules may contribute unnecessary depth to the decision tree.
