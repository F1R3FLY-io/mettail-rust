# DIS03: decision-tree-depth

**Severity:** Warning
**Category:** dispatch
**Feature Gate:** None

## Description

Warns when a category's PathMap-based decision tree exceeds a maximum depth
threshold of 8. The decision tree is a trie structure that dispatches parse
attempts based on prefix token sequences: each level of the tree corresponds
to one token of lookahead consumed during dispatch. A deep tree means that
many tokens must be inspected before the parser can commit to a specific rule,
which increases both the latency of the dispatch decision and the amount of
input that must be tentatively consumed and potentially backtracked.

Deep decision trees typically arise when multiple rules in a category share
long common prefixes. For example, if five rules all begin with `"let" IDENT
":" Type "="`, the decision tree must descend through at least five tokens
before it can distinguish them.

```
  Decision tree for category `Stmt` (depth = 10)

  ┌─ "let"
  │  ├─ IDENT
  │  │  ├─ ":"
  │  │  │  ├─ Type
  │  │  │  │  ├─ "="
  │  │  │  │  │  ├─ Expr ";"         → LetBind
  │  │  │  │  │  ├─ "mut" Expr ";"   → LetMut
  │  │  │  │  │  ├─ "[" ...          → LetDestr
  │  │  │  │  │  └─ ...              (depth continues)
  │  │  │  │  └─ ...
  │  │  │  └─ ...
  │  │  └─ ...
  │  └─ ...
  └─ ...

  Depth 10 > threshold 8 → DIS03 fires
```

## Trigger Conditions

All of the following must hold:

- A `DecisionTree` exists for the category in the lint context.
- The tree's `stats.max_depth` exceeds 8.

One diagnostic is emitted per affected category.

## Example

### Grammar

```rust
language! {
    name: DeepStmt,
    types {
        ![String] as Stmt,
        ![String] as Expr,
        ![String] as Type
    },
    terms {
        Lit      . s:Expr |- s : Expr;
        LetBind  . name:Expr, ty:Type, val:Expr |- "let" name ":" ty "=" val ";" : Stmt;
        LetMut   . name:Expr, ty:Type, val:Expr |- "let" "mut" name ":" ty "=" val ";" : Stmt;
        LetRef   . name:Expr, ty:Type, val:Expr |- "let" "ref" name ":" ty "=" val ";" : Stmt;
        LetPat   . name:Expr, ty:Type, val:Expr |- "let" "(" name ")" ":" ty "=" val ";" : Stmt;
        // Many more "let" variants...
    },
}
```

### Output

```
warning[DIS03] (DeepStmt): category `Stmt` decision tree depth 12 exceeds threshold of 8 -- long shared prefixes
  = hint: consider left-factoring rules or using segment merging (CD02)
```

## Resolution

1. **Left-factor rules.** Extract the shared prefix into a single rule and
   differentiate only at the point of divergence. For example, parse
   `"let"` once, then branch on the next token (`"mut"`, `"ref"`, `"("`,
   or an identifier).

2. **Use segment merging (CD02).** The codegen optimization CD02 (disjoint-
   first segment merging) can automatically merge shared prefix segments
   across rules, reducing effective decision tree depth without manual
   grammar refactoring.

3. **Introduce intermediate categories.** Break a deeply-nested category
   into sub-categories. For example, a `LetBinding` sub-category can handle
   all `"let"` variants, reducing the depth of the parent `Stmt` tree.

4. **Accept the depth.** Some grammars inherently require deep lookahead.
   If the depth is unavoidable (e.g., the language specification mandates
   long shared prefixes), the warning can be acknowledged. Backtracking
   elimination (G1) and multi-token lookahead (B1) mitigate the runtime
   cost.

## Hint Explanation

The hint **"consider left-factoring rules or using segment merging (CD02)"**
recommends two complementary strategies:

- **Left-factoring** is a classic grammar transformation that extracts
  shared prefixes from multiple rules into a single production, deferring
  the branching decision to the first point of divergence. This directly
  reduces tree depth.

- **CD02 (disjoint-first segment merging)** is a codegen optimization that
  identifies shared prefix segments at compile time and generates code that
  parses the common prefix once, then dispatches to the divergent suffix.
  It achieves the same effect as left-factoring without requiring the
  grammar author to restructure rules manually.

## Related Lints

- [DIS04](DIS04-backtrack-elimination-coverage.md) -- Deep trees often have
  low backtracking elimination coverage because the shared prefixes force
  save/restore at each probe.
- [DIS05](DIS05-nfa-try-all-set-size.md) -- Deep trees with ambiguous
  leaves may produce large try-all sets at the ambiguous depth levels.
- [PAR01](../parser/PAR01-deep-rd-chain.md) -- Deep decision trees within a
  single category compound with deep cross-category RD chains to produce
  extreme call stack depth.
