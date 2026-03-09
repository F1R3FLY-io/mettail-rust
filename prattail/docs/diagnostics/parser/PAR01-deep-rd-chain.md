# PAR01: deep-rd-chain

**Severity:** Warning
**Category:** parser
**Feature Gate:** None

## Description

Warns when a category's cross-category recursive-descent (RD) call chain
depth exceeds a threshold of 5. The call chain depth is the longest path
through the inter-category call graph, where an edge from category A to
category B exists when a rule in A references B via a `NonTerminal` item.

Deep call chains arise in grammars with many layers of syntactic delegation.
For example, a grammar that routes `Stmt -> Expr -> Term -> Factor -> Atom ->
Literal -> NumLit` has a chain depth of 6 for `Stmt`. Each level of
delegation corresponds to a function call in the recursive-descent parser
(or a trampoline frame push in the trampoline-based parser), so deep chains
stress the call stack (or the trampoline frame pool) and increase the latency
of parsing even simple inputs.

The lint builds a call graph from the grammar's syntax items and computes the
maximum depth for each category using depth-first search with cycle detection.
Cycles (mutual recursion between categories) are detected and broken to avoid
infinite recursion in the analysis.

```
  Cross-category call graph (depth = 7)

  Program ──→ Stmt ──→ Expr ──→ BinExpr ──→ UnaryExpr ──→ PostfixExpr ──→ Primary ──→ Literal
     │                                                                        │
     └─ depth 7 ─────────────────────────────────────────────────────────────┘

  Threshold: 5
  Program depth (7) > 5 → PAR01 fires for category `Program`
```

## Trigger Conditions

All of the following must hold:

- The inter-category call graph contains a path from the category to a
  leaf (a category with no outgoing cross-category references) with
  length greater than 5.
- Cycles are not counted (the DFS breaks on revisited nodes).

One diagnostic is emitted per affected category.

## Example

### Grammar

```rust
language! {
    name: DeepLang,
    types {
        ![String] as Program,
        ![String] as Stmt,
        ![String] as Expr,
        ![String] as Term,
        ![String] as Factor,
        ![String] as Atom
    },
    terms {
        Prog     . s:Stmt |- s : Program;
        ExprStmt . e:Expr |- e ";" : Stmt;
        TermExpr . t:Term |- t : Expr;
        FactTerm . f:Factor |- f : Term;
        AtomFact . a:Atom |- a : Factor;
        NumAtom  . n:Atom |- n : Atom;
        Add      . a:Expr, b:Term |- a "+" b : Expr;
    },
}
```

### Output

```
warning[PAR01] (DeepLang): category `Program` has cross-category RD call chain depth 5 (threshold: 5)
  = hint: deep call chains stress the trampoline stack -- consider flattening with cast rules
```

(If `Program -> Stmt -> Expr -> Term -> Factor -> Atom -> ...` exceeds 5.)

## Resolution

1. **Flatten with cast rules.** PraTTaIL supports cast rules that allow
   one category to directly accept values of another without an explicit
   delegation rule. For example, instead of `Expr -> Term -> Factor`,
   use a cast from `Factor` to `Expr` and eliminate the intermediate
   `Term` category.

2. **Merge intermediate categories.** If `Term` and `Factor` serve only as
   precedence scaffolding, consider merging them into `Expr` and using
   binding power levels to handle precedence instead of separate categories.

3. **Use Pratt parsing for precedence.** PraTTaIL's Pratt parser handles
   operator precedence within a single category via binding powers,
   eliminating the need for precedence-climbing category chains like
   `Expr -> Term -> Factor -> Atom`.

4. **Accept the depth.** Some grammars inherently require deep category
   hierarchies (e.g., languages with many distinct syntactic forms). The
   trampoline parser handles deep chains safely without stack overflow,
   so the warning is about performance, not correctness.

## Hint Explanation

The hint **"deep call chains stress the trampoline stack -- consider
flattening with cast rules"** explains:

- **Trampoline stack stress** refers to the trampoline parser's explicit
  continuation stack (`Vec<Frame_Cat>`). Each cross-category call pushes a
  frame, and deep chains produce tall frame stacks. While the trampoline
  prevents stack overflow (unlike raw recursion), deep stacks still consume
  heap memory and reduce cache locality.

- **Cast rules** are PraTTaIL's mechanism for direct cross-category value
  acceptance. A cast from category B to category A allows A to accept any
  value that B produces, without an intermediate rule. This eliminates one
  level of call chain per cast.

## Related Lints

- [DIS03](../dispatch/DIS03-decision-tree-depth.md) -- Decision tree depth
  within a category compounds with cross-category call chain depth to
  produce the total parse path length.
- [PAR05](PAR05-trampoline-frame-variant-count.md) -- Deep call chains
  often correspond to many trampoline frame variants, since each category
  in the chain contributes its own frame types.
- [PAR02](PAR02-unused-bp-level.md) -- Unused BP levels may indicate that
  precedence could be handled within a single category (via Pratt parsing)
  instead of separate category layers.
