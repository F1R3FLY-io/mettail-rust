# G32: prefix-isomorphism

**Severity:** Note
**Category:** Grammar Structure
**Feature Gate:** (none -- always active)

## Description

Detects categories with **structurally identical dispatch tries** -- their
PathMap-based decision trees have the same shape, depth, branching structure,
and action types, even though they serve different categories. Categories
with isomorphic dispatch tries could share parser code via parameterization,
reducing generated code size and compilation time.

The isomorphism detection uses **content hashing** of each category's
decision tree structure. For each category, the lint serializes:

- All (path, action) pairs from the tree's segments, where actions are
  normalized to their structural type (`Commit`, `Ambiguous`, or
  `NonterminalBoundary`) with sorted labels.
- `TreeStats`: total states, ambiguous nodes, and max depth.

Categories with identical hashes are grouped as isomorphic.

```
  Category "Expr"                   Category "Type"
  ┌─────────────────────┐         ┌─────────────────────┐
  │ Decision Tree:      │         │ Decision Tree:      │
  │   "+" → Commit(Add) │         │   "+" → Commit(Sum) │
  │   "-" → Commit(Sub) │         │   "-" → Commit(Neg) │
  │   states: 3         │         │   states: 3         │
  │   depth: 1          │         │   depth: 1          │
  └─────────────────────┘         └─────────────────────┘
  Same structure (paths, state count, depth) → isomorphic

  Note: rule labels differ (Add vs Sum), but the dispatch
  structure (paths and action types) is identical.
```

This lint complements [G30](G30-isomorphic-wfst-groups.md), which detects
isomorphic prediction WFSTs (the WFST-based dispatch counterpart). G32
operates on the PathMap decision tree, which is the primary dispatch
mechanism in the generated parser.

## Trigger Conditions

All of the following must hold:

- The grammar has at least two categories with decision trees in the lint
  context (`ctx.decision_trees`).
- At least two categories produce identical content hashes from their
  decision tree structure.

One diagnostic is emitted per group of isomorphic categories.

## Example

### Grammar

```rust
language! {
    name: TypedLang,
    types {
        ![i32] as Expr
        ![Type] as Type
    },
    terms {
        AddExpr . a:Expr, b:Expr |- a "+" b : Expr;
        SubExpr . a:Expr, b:Expr |- a "-" b : Expr;
        SumType . a:Type, b:Type |- a "+" b : Type;
        DifType . a:Type, b:Type |- a "-" b : Type;
    },
}
```

Both `Expr` and `Type` have identical dispatch structure: two tokens (`+`
and `-`), each leading to a `Commit` action, same depth, same state count.

### Output

```
note[G32] (TypedLang): categories [Expr, Type] have structurally identical dispatch tries; they could share parser code via parameterization
  = hint: consider using a generic parser parameterized over the category type
```

## Resolution

No action is required. This is an informational diagnostic suggesting a
potential optimization.

To exploit the isomorphism:

1. **Parameterize the dispatch code.** If the categories differ only in
   their semantic actions (not their dispatch structure), a generic parser
   function parameterized over the category type would avoid code
   duplication:

   ```rust
   fn parse_binop<C: Category>(input: &str, token_map: &TokenMap<C>) -> C {
       // Shared dispatch logic
   }
   ```

2. **Accept as informational.** If the grammar is small or compilation time
   is not a concern, the diagnostic requires no action. The parser will
   work correctly with duplicated dispatch code.

3. **Merge similar categories.** If the isomorphic categories represent
   similar concepts (e.g., `Expr` and `Type` both supporting the same
   operators), consider whether they could be unified into a single
   category with a discriminating wrapper.

## Hint Explanation

> consider using a generic parser parameterized over the category type

The hint suggests that since the dispatch structure is identical across
the listed categories, the generated code could be deduplicated by using
a generic function. Instead of generating N copies of the same dispatch
trie traversal (one per category), a single generic implementation would
reduce binary size and may improve instruction cache utilization. The
category-specific rule labels would be provided as a parameter (e.g., a
function pointer table or trait implementation).

## Related Lints

- [G30](G30-isomorphic-wfst-groups.md) -- detects categories with
  isomorphic prediction WFSTs (the WFST-based dispatch counterpart of
  G32's decision tree isomorphism)
- [G24](G24-alpha-equivalent-rules.md) -- detects alpha-equivalent rules
  within a category (rule-level structural sharing)
- [D10](../decision-tree/D10-lookahead-waste.md) -- detects when generated
  lookahead depth exceeds what is needed (related decision tree diagnostic)
