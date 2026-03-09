# DIS01: hot-path-misalignment

**Severity:** Note
**Category:** dispatch
**Feature Gate:** None (verbose-only: requires `PRATTAIL_LINT_VERBOSE=1`)

## Description

Detects when the WFST action table for a category is not ordered by weight,
meaning the first dispatch arm does not correspond to the lowest-weight
(highest-probability) parse alternative. In a well-ordered action table the
hot path -- the parse alternative most likely to succeed -- appears first, so
the dispatcher can try it before any alternatives.

The codegen pass CD01 always compensates for this by sorting dispatch arms
according to `predict()` output, which is weight-ordered. Therefore, DIS01
does **not** indicate that the emitted parser code is mis-ordered. Rather, it
signals that the `PredictionWfst` builder did not finalize action weights in
ascending order, which may indicate a builder logic issue or a non-converged
weight-training pass.

Because CD01 fully compensates, this lint is suppressed by default and only
appears when the `PRATTAIL_LINT_VERBOSE` environment variable is set.

```
  WFST action table for category `Expr`
  ┌──────────────┬────────┐
  │ Action       │ Weight │
  ├──────────────┼────────┤
  │ parse_Add    │  3.00  │  <-- first entry, but NOT lowest weight
  │ parse_Num    │  1.00  │  <-- lowest weight (hot path)
  │ parse_Mul    │  2.50  │
  └──────────────┴────────┘
        ↑
        DIS01 fires: first weight (3.00) ≠ minimum weight (1.00)
        CD01 reorders to: Num (1.00) → Mul (2.50) → Add (3.00)
```

## Trigger Conditions

All of the following must hold:

- The `PRATTAIL_LINT_VERBOSE` environment variable is set.
- A `PredictionWfst` exists for the category with at least 2 actions.
- The first action in the WFST action table has a weight that differs from
  the minimum weight across all actions by more than 0.01.

One diagnostic is emitted per affected category.

## Example

### Grammar

```rust
language! {
    name: MathExpr,
    types {
        ![i64] as Expr
    },
    terms {
        Num   . n:Expr |- n : Expr;
        Add   . a:Expr, b:Expr |- a "+" b : Expr;
        Mul   . a:Expr, b:Expr |- a "*" b : Expr;
    },
}
```

### Output

```
note[DIS01] (MathExpr): category `Expr`: WFST action table first weight 3.00 != minimum weight 1.00 (codegen CD01 compensates via predict()-based ordering)
  = hint: WFST builder should finalize actions in weight order; codegen dispatch arms are CD01-sorted regardless
```

## Resolution

1. **Verify weight training convergence.** If the grammar uses WFST weight
   training, ensure the training loop ran to convergence. Premature
   termination can leave action weights in an arbitrary order.

2. **Check builder finalization.** The `PredictionWfst` builder should sort
   its action list by weight before producing the final table. If a custom
   builder or plugin is used, ensure it calls the sort step.

3. **Ignore safely.** Since CD01 always reorders dispatch arms in the
   generated code, this diagnostic is informational. The emitted parser is
   correct regardless. The lint exists primarily as a builder hygiene check.

## Hint Explanation

The hint **"WFST builder should finalize actions in weight order; codegen
dispatch arms are CD01-sorted regardless"** conveys two facts:

- The **builder** (the pipeline stage that constructs `PredictionWfst`
  tables) is expected to produce weight-sorted action lists. When it does
  not, the lint fires as a hygiene warning.

- The **codegen** pass CD01 independently sorts dispatch arms by the output
  of `predict()`, which is always weight-ordered. This means the generated
  parser code is correct even when DIS01 fires -- the lint is about builder
  consistency, not runtime correctness.

## Related Lints

- [DIS02](DIS02-cold-arm-ratio.md) -- If most arms are cold, even the
  "hot path" may not be very hot, and the misalignment may be irrelevant.
- [DIS03](DIS03-decision-tree-depth.md) -- Deep decision trees interact
  with dispatch ordering: a misaligned hot path in a deep tree compounds
  the cost of each unsuccessful probe.
