# I17: computed-goto-dispatch

**Severity:** Info
**Category:** infrastructure
**Feature Gate:** None (always enabled; activated by CD03 optimization gate)

## Description

Reports that the CD03 computed-goto dispatch optimization has been activated
for a category. Instead of generating a `match` statement with one arm per
token variant (which the Rust compiler may lower to a jump table or a linear
scan depending on variant count and density), CD03 generates an explicit
function pointer table indexed by token ID. This guarantees O(1) dispatch
regardless of the number of token variants.

The computed-goto pattern pre-computes a fixed-size array of function pointers
(`DispatchFn`) at function entry, indexed by the integer token ID. When a token
arrives, its ID is used as a direct array index to select the parsing function,
eliminating the branch prediction and comparison overhead of a `match` statement.

```
  Computed-goto dispatch:

  ┌──────────────────────────────────────────────┐
  │  type DispatchFn = fn(&[Token], &mut usize,  │
  │                       u8) -> Result<Cat>;     │
  │                                               │
  │  let table: [DispatchFn; N] = [               │
  │      parse_num,     // token_id 0             │
  │      parse_add,     // token_id 1             │
  │      parse_mul,     // token_id 2             │
  │      fallback,      // token_id 3             │
  │      ...                                      │
  │  ];                                           │
  │                                               │
  │  let id = token_to_id(&token) as usize;       │
  │  table[id](tokens, pos, min_bp)               │
  │  ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^              │
  │  O(1) dispatch: array index + indirect call    │
  └──────────────────────────────────────────────┘
```

For categories with many token variants (>8), this provides measurably better
branch prediction performance than a `match` statement, because the CPU's
indirect branch predictor has a single call site to track rather than N
conditional branches.

## Trigger Conditions

All of the following must hold:

- The CD03 optimization gate is enabled (either via cost-benefit analysis or
  `PRATTAIL_AUTO_OPTIMIZE` environment variable).
- The category has at least 2 dispatch arms.
- The `generate_computed_goto_dispatch()` function is called during codegen.

One diagnostic is emitted per category that receives computed-goto dispatch.

## Example

### Grammar

```rust
language! {
    name: ExprLang,
    types {
        ![i32] as Expr
    },
    terms {
        Num    . n:Expr |- n             : Expr;
        Add    . a:Expr, b:Expr |- a "+" b : Expr;
        Sub    . a:Expr, b:Expr |- a "-" b : Expr;
        Mul    . a:Expr, b:Expr |- a "*" b : Expr;
        Div    . a:Expr, b:Expr |- a "/" b : Expr;
        Neg    . a:Expr |- "-" a         : Expr;
        Paren  . a:Expr |- "(" a ")"     : Expr;
    },
}
```

### Output

```
info[I17]: CD03: computed goto dispatch activated for category `Expr`: 6 arm(s), table size 8
  = in category `Expr`
```

## Resolution

No action required. I17 is an informational diagnostic confirming that the
CD03 optimization is active. The function pointer table is generated
automatically when the optimization gate is enabled.

If computed-goto dispatch is **not** desired:

1. **Disable via environment.** Set `PRATTAIL_AUTO_OPTIMIZE` without `CD03`
   in the gate list to disable the optimization.

2. **Let cost-benefit decide.** If the cost-benefit analysis determines that
   the category has too few dispatch arms for the optimization to be
   beneficial, it will not activate CD03.

## Hint Explanation

I17 does not emit a hint. The diagnostic message itself provides the complete
information: the category name, the number of dispatch arms, and the table
size. The table size may be larger than the arm count when the token ID space
is sparse (gaps are filled with fallback function pointers).

## Related Lints

- [I01](I01-transducer-cascade.md) -- Transducer cascade. Pipeline
  infrastructure diagnostics share the I-prefix category.
- [I08](I08-env-override-active.md) -- Environment override active. The CD03
  gate can be controlled via `PRATTAIL_AUTO_OPTIMIZE`.
- [D10](../decision-tree/D10-dead-rule-weight.md) -- Lookahead waste. The
  decision tree depth affects the dispatch strategy; computed-goto handles the
  first-token dispatch, while deeper lookahead uses the decision tree.
