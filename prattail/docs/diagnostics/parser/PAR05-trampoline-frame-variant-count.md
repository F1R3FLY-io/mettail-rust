# PAR05: trampoline-frame-variant-count

**Severity:** Note
**Category:** parser
**Feature Gate:** None

## Description

Reports when the estimated number of trampoline frame variants for a
category exceeds 15. In PraTTaIL's trampoline-based parser, each category
generates a `Frame_<Cat>` enum whose variants represent continuation points
in the parse. When a rule calls into a sub-parse (e.g., to parse a
non-terminal), the current state is saved as a frame variant and pushed onto
the explicit continuation stack. After the sub-parse completes, the frame is
popped and execution resumes.

Each recursive-descent rule with N non-terminal items generates approximately
N continuation frame variants (one for each point where the parser yields
control to a sub-parse). A category with many complex rules accumulates
many frame variants, which increases the size of the `Frame_<Cat>` enum.
Large enums have two costs:

1. **Compilation overhead.** The Rust compiler must generate match arms for
   every variant. Large enums with many variants can slow down compilation,
   especially with LLVM optimizations enabled.

2. **Frame size.** The enum's in-memory size is the maximum of all variant
   sizes. Many variants with different payload types can produce a large
   frame, which consumes more stack/heap memory per frame and reduces cache
   efficiency.

```
  Frame_Expr enum (estimated 18 variants)

  ┌─────────────────────────────────────────────────┐
  │ Frame_Expr                                      │
  ├─────────────────────────────────────────────────┤
  │ Add_rhs  { lhs: Expr, op_pos: usize }          │
  │ Sub_rhs  { lhs: Expr, op_pos: usize }          │
  │ Mul_rhs  { lhs: Expr, op_pos: usize }          │
  │ Div_rhs  { lhs: Expr, op_pos: usize }          │
  │ Mod_rhs  { lhs: Expr, op_pos: usize }          │
  │ Pow_rhs  { lhs: Expr, op_pos: usize }          │
  │ Neg_arg  { op_pos: usize }                     │
  │ Paren_inner  { op_pos: usize }                 │
  │ FnCall_arg   { func: Expr, op_pos: usize }     │
  │ FnCall_close { func: Expr, arg: Expr }          │
  │ Index_idx    { arr: Expr, op_pos: usize }       │
  │ Index_close  { arr: Expr, idx: Expr }            │
  │ Ternary_then { cond: Expr }                     │
  │ Ternary_else { cond: Expr, then: Expr }          │
  │ Cast_type    { expr: Expr }                      │
  │ Lambda_body  { param: Expr, arrow_pos: usize }   │
  │ Block_inner  { brace_pos: usize }                │
  │ Tuple_next   { elems: Vec<Expr>, comma_pos: ... }│
  └─────────────────────────────────────────────────┘

  18 variants > threshold 15 → PAR05 fires
```

## Trigger Conditions

All of the following must hold:

- The category has at least one recursive-descent rule.
- The estimated frame variant count (sum of non-terminal counts per rule,
  with a minimum of 1 per rule) exceeds 15.

One diagnostic is emitted per affected category.

## Example

### Grammar

```rust
language! {
    name: BigExpr,
    types {
        ![i64] as Expr
    },
    terms {
        Num      . n:Expr |- n : Expr;
        Add      . a:Expr, b:Expr |- a "+" b : Expr;
        Sub      . a:Expr, b:Expr |- a "-" b : Expr;
        Mul      . a:Expr, b:Expr |- a "*" b : Expr;
        Div      . a:Expr, b:Expr |- a "/" b : Expr;
        Mod      . a:Expr, b:Expr |- a "%" b : Expr;
        Pow      . a:Expr, b:Expr |- a "^" b : Expr;
        Neg      . a:Expr |- "-" a : Expr;
        Paren    . a:Expr |- "(" a ")" : Expr;
        FnCall   . f:Expr, a:Expr |- f "(" a ")" : Expr;
        Index    . a:Expr, i:Expr |- a "[" i "]" : Expr;
        Ternary  . c:Expr, t:Expr, e:Expr |- c "?" t ":" e : Expr;
        Cast     . a:Expr, t:Expr |- a "as" t : Expr;
        Lambda   . p:Expr, b:Expr |- p "->" b : Expr;
        Block    . a:Expr |- "{" a "}" : Expr;
        Tuple    . a:Expr, b:Expr |- "(" a "," b ")" : Expr;
    },
}
```

### Output

```
note[PAR05] (BigExpr): category `Expr` has ~22 trampoline frame variants (threshold: 15) -- large frame size
  = hint: consider splitting complex rules or factoring common prefixes
```

## Resolution

1. **Split into sub-categories.** Move some rules into a sub-category to
   distribute the frame variants. For example, create a `PrimaryExpr`
   category for `Paren`, `FnCall`, `Index`, `Block`, and `Tuple`, reducing
   the variant count for both the main `Expr` category and the new
   sub-category.

2. **Factor common prefixes.** Rules that share non-terminal patterns (e.g.,
   `FnCall` and `Index` both start with `Expr`) can be factored so that the
   first non-terminal is parsed once and the continuation branches on the
   following terminal. This reduces the total variant count.

3. **Use infix/postfix operators.** Rules like `Add`, `Sub`, `Mul` are
   handled by the Pratt infix parser, which shares a single frame variant
   for all binary operators. Moving more rules to infix form reduces the
   RD frame variant count.

4. **Accept the count.** Large grammars for real languages often exceed the
   threshold. The compilation overhead is manageable (especially with the
   Cranelift codegen backend for dev builds), and runtime performance is
   not significantly affected. The lint is a monitoring signal.

## Hint Explanation

The hint **"consider splitting complex rules or factoring common prefixes"**
recommends:

- **Splitting complex rules** means distributing rules across multiple
  categories so no single category accumulates too many frame variants. This
  is the most direct solution.

- **Factoring common prefixes** means identifying shared non-terminal
  patterns across rules and parsing them once, branching at the first
  divergence point. This reduces the number of distinct continuation points
  (and thus frame variants).

## Related Lints

- [PAR01](PAR01-deep-rd-chain.md) -- Splitting rules into sub-categories
  increases call chain depth. PAR05 and PAR01 represent a trade-off:
  fewer variants per category vs. deeper cross-category chains.
- [DIS03](../dispatch/DIS03-decision-tree-depth.md) -- Categories with many
  rules tend to have both deep decision trees and many frame variants.
- [DIS04](../dispatch/DIS04-backtrack-elimination-coverage.md) -- Many
  frame variants may correlate with low backtracking elimination coverage
  if the variants correspond to rules with shared prefixes.
