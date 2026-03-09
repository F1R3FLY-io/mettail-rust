# C-AP03: deep-congruence-chains

**Severity:** Warning
**Category:** codegen-antipattern
**Feature Gate:** None (always enabled)

## Description

Detects categories whose constructor field graph contains self-recursive or
mutually-recursive references, causing the generated Ascent congruence rules to
form chains of unbounded depth. For every nesting level of the recursive
constructor, the congruence engine must fire an additional rule iteration,
leading to fixpoint iteration counts proportional to the deepest AST nesting
encountered at runtime.

The detector builds a directed graph from each grammar category to the set of
categories referenced by its constructor fields. A self-loop (category A has a
field of type A) produces an immediately unbounded chain. An indirect cycle
(A -> B -> ... -> A) is detected by computing the longest simple path from each
node; when the path visits a node already on the stack, the depth is marked
unbounded.

```
  Constructor field graph with self-loop:

  ┌─────────────────────────┐
  │  category Expr           │
  │  ┌─────────────────────┐ │
  │  │ Add(Expr, Expr)     │─┤
  │  │ Neg(Expr)           │─┤
  │  │ Num(i32)            │ │
  │  └─────────────────────┘ │
  └──────────┬──────────────┘
             │
             └──── self-loop: Expr -> Expr
                   congruence chain depth = unbounded
```

When the maximum congruence chain depth exceeds the threshold (default 10) or
is unbounded, one C-AP03 diagnostic is emitted per affected category. In
grouped mode, all affected categories are consolidated into a single summary
diagnostic.

## Trigger Conditions

All of the following must hold:

- The grammar defines at least one category with constructor rules.
- The constructor field graph for a category contains either:
  - A **self-loop**: the category has a constructor whose field type is the
    same category (e.g., `Add . a:Expr, b:Expr |- ... : Expr`).
  - An **indirect cycle**: a chain of field references that eventually returns
    to the originating category (e.g., Expr -> Stmt -> Expr).
  - A **deep acyclic chain**: the longest path through the field graph exceeds
    the depth threshold (default 10).
- Antipattern detection is invoked during macro expansion (always-on).

## Example

### Grammar

```rust
language! {
    name: DeepNest,
    types {
        ![i32] as Expr
    },
    terms {
        Num  . n:Expr |- n            : Expr;
        Add  . a:Expr, b:Expr |- a "+" b : Expr;
        Neg  . a:Expr |- "-" a        : Expr;
    },
}
```

### Output

```
warning[C-AP03] (DeepNest): deep congruence chain: category `Expr` has a self-recursive constructor field -- congruence chain depth is unbounded
  = hint: congruence rules for `Expr` will apply recursively at every nesting level; consider bounding the rewrite depth or using explicit recursion control
```

When multiple categories are affected, grouping consolidates:

```
warning[C-AP03] (RhoPi): 3 categories have unbounded congruence chain depth: Expr, Proc, Name
  = hint: congruence rules for `Expr` will apply recursively at every nesting level; consider bounding the rewrite depth or using explicit recursion control
```

## Resolution

1. **Add explicit depth bounds.** Use the ART05 compile-time depth bound
   analysis (feature `depth-bounds`) to cap congruence propagation at a
   fixed depth. This trades completeness for predictable fixpoint iteration.

2. **Break the recursion with an indirection.** Wrap the recursive field in
   `Rc<T>` or `Arc<T>` so the congruence rule operates on a reference rather
   than the structural term. This does not eliminate the logical recursion but
   reduces the per-iteration work.

3. **Factor out recursive constructors.** Move deeply nested constructors
   into a separate category that is processed by a dedicated rewrite pass,
   reducing the congruence chain length in the primary category.

4. **Accept unbounded depth.** If the grammar inherently requires unbounded
   congruence propagation (e.g., a full lambda calculus), suppress this
   warning by acknowledging that fixpoint iteration count is proportional to
   AST depth.

## Hint Explanation

The hint **"congruence rules for `<Cat>` will apply recursively at every
nesting level; consider bounding the rewrite depth or using explicit recursion
control"** warns that the generated Ascent congruence rules form a chain where
each nesting level of the recursive constructor triggers an additional
iteration. For an AST of depth d, the congruence fixpoint requires at least d
iterations before convergence. The two remediation strategies are:

- **Bounding the rewrite depth**: limiting how many levels of congruence are
  propagated per evaluation, trading completeness for bounded runtime.
- **Explicit recursion control**: restructuring the grammar so that deep
  nesting is handled by a separate recursive pass rather than implicit
  congruence rule chaining.

## Related Lints

- [C-AP04](C-AP04-unbounded-rewrite-growth.md) -- Unbounded term growth via
  rewrite feedback. Interacts with C-AP03: deep congruence chains amplify the
  impact of positive-depth-delta rewrites.
- [C-AP05](C-AP05-clone-storm.md) -- Clone storm on collection fields.
  Collection fields in recursive constructors compound the congruence chain
  cost with per-iteration cloning.
- [G35](../grammar/G35-ground-rewrite-short-circuit.md) -- Ground rewrite
  short-circuit. Ground rewrites bypass congruence chains entirely.
