# C-AP03: deep-congruence-chains

> **Historical Ascent-era identifier.** The current Dovetail/Rho pipeline has
> no production C-AP03 emitter. This page records the retired diagnostic contract.

**Severity:** Warning
**Category:** codegen-antipattern
**Feature Gate:** retired (not emitted)

## Description

Detects categories whose constructor field graph contains self-recursive or
mutually-recursive references, causing the generated Dovetail/Rho congruence
network to traverse chains of unbounded semantic depth. The generated
traversal must remain an explicit pushdown automaton (PDA), so term depth
affects heap-backed work rather than native-stack depth.

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
  = hint: retain stack-safe iterative congruence traversal, remove semantically redundant cycles, and measure work/RSS for the unbounded family
```

When multiple categories are affected, grouping consolidates:

```
warning[C-AP03] (RhoPi): 3 categories have unbounded congruence chain depth: Expr, Proc, Name
  = hint: retain stack-safe iterative congruence traversal, remove semantically redundant cycles, and measure work/RSS for the unbounded family
```

## Resolution

1. **Keep traversal stack-safe.** Generate an explicit PDA/worklist whose
   native-stack usage is constant in term depth. Do not impose an artificial
   semantic-depth ceiling.

2. **Share persistent structure.** Reuse immutable subterms or trie/arena
   identities where ownership permits. `Rc<T>` or `Arc<T>` alone is not a
   traversal algorithm; the consumer must still use an explicit work machine.

3. **Factor out recursive constructors.** Move deeply nested constructors
   into a separate category that is processed by a dedicated rewrite pass,
   reducing the congruence chain length in the primary category.

4. **Accept unbounded depth.** If the grammar inherently requires unbounded
   congruence propagation (e.g., a full lambda calculus), suppress this
   warning only after the iterative path and measured resource behavior are
   established for the intended depth distribution.

## Hint Explanation

The hint warns that an unbounded semantic chain is expected and separates
that property from native-stack use. The remediation strategies are:

- **Explicit PDA traversal**: put continuations on typed heap frames and drive
  them iteratively.
- **Cycle reduction and structural sharing**: remove semantically redundant
  work while preserving unbounded inputs.
- **Measurement**: govern time and RSS with workload/service-level evidence,
  not a completeness-losing depth cutoff.

## Related Lints

- [C-AP04](C-AP04-unbounded-rewrite-growth.md) -- Unbounded term growth via
  rewrite feedback. Interacts with C-AP03: deep congruence chains amplify the
  impact of positive-depth-delta rewrites.
- [C-AP05](C-AP05-clone-storm.md) -- Clone storm on collection fields.
  Collection fields in recursive constructors compound the congruence chain
  cost with per-iteration cloning.
- [G35](../grammar/G35-ground-rewrite-short-circuit.md) -- Ground rewrite
  short-circuit. Ground rewrites bypass congruence chains entirely.
