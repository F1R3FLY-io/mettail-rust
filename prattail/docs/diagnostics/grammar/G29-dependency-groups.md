# G29: dependency-groups

**Severity:** Note
**Category:** Grammar Structure (macro phase)
**Feature Gate:** (none -- always active)

## Description

Reports the results of **fine-grained dependency group analysis** on the
grammar's equations and rewrites. Dependency groups are connected components
in a graph where nodes are rules and edges connect rules that share
constructor labels in their LHS patterns. Rules in different connected
components have no constructor-level dependencies and can potentially be
evaluated in separate strata during Ascent's fixpoint computation.

The analysis is performed by `compute_fine_dependency_groups()` from the
`PatternIndex` infrastructure (Sprint 6). It builds a graph where each rule
is a node and adds an edge between any two rules that reference the same
constructor label. The connected components of this graph partition the rules
into independent groups.

```
  Rules:         Constructor Graph:        Dependency Groups:
  ┌──────────┐   Add ─── Sub              ┌──────────┐
  │ AddZero  │    │       │               │ Group 1:  │
  │ SubZero  │    │       │               │ AddZero   │
  │ MulOne   │   Mul ─── Div              │ SubZero   │
  │ DivOne   │                            ├──────────┤
  └──────────┘                            │ Group 2:  │
                                          │ MulOne    │
                 AddZero uses Add         │ DivOne    │
                 SubZero uses Sub         └──────────┘
                 Add, Sub are linked
                 (via shared Expr category)
                 MulOne uses Mul
                 DivOne uses Div
                 Mul, Div are linked
```

The diagnostic reports the total number of groups, how many are
**independent** (single-rule groups that share no constructors with any other
rule), and how many are **cross-group** (multi-rule groups with internal
dependencies).

## Trigger Conditions

All of the following must hold:

- The grammar defines equations or rewrites.
- The `PatternIndex` is built and `compute_fine_dependency_groups()` returns
  more than one group.

One diagnostic is emitted per grammar (summary level).

## Example

### Grammar

```rust
language! {
    name: Arith,
    types { ![i32] as Expr },
    terms {
        Add  . a:Expr, b:Expr |- a "+" b : Expr;
        Mul  . a:Expr, b:Expr |- a "*" b : Expr;
        Zero . |- "0" : Expr;
        One  . |- "1" : Expr;
    },
    equations {
        AddZero . a:Expr |- Add(a, Zero()) = a;
        MulOne  . a:Expr |- Mul(a, One()) = a;
    },
}
```

### Output

```
note[G29] (Arith): 2 fine-grained dependency group(s) detected (1 independent, 1 cross-group)
  = hint: independent groups can be evaluated in separate strata for performance
```

## Resolution

No action is required. This is an informational diagnostic. The dependency
group information is used internally by the compiler for potential
stratification optimizations.

The information is useful for understanding the grammar's structure:

1. **Many independent groups** suggest the grammar has well-separated
   concerns that could benefit from multi-stratum evaluation.

2. **Few large cross-group components** suggest tightly coupled rules that
   must be evaluated together in the same fixpoint.

3. **A single group** means all rules are transitively connected through
   shared constructors, and no stratification optimization is possible.

## Hint Explanation

> independent groups can be evaluated in separate strata for performance

The hint refers to a potential optimization: when rules have no constructor-
level dependencies, their Ascent evaluation can be split into separate
strata (evaluation phases). Each stratum computes a partial fixpoint
independently, and the results are combined. This reduces the working set
size of each stratum's SCC (strongly connected component) and can
significantly reduce fixpoint iteration count for grammars with many
independent rule clusters.

Currently, multi-stratum evaluation is deferred pending compilation cost
analysis (each additional `ascent!` struct adds ~5-10s compile time), but
the dependency group data is available for future activation.

## Related Lints

- [G28](G28-alpha-equivalent-groups.md) -- alpha-equivalent LHS pattern
  groups (a different structural analysis from the same pattern trie)
- [G30](G30-isomorphic-wfst-groups.md) -- isomorphic WFST dispatch topology
  groups (categories with identical dispatch structure)
- [G24](G24-alpha-equivalent-rules.md) -- per-category alpha-equivalence
  detection
