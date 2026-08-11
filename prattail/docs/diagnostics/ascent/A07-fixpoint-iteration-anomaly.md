# A07: fixpoint-iteration-anomaly

**Severity:** Warning
**Category:** Equation/rewrite dependency performance (historical `A` identifier)
**Feature Gate:** none (always active)

## Description

Detects grammars whose **dependency group structure** suggests that generated
rewrite closure may require excessive cross-group propagation. The lint uses
a dual-threshold heuristic: if the grammar has more
than 10 dependency groups AND the largest group contains more than 5
constructor labels, the combination of breadth (many groups) and depth
(large groups) creates conditions for slow convergence.

Generated matching and rewrite closure must propagate consequences through
the dependency graph. When groups are both numerous and large, more
cross-group interactions are possible:

```
  Dependency Groups (>10):
  ┌───┬───┬───┬───┬───┬───┬───┬───┬───┬───┬───┐
  │G1 │G2 │G3 │G4 │G5 │G6 │G7 │G8 │G9 │G10│G11│
  └───┴───┴───┴───┴───┴───┴───┴───┴───┴───┴───┘

  Max group size (>5):
  ┌──────────────────────────────────────┐
  │ G7: {A, B, C, D, E, F, G, H}        │  8 labels
  │      ↕   ↕   ↕   ↕   ↕   ↕         │
  │ Cross-references between labels      │
  │ create O(n^2) pairwise interactions  │
  └──────────────────────────────────────┘

  Heuristic signal: many groups and a large maximum group
  (measure actual work before assigning a complexity class)
```

The thresholds classify a review candidate; they are not a theorem about
runtime complexity or a substitute for measured work/RSS evidence.

## Trigger Conditions

Both of the following must hold:

- The grammar has **more than 10** semantic dependency groups.
- The largest dependency group contains **more than 5** constructor labels.

At most one diagnostic is emitted per grammar.

## Example

### Grammar

```rust
language! {
    name: ComplexLang,
    types { ![i32] as Expr, ![String] as Name },
    // ... 11+ dependency groups with large axiom sets ...
    equations {
        // Group G1: {Add, Sub, Neg} (3 labels)
        // Group G2: {Mul, Div, Inv} (3 labels)
        // ...
        // Group G7: {Bind, Scope, Ref, Deref, Alloc, Free, Lock, Unlock} (8 labels)
        // Group G8-G11: ...
    },
}
```

### Output

```
warning[A07] (ComplexLang): 11 dependency groups with max size 8 — generated rewrite closure may require excessive cross-group propagation
  = hint: partition independent equations into strata, remove redundant cross-group dependencies, and profile the measured work/RSS of the remaining closure
```

## Resolution

1. **Partition equations into strata.**  Independent sets of equations can be
   compiled into separate closure strata. If groups G1-G3 concern arithmetic
   and G7-G11 concern memory operations, running them as independent strata
   eliminates irrelevant cross-group interference.

2. **Remove redundant dependencies.** Delete derivationally redundant axioms
   or factor shared lemmas so the same constructor is not a hub in unrelated
   groups.

3. **Simplify dependency groups.**  Review whether large groups can be
   decomposed.  A group with 8 labels may contain independent subsets that
   should be separate groups, reducing the max-group-size metric.

4. **Accept the warning.**  Complex languages (e.g., process calculi with
   structural equivalence) inherently have many interacting axioms.  If the
   closure converges within a measured resource service-level objective,
   suppress with
   `PRATTAIL_LINT_LEVEL=error`.

## Hint Explanation

The hint offers three complementary, semantics-preserving strategies:

- **Stratification** reduces the breadth (number of simultaneously active
  groups) by sequencing independent equation sets into phases.  Each phase
  reaches closure independently, and downstream phases build on the
  results.

- **Dependency reduction** removes unnecessary propagation edges.
- **Measurement** establishes whether remaining work and RSS meet the intended
  service-level objective. An artificial term-depth or iteration ceiling is
  not recommended because it would trade away completeness.

## Related Lints

- [A01](A01-fixpoint-non-convergence.md) -- Unbounded term growth within a
  single rule compounds the iteration-count problem by generating more terms
  per iteration.
- [A04](A04-large-equivalence-class.md) -- High-participation constructors
  amplify the per-iteration cost within large dependency groups.
- [T03](../analysis/trs/T03-non-terminating-cycle.md) -- Non-terminating
  rewrite cycles can cause the fixpoint to never converge regardless of
  iteration count, a more severe form of the same underlying concern.
