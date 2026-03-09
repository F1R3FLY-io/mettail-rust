# A07: fixpoint-iteration-anomaly

**Severity:** Warning
**Category:** Ascent / Fixpoint Performance
**Feature Gate:** none (always active)

## Description

Detects grammars whose **dependency group structure** suggests that Ascent's
fixpoint iteration may require an unusually large number of rounds to
converge.  The lint uses a dual-threshold heuristic: if the grammar has more
than 10 dependency groups AND the largest group contains more than 5
constructor labels, the combination of breadth (many groups) and depth
(large groups) creates conditions for slow convergence.

Each fixpoint iteration must propagate new equalities and rewrites through all
dependency groups.  When groups are both numerous and large, the amount of
cross-group interaction grows super-linearly:

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

  Combined effect: O(groups * max_group_size^2) work per iteration
  With >10 groups and >5 labels: risk of 50+ iterations
```

The 50-iteration threshold is empirically calibrated.  Grammars below the
dual threshold typically converge in under 20 iterations; those above it
may require 50 or more, with each iteration becoming progressively more
expensive as equivalence classes grow.

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
warning[A07] (ComplexLang): 11 dependency groups with max size 8 — fixpoint may require many iterations
  = hint: consider partitioning equations into independent strata or adding a depth bound
```

## Resolution

1. **Partition equations into strata.**  Independent sets of equations can be
   evaluated in separate Ascent phases.  If groups G1-G3 concern arithmetic
   and G7-G11 concern memory operations, running them as independent strata
   eliminates cross-group interference and reduces per-iteration work.

2. **Add a depth bound.**  The `ART05_DepthBound` optimization limits term
   depth during fixpoint evaluation.  This does not reduce iteration count
   directly but caps the cost of each iteration by preventing deep terms from
   entering the equivalence classes.

3. **Simplify dependency groups.**  Review whether large groups can be
   decomposed.  A group with 8 labels may contain independent subsets that
   should be separate groups, reducing the max-group-size metric.

4. **Accept the warning.**  Complex languages (e.g., process calculi with
   structural equivalence) inherently have many interacting axioms.  If the
   fixpoint converges in acceptable time, suppress with
   `PRATTAIL_LINT_LEVEL=error`.

## Hint Explanation

The hint **"consider partitioning equations into independent strata or adding
a depth bound"** offers two orthogonal strategies:

- **Stratification** reduces the breadth (number of simultaneously active
  groups) by sequencing independent equation sets into phases.  Each phase
  reaches its fixpoint independently, and downstream phases build on the
  results.

- A **depth bound** reduces the height (maximum term depth) that the fixpoint
  must process.  This prevents the worst-case exponential growth in
  equivalence class sizes, trading completeness for guaranteed termination.

## Related Lints

- [A01](A01-fixpoint-non-convergence.md) -- Unbounded term growth within a
  single rule compounds the iteration-count problem by generating more terms
  per iteration.
- [A04](A04-large-equivalence-class.md) -- High-participation constructors
  amplify the per-iteration cost within large dependency groups.
- [T03](../analysis/trs/T03-non-terminating-cycle.md) -- Non-terminating
  rewrite cycles can cause the fixpoint to never converge regardless of
  iteration count, a more severe form of the same underlying concern.
