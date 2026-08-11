# A09: generated-rewrite-network-size

**Severity:** Warning or Note
**Category:** Dovetail/Rho code-generation performance (historical `A` identifier)
**Feature Gate:** none (always active)

## Description

Reports when the estimated size of the generated **Dovetail/Rho equation and
rewrite network** exceeds practical thresholds. PraTTaIL lowers each
grammar into relations (approximately 3 per
category: the category relation, its equation relation, and its rewrite
relation) and rules (approximately 2 per syntax entry: a deconstruction rule
and a congruence rule). Large generated networks can significantly impact
**compile time**, since the Rust compiler must monomorphize, type-check, and
optimize every relation and rule.

The lint uses two thresholds:

```
  ┌─────────────────────────────────────────────────────────┐
  │  Metric            │  Threshold  │  Severity            │
  ├────────────────────┼─────────────┼──────────────────────┤
  │  Rule estimate     │  >100       │  Warning             │
  │  Relation count    │  >50        │  Note (if rules <=100│
  └─────────────────────────────────────────────────────────┘

  relation_count = categories * 3
  rule_estimate  = syntax_entries * 2
```

A Warning-level A09 identifies a compile-cost review candidate. The heuristic
does not by itself establish a complexity class or predict wall time; capped
build measurements provide that evidence.

A Note-level A09 is informational: the grammar is substantial but not yet
at the point where compilation is prohibitively slow.

## Trigger Conditions

One of the following must hold:

- **Warning:** The estimated rule count (`all_syntax.len() * 2`) exceeds
  **100**.  One diagnostic is emitted.
- **Note:** The estimated relation count (`categories.len() * 3`) exceeds
  **50**, AND the rule estimate is 100 or fewer.  One diagnostic is emitted.

At most one diagnostic is emitted per grammar.

## Example

### Grammar (large)

```rust
language! {
    name: Rholang,
    // 20 categories, 60+ syntax entries
    types { ![...] as Proc, ... },
    terms {
        // ~60 constructors across 20 categories
        // Estimated: ~60 relations, ~120 rules
    },
}
```

### Output (Warning)

```
warning[A09] (Rholang): estimated ~60 relations and ~120 generated equation/rewrite rules — a large Dovetail/Rho network may slow compilation
  = hint: consider splitting categories into independent modules or enabling demand-driven population
```

### Output (Note)

```
note[A09] (MediumLang): estimated ~54 relations in the generated Dovetail/Rho rewrite network
```

## Resolution

1. **Split into independent modules.**  If the grammar has categories that do
   not interact equationally, they can be compiled as separate network
   strata. This reduces per-unit complexity and allows parallel construction.

2. **Enable demand-driven population.**  The `ART06_DemandAnalysis`
   optimization skips populating equation/rewrite relations for categories
   that are not demanded by any equation or rewrite rule.  This reduces the
   effective struct size without restructuring the grammar.

3. **Measure before changing the compiler backend.** Use capped clean and
   incremental builds to distinguish generated-code volume, monomorphization,
   and LLVM optimization cost. Record an alternate backend only as a separate
   controlled experiment.

4. **Accept the diagnostic.**  If the grammar is inherently large and cannot
   be decomposed, the compile-time cost is a necessary trade-off.  Use
   incremental compilation and caching to mitigate.

## Hint Explanation

The hint **"consider splitting categories into independent modules or enabling
demand-driven population"** targets the two main strategies:

- **Splitting** reduces the monolithic generated network into smaller,
  independently compiled units.  The key insight is that categories without
  cross-references can be separated without loss of semantics.

- **Demand-driven population** (ART06) uses compile-time analysis to identify
  which categories actually need equation and rewrite relations.  Categories
  that are never referenced in equations get empty relations, reducing the
  closure work even when the grammar itself remains large.

## Related Lints

- [A02](A02-redundant-congruence.md) -- Redundant congruence rules contribute
  to struct bloat; eliminating them reduces the rule count.
- [A07](A07-fixpoint-iteration-anomaly.md) -- Large structs with many
  dependency groups have compounding performance issues (slow compilation +
  expensive rewrite closure).
- [P01](../performance/P01-dfa-state-count.md) -- DFA state counts affect
  a different dimension of codegen size (the dispatch tables), complementing
  A09's focus on the generated rewrite network.
