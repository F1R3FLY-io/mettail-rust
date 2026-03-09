# G35: ground-rewrite-short-circuit

**Severity:** Note
**Category:** grammar
**Feature Gate:** None (always enabled)

## Description

Reports that one or more rewrite rules have a ground (variable-free) LHS
pattern, meaning the rewrite can be evaluated at Ascent initialization time
(iteration 0) without pattern matching or fixpoint scanning. Ground rewrite
results are "seeded" into the `rw_cat` relation at the start of evaluation,
making them immediately available to all downstream rules.

A **ground rewrite** is a rewrite rule whose LHS is a fully concrete term
with no variable positions -- every field is either a literal or a constructor
applied to other ground terms. Because the LHS matches exactly one term
(itself), the rewrite result is statically known at compile time and can be
computed once rather than checked on every iteration.

```
  Ground rewrite evaluation:

  Normal rewrite (per-iteration):
  ┌──────────────────────────────────────┐
  │  iteration 0: scan rw_cat for match  │ -> no match yet
  │  iteration 1: scan rw_cat for match  │ -> ...
  │  iteration k: match found!           │ -> apply rewrite
  └──────────────────────────────────────┘

  Ground rewrite (seeded at init):
  ┌──────────────────────────────────────┐
  │  iteration 0: rw_cat seeded with     │ -> result immediately
  │               ground rewrite result  │    available
  └──────────────────────────────────────┘
```

This optimization (B-CG04) reduces the number of fixpoint iterations needed to
propagate ground rewrite results and eliminates redundant scanning of the
rewrite relation for statically resolvable patterns.

## Trigger Conditions

All of the following must hold:

- The grammar defines at least one rewrite rule.
- At least one rewrite rule has a ground (variable-free) LHS pattern, as
  determined by `rules::generate_ground_rewrite_seeds()`.
- The function successfully generates seed tuples for the ground rewrites.

One diagnostic is emitted per grammar, summarizing the count of ground rewrites
detected.

## Example

### Grammar

```rust
language! {
    name: BoolSimplify,
    types {
        Bool
    },
    terms {
        True  . |- "true"  : Bool;
        False . |- "false" : Bool;
        Not   . b:Bool |- "!" b : Bool;
        And   . a:Bool, b:Bool |- a "&&" b : Bool;
    },
    rewrites {
        // Ground: Not(True) -> False  (LHS is fully concrete)
        Not(True) -> False;
        // Ground: Not(False) -> True  (LHS is fully concrete)
        Not(False) -> True;
        // NOT ground: Not(x) where x is a variable
        // Not(x) -> ... would not be ground
    },
}
```

### Output

```
note[G35] (BoolSimplify): 2 ground-LHS rewrite(s) detected -- results seeded at initialization (B-CG04)
  = hint: ground rewrites produce statically known results; seeding avoids per-iteration scanning
```

## Resolution

No action required. G35 is an informational diagnostic confirming that the
B-CG04 optimization is active. The ground rewrite seeds are generated
automatically and provide a strict improvement over the default per-iteration
scanning behavior.

If a ground rewrite is unexpectedly detected (or not detected):

1. **Verify LHS groundness.** Check that the rewrite rule's LHS contains no
   variable positions. A constructor applied to variables is not ground.

2. **Inspect the generated seeds.** Set `PRATTAIL_LINT_VERBOSE=1` and examine
   the generated Ascent file to verify that the seed tuples match expectations.

## Hint Explanation

The hint **"ground rewrites produce statically known results; seeding avoids
per-iteration scanning"** explains the optimization's mechanism: because the
LHS matches exactly one term, the result is computable at compile time. Seeding
the result at iteration 0 means downstream rules can consume it immediately
rather than waiting for the fixpoint scanner to discover the match.

## Related Lints

- [G38](G38-bloom-filter-rw-congruence-guard.md) -- Bloom filter rewrite
  congruence guard. Another codegen optimization for rewrite rules that uses
  discriminant pre-checks to skip non-participating terms.
- [G41](G41-normalize-dedup-active.md) -- Normalize dedup active. Hash-based
  deduplication guards that complement ground rewrite seeding.
- [G42](G42-eq-strata-analysis.md) -- Equation stratification and rule fusion.
  Stratification analysis that determines the order in which rewrite results
  propagate through the dependency graph.
- [C-AP03](../codegen-antipattern/C-AP03-deep-congruence-chains.md) -- Deep
  congruence chains. Ground rewrites bypass congruence chains entirely.
