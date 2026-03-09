# G38: bloom-filter-rw-congruence-guard

**Severity:** Note
**Category:** grammar
**Feature Gate:** None (always enabled)

## Description

Reports that rewrite congruence rule groups have been guarded by compile-time
discriminant pre-checks (the A-RT04 optimization). For each congruence group
that processes rewrite rules, the codegen determines which constructor
discriminants actually participate in the group's equations. A `matches!()`
guard is generated that skips the congruence rule entirely for terms whose
discriminant is not in the participating set.

This optimization arises from the observation that congruence rules are
generated for every category-level field combination, but only a subset of
constructors within a category actually participate in rewrite equations. The
discriminant pre-check avoids entering the congruence evaluation path (which
involves pool allocation and fixpoint iteration) for terms that cannot
possibly match any rewrite LHS.

```
  Discriminant pre-check flow:

  ┌───────────────────────────────┐
  │  term t enters rw congruence  │
  │                               │
  │  matches!(t, Cat::Add(..)     │
  │           | Cat::Mul(..))     │
  │  ├── yes -> evaluate pool     │
  │  │         congruence rules   │
  │  │                            │
  │  └── no  -> skip (no rewrite  │
  │             touches Neg, Num) │
  └───────────────────────────────┘

  Participating constructors:  {Add, Mul}  (2 of 4)
  Skipped constructors:        {Neg, Num}  (2 of 4)
```

The bloom filter terminology is historical: the original design used a runtime
bloom filter, but the current implementation generates exact `matches!()` guards
verified at compile time with `debug_assert!` for zero false negatives. The
diagnostic retains the "bloom filter" name for continuity with the optimization
catalog (A-RT04).

## Trigger Conditions

All of the following must hold:

- The grammar has at least one rewrite rule.
- At least one rewrite congruence group (a category-to-category field reference
  that generates congruence rules) has a subset of constructors that participate
  in rewrites.
- The `generate_consolidated_simple_congruence()` function successfully builds
  a guarded congruence rule.
- Diagnostic emission is enabled (the `emit_diagnostics` flag is true).

One diagnostic is emitted per grammar, summarizing the number of guarded groups
and total participating constructors.

## Example

### Grammar

```rust
language! {
    name: ArithSimp,
    types {
        ![i32] as Expr
    },
    terms {
        Num  . n:Expr |- n           : Expr;
        Add  . a:Expr, b:Expr |- a "+" b : Expr;
        Mul  . a:Expr, b:Expr |- a "*" b : Expr;
        Neg  . a:Expr |- "-" a       : Expr;
    },
    rewrites {
        // Only Add and Mul participate in rewrites
        Add(Num(0), x) -> x;
        Mul(Num(1), x) -> x;
    },
}
```

### Output

```
note[G38] (ArithSimp): 1 rewrite congruence group(s) guarded by discriminant pre-check (A-RT04) -- 2 constructor(s) participate; non-participating terms skipped before pool evaluation
  = hint: compile-time bloom filter verified zero false negatives; generated matches!() guard uses exact discriminant comparison
```

## Resolution

No action required. G38 is an informational diagnostic confirming that the
A-RT04 optimization is active. The discriminant pre-check is generated
automatically and provides a strict improvement by reducing unnecessary
congruence rule evaluations.

If the diagnostic reports fewer guarded groups or participating constructors
than expected:

1. **Check rewrite rule coverage.** Ensure that the rewrite rules reference
   the expected constructors. A rewrite that uses a variable pattern (`x -> y`)
   rather than a constructor pattern (`Add(x, y) -> ...`) will not produce
   a discriminant guard.

2. **Inspect the generated code.** Set `PRATTAIL_LINT_VERBOSE=1` and examine
   the generated Ascent file to verify that the `matches!()` guards include
   the expected constructors.

## Hint Explanation

The hint **"compile-time bloom filter verified zero false negatives; generated
matches!() guard uses exact discriminant comparison"** confirms two properties:

- **Zero false negatives**: every constructor that participates in a rewrite
  equation is included in the guard. No valid rewrite will be skipped.
- **Exact discriminant comparison**: the guard uses Rust's `matches!()` macro
  with exact constructor patterns, not a probabilistic bloom filter. There are
  zero false positives in the guard itself (though the term may still fail to
  match the full rewrite pattern after passing the discriminant check).

## Related Lints

- [G35](G35-ground-rewrite-short-circuit.md) -- Ground rewrite short-circuit.
  Complements G38: ground rewrites are seeded at init, while G38 guards non-
  ground rewrite congruence.
- [G41](G41-normalize-dedup-active.md) -- Normalize dedup active. Hash-based
  dedup guards that reduce duplicate congruence rule firings.
- [G42](G42-eq-strata-analysis.md) -- Equation stratification. Controls the
  order in which congruence groups are evaluated.
- [C-AP05](../codegen-antipattern/C-AP05-clone-storm.md) -- Clone storm.
  Discriminant pre-checks reduce the number of congruence firings, mitigating
  clone storm impact for non-participating constructors.
