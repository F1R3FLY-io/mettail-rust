# G31: subsumed-equations-eliminated

**Severity:** Note
**Category:** Grammar Structure (macro phase)
**Feature Gate:** (none -- always active)

## Description

Reports the total number of equations eliminated from Ascent codegen via
**subsumption analysis**. This is a **summary-level** lint that aggregates
the results of the pattern trie's `detect_subsumption()` pass and the
`compute_subsumed_equations()` function. It fires once per grammar when at
least one equation has been eliminated.

Subsumption elimination works as follows: for each pair of equations where
one LHS pattern is strictly more general than the other, the more specific
equation is marked as subsumed and excluded from Ascent codegen. The general
equation already handles all cases that the specific equation would match,
so the elimination is semantics-preserving.

```
  Before elimination:             After elimination:
  ┌──────────────────────────┐    ┌──────────────────────────┐
  │ eq_1: F(X, Y) = G(X, Y) │    │ eq_1: F(X, Y) = G(X, Y) │
  │ eq_2: F(A, A) = G(A, A) │    │ eq_2: (eliminated)       │
  │ eq_3: F(B, C) = G(B, C) │    │ eq_3: (eliminated)       │
  └──────────────────────────┘    └──────────────────────────┘
  eq_1 subsumes eq_2 and eq_3     G31: "2 subsumed equation(s) eliminated"
```

The elimination reduces the Ascent fixpoint computation's working set: fewer
rules mean fewer tuples generated per iteration, fewer joins, and faster
convergence.

## Trigger Conditions

All of the following must hold:

- The grammar defines at least one equation.
- The `compute_subsumed_equations()` function identifies at least one
  equation that is subsumed by a more general equation.

One diagnostic is emitted per grammar (summary level).

## Example

### Grammar

```rust
language! {
    name: Simplify,
    types { ![Expr] as Expr },
    terms {
        Add  . a:Expr, b:Expr |- a "+" b : Expr;
        Zero . |- "0" : Expr;
    },
    equations {
        // General: any X + 0 = X
        AddZeroR . a:Expr |- Add(a, Zero()) = a;
        // Specific: 0 + 0 = 0 (subsumed by AddZeroR)
        ZeroZero . |- Add(Zero(), Zero()) = Zero();
        // Specific: another subsumed case
        AddSelf  . a:Expr |- Add(a, Zero()) = a;
    },
}
```

### Output

```
note[G31] (Simplify): 2 subsumed equation(s) eliminated from Ascent codegen
  = hint: subsumed equations are redundant and have been removed from Ascent codegen
```

## Resolution

No action is required. This is an informational diagnostic confirming that
the compiler has successfully optimized the equation set. The individual
eliminations are reported by [G26](G26-equation-subsumed.md).

The diagnostic is useful for:

1. **Monitoring grammar complexity.** A high elimination count suggests the
   grammar has many redundant equations that could be manually simplified.

2. **Validating optimization effectiveness.** The count confirms that the
   subsumption analysis is working and reducing the Ascent codegen workload.

## Hint Explanation

> subsumed equations are redundant and have been removed from Ascent codegen

The hint confirms that the elimination is safe and reduces generated code.
Each eliminated equation would have generated Ascent rules that produce
tuples already covered by a more general equation's rules. Removing them
reduces:

- Generated Rust code size (fewer `ascent!` rules).
- Fixpoint iteration count (fewer redundant tuple insertions).
- Compilation time (fewer rules for the Rust compiler to process).

## Related Lints

- [G26](G26-equation-subsumed.md) -- per-equation subsumption diagnostic
  (fires for each individual eliminated equation)
- [G27](G27-rule-subsumption-candidate.md) -- subsumption candidates that
  are NOT auto-eliminated (rewrites and mixed pairs)
- [G25](G25-cancellation-pair-detected.md) -- a different equation
  elimination mechanism (cancellation pair suppression)
