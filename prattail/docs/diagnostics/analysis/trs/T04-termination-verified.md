# T04: termination-verified

**Severity:** Note
**Category:** analysis/trs
**Feature Gate:** `trs-analysis`

## Description

Confirms that the grammar's term rewriting system (TRS) is **terminating**
(strongly normalizing): every reduction sequence is finite, and every term has a
normal form reachable in finitely many steps.

A TRS R is terminating when there is no infinite chain:

    t₀ ->_R t₁ ->_R t₂ ->_R t₃ ->_R ...

The analysis establishes this by computing the **dependency graph** of R,
decomposing it into strongly connected components (SCCs), and verifying that
each SCC admits a decreasing measure -- a well-founded ordering that strictly
decreases between dependency pairs within the SCC.

```
  Dependency Graph (all SCCs verified)
  ════════════════════════════════════

  ┌─────────────┐     ┌─────────────┐     ┌─────────────┐
  │   SCC 0     │     │   SCC 1     │     │   SCC 2     │
  │  Rules 0,1  │────>│  Rules 2,3  │────>│  Rule 4     │
  │  measure: |t|│     │  measure:   │     │  (no cycle) │
  │  (size)     │     │  KBO weight │     │  trivially  │
  └─────────────┘     └─────────────┘     │  terminating│
        ✓                   ✓             └─────────────┘
                                                ✓
                        all SCCs ✓  =>  T04 fires
```

When every SCC in the dependency graph has been verified to possess a decreasing
ordering witness, T04 fires. Singleton SCCs without self-loops are trivially
terminating (the dependency pair cannot cycle). Non-trivial SCCs require an
explicit measure witness (term size, Knuth-Bendix ordering, lexicographic path
ordering, or polynomial interpretation).

When T04 fires together with [T02](T02-confluence-verified.md), the TRS is
**convergent** (also called **canonical** or **complete**): every term has a
**unique** normal form, and that normal form can be computed by any reduction
strategy. This is the strongest guarantee for a rewriting-based grammar system.

## Trigger Conditions

All of the following must hold:

- The `trs-analysis` feature is enabled at compile time.
- A `TerminationResult` is available in the lint context.
- The result is `Terminating` (all SCCs in the dependency graph have verified
  decreasing measures).

Exactly one T04 diagnostic is emitted per grammar.

## Example

### Grammar

```rust
language! {
    name: ArithNormalize,
    types {
        ![i32] as Expr
    },
    terms {
        Num . n:Expr |- n : Expr;
        Add . a:Expr, b:Expr |- a "+" b : Expr ![a + b] fold;
        Mul . a:Expr, b:Expr |- a "*" b : Expr ![a * b] fold;
        Neg . a:Expr |- "-" a : Expr ![{ -a }];

        // Simplification rewrites (all terminating):
        // -(-(x))  -> x        (size decreases by 2)
        // x + 0    -> x        (size decreases by 2)
        // 0 + x    -> x        (size decreases by 2)
        // x * 1    -> x        (size decreases by 2)
        // 1 * x    -> x        (size decreases by 2)
        // x * 0    -> 0        (size decreases)
        // 0 * x    -> 0        (size decreases)
    },
}
```

### Output

```
note[T04] (ArithNormalize): all SCCs have decreasing measures — system terminates
```

## Resolution

No action is required. T04 is an informational note confirming a desirable
property. The grammar's rewriting rules always reach a normal form in finitely
many steps.

The combination of T02 (confluence) and T04 (termination) guarantees
**convergence**: every input term has exactly one normal form, and any reduction
strategy will find it. This is the ideal state for a grammar transformation
pipeline.

## Hint Explanation

This lint has no hint. The system is terminating and no corrective action is
needed.

## Related Lints

- [T03](T03-non-terminating-cycle.md) -- The negative counterpart: emitted when
  at least one SCC lacks a decreasing measure. T03 and T04 are mutually
  exclusive (T04 fires only when zero T03 warnings exist).
- [T02](T02-confluence-verified.md) -- Confluence verification. When both T02
  and T04 fire, the TRS is convergent (canonical).
- [T01](T01-non-joinable-critical-pair.md) -- If T04 fires but T01 also fires,
  the system terminates but is not confluent -- Knuth-Bendix completion can
  potentially be applied (since the ordering exists) to add rules that restore
  confluence.
