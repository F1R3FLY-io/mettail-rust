# MSO02: non-recognizable-step

**Severity:** Warning
**Module:** M10 Weighted MSO Logic
**Feature gate:** `weighted-mso`

## What It Detects

- A weighted MSO formula has a decidability tier of `SemiDecidable` (T3) or `Undecidable` (T4), indicating that its `forall x` quantification binds over a body that is not a recognizable step function.
- In restricted MSO (Definition 3.6, Droste & Gastin 2007), universal first-order quantification `forall x. phi` requires that the semantics `[[phi]]` is a recognizable step function -- a function that takes finitely many values. When this condition fails, the formula cannot be compiled to a weighted automaton.

## Example

### Triggering Code

```
language! {
    name: VerifyLang;
    primary: Stmt;

    category Stmt {
        Assign = <ident> "=" Expr;
        Loop   = "while" Expr "{" Block "}";
    }

    // forall x. phi where phi is not a recognizable step function:
    // The body references an unbounded computation (reachability
    // over arbitrary reduction chains).
    predicate terminates:
        forall x. not(exists x'. x ->* x');
    // This is T4 (undecidable): bounded halting is semi-decidable,
    // unbounded halting is undecidable.
}
```

### Diagnostic Output

```
warning[MSO02] (VerifyLang): formula decidability tier Undecidable -- forall x body is not a recognizable step function
  = hint: provide a user proof/assertion or restrict to first-order fragment
```

### Fix

```
// Option 1: Bound the quantification to make it semi-decidable (T3):
predicate terminates_bounded:
    forall x. not(exists x'. x ->k x');  // bounded to k steps

// Option 2: Use the first-order fragment (aperiodic/star-free):
// For weakly bi-aperiodic semirings, K^aper = K^rfo = K^fo
predicate local_progress:
    forall x. exists y. y = x + 1 /\ P_a(y);  // step function

// Option 3: Provide a user proof for the undecidable predicate:
#[assert_pred(proof = "termination_proof.rocq")]
predicate terminates:
    forall x. not(exists x'. x ->* x');
```

## Rationale

- The decidability classification in `symbolic.rs` assigns tiers:
  - T1 (compile-time decidable): structural patterns, finite-domain quantifiers
  - T2 (runtime decidable): Ascent relation queries, finite-state checks
  - T3 (semi-decidable): bounded reachability, bounded halting
  - T4 (undecidable): general halting, unbounded `forall` over infinite domains
- The restricted MSO theorem (Theorem 4.5) guarantees that `forall x. phi` preserves recognizability only when `[[phi]]_V` is a recognizable step function. A step function takes finitely many values as the variable `x` ranges over all positions.
- When `phi` references unbounded computations (e.g., transitive closure `->*`), it takes infinitely many distinct values, violating the step function requirement.
- T3/T4 formulas require special handling: bounded verification with configurable depth limits (T3), or user-provided proofs and runtime monitors (T4).
- The first-order fragment (Section 7, Theorem 7.11) provides a safe alternative: for weakly bi-aperiodic semirings, all FO-definable series are recognizable.

## Related Lints

- [MSO01](MSO01.md) -- Unrestricted universal set: formula-level issue that also produces T3/T4 classification
- [MSO03](MSO03.md) -- Equivalent formulas: equivalence checking requires recognizable formulas
- [PT03](../parity-tree/PT03.md) -- PATA high priority: deep fixpoints can produce non-step function bodies
- [S01](../analysis/safety/S01-safety-violation.md) -- Safety violation: undecidable predicates may mask safety issues
