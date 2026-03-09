# A04: large-equivalence-class

**Severity:** Warning
**Category:** Ascent / Equivalence Class Analysis
**Feature Gate:** none (always active)

## Description

Detects constructors that appear in **three or more** equation/rewrite
dependency groups, indicating a risk of **equivalence class explosion** during
Ascent fixpoint evaluation.  Each dependency group represents a set of
constructor labels connected by shared equations or rewrites.  A constructor
appearing in many groups acts as a hub, causing its equivalence class to merge
with other classes through transitive closure.

In Ascent's fixpoint semantics, an equivalence class records all terms that
are provably equal via the grammar's equations.  When constructor `C` appears
in groups `G1`, `G2`, and `G3`, the classes of all terms involving `C` must
be unified across all three groups.  This can trigger **exponential growth**
in the number of derived equalities:

```
  Constructor "Add" in 4 groups:
  ┌────────────────────┐
  │ G1: {Add, Sub}     │ commutativity
  │ G2: {Add, Mul}     │ distributivity
  │ G3: {Add, Neg}     │ inverse
  │ G4: {Add, Zero}    │ identity
  └────────────────────┘
         │
         v
  Transitive merge: all terms reachable from
  Add via any axiom chain are equated, causing
  cross-group unification of equivalence classes.
```

The explosion manifests as:

- Rapidly growing Ascent relation sizes (memory).
- Increasing iteration counts per fixpoint round (time).
- Potentially non-terminating fixpoint if the equivalence classes keep
  growing without reaching a stable state.

## Trigger Conditions

All of the following must hold:

- The grammar defines semantic dependency groups (at least one equation or
  rewrite exists).
- A constructor label appears in **three or more** distinct dependency groups.

One diagnostic is emitted per constructor exceeding the threshold.

## Example

### Grammar

```rust
language! {
    name: RichArith,
    types { ![i32] as Expr },
    terms {
        Num  . |- <int>          : Expr;
        Add  . a:Expr, b:Expr   |- a "+" b : Expr;
        Mul  . a:Expr, b:Expr   |- a "*" b : Expr;
        Sub  . a:Expr, b:Expr   |- a "-" b : Expr;
    },
    equations {
        |- Add(X, Y) = Add(Y, X);       // G1: {Add}
        |- Add(X, Mul(Y, Z)) = ...;     // G2: {Add, Mul}
        |- Add(X, Sub(Y, Z)) = ...;     // G3: {Add, Sub}
    },
}
```

### Output

```
warning[A04] (RichArith): constructor `Add` appears in 3 equation/rewrite groups (3 equation group(s)) — potential equivalence class explosion during Ascent fixpoint evaluation
  = hint: this constructor is referenced by many equations/rewrites, which can cause equivalence class explosion during Ascent fixpoint evaluation; consider reducing the number of equations involving this constructor, or simplifying equational axioms (e.g., removing redundant commutativity/associativity declarations)
```

When multiple constructors are flagged, the grouper consolidates them:

```
warning[A04] (RhoCalc): 3 constructors appear in 3+ equation/rewrite groups (risk of equivalence class explosion): Name(NQuote), Proc(PPar, PNew)
```

## Resolution

1. **Reduce axiom overlap.**  Examine whether all dependency groups truly need
   the same constructor.  Often, distributivity or absorption axioms can be
   reformulated to avoid referencing a shared hub constructor, reducing the
   cross-group unification pressure.

2. **Remove redundant axioms.**  If the same equational consequence can be
   derived through fewer axioms, eliminating redundant ones reduces the number
   of groups a constructor participates in.  For instance, if commutativity +
   associativity already imply a distributivity axiom, the latter is redundant.

3. **Partition into strata.**  Split the equational reasoning into independent
   phases (strata) that run sequentially rather than simultaneously.  This
   prevents cross-group class merging during any single fixpoint phase.

4. **Accept the warning.**  For inherently rich algebraic structures (rings,
   lattices, etc.), constructors like `+` and `*` will naturally appear in
   many axiom groups.  Verify that the fixpoint converges in acceptable time
   and suppress with `PRATTAIL_LINT_LEVEL=error`.

## Hint Explanation

The hint explains the mechanism behind the warning: a constructor referenced
by many equations/rewrites becomes a **merge hub** in the equivalence class
structure.  The suggested mitigations target the root cause:

- **Reducing equations** directly lowers the group participation count.
- **Simplifying axioms** (e.g., removing a redundant commutativity when
  associativity already provides the needed reordering) eliminates
  unnecessary cross-group links.

## Related Lints

- [A01](A01-fixpoint-non-convergence.md) -- Unbounded term growth can amplify
  equivalence class explosion by continuously generating new terms that must
  be classified.
- [A07](A07-fixpoint-iteration-anomaly.md) -- High dependency group count and
  size are correlated with both A04 and A07 conditions.
- [A08](A08-equation-subsumes-rewrite.md) -- If an equation subsumes a rewrite
  for the same constructor, removing the redundant rewrite reduces the group
  count.
