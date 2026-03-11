# MSO01: unrestricted-universal-set

**Severity:** Warning
**Module:** M10 Weighted MSO Logic
**Feature gate:** `weighted-mso`

## What It Detects

- A weighted MSO formula uses unrestricted universal set quantification (`ForallSecond` / `forall X. phi`), placing it in the `Full` MSO class rather than the `Restricted` or `RestrictedExistential` class.
- Full MSO formulas are not guaranteed to define recognizable formal power series, meaning they cannot always be compiled to weighted automata. This pushes the formula's decidability tier to T3 (semi-decidable) or T4 (undecidable).

## Example

### Triggering Code

```
language! {
    name: LogicLang;
    primary: Formula;

    category Formula {
        And  = Formula "/\\" Formula;
        Or   = Formula "\\/" Formula;
        Not  = "!" Formula;
        Atom = <ident>;
    }

    // Unrestricted universal set quantification:
    // "for all sets X of positions, if X contains position 0,
    //  then X contains all positions" -- this is full MSO
    predicate everywhere:
        forall X. (0 in X) -> (forall x. x in X);
}
```

### Diagnostic Output

```
warning[MSO01] (LogicLang): formula uses unrestricted forall X (full MSO -- not recognizable, T3/T4)
  = hint: restrict to exists X quantification or bounded forall x for decidability
```

### Fix

```
// Option 1: Use existential set quantification instead:
predicate exists_cover:
    exists X. (0 in X) /\ (forall x. x in X);

// Option 2: Use bounded first-order quantification (restricted MSO):
predicate all_positions:
    forall x. P_a(x);  // forall x is OK if body is a recognizable step function

// Option 3: If full MSO is necessary, provide a user proof/assertion:
#[assert_decidable]
predicate everywhere:
    forall X. (0 in X) -> (forall x. x in X);
```

## Rationale

- The weighted Buchi-Elgot-Trakhtenbrot theorem (Droste & Gastin 2007, Theorem 3.7) establishes that recognizable formal power series `K^rec<<A*>>` coincide exactly with restricted weighted MSO-definable series `K^rmso<<A*>>`. Full MSO with `forall X` breaks this correspondence.
- The `classify_formula()` function checks for `ForallSecond` variants. Any formula containing `ForallSecond` is classified as `MsoFormulaClass::Full`, which maps to T3/T4 decidability via `check_decidability()`.
- For locally finite commutative semirings, equivalence of restricted MSO sentences is decidable (Corollary 6.5). Full MSO loses this decidability guarantee.
- In predicated types, unrestricted `forall X` quantification over sets of positions corresponds to predicates that reason about "all possible subsets" of the input -- a fundamentally more powerful (and less decidable) operation than reasoning about individual positions.

## Related Lints

- [MSO02](MSO02.md) -- Non-recognizable step: a more specific violation where `forall x` has a non-step body
- [MSO03](MSO03.md) -- Equivalent formulas: decidable equivalence requires restricted MSO sentences
- [SYM01](../symbolic/SYM01.md) -- Unsatisfiable guard: the guard-level consequence of undecidable formulas
- [PT01](../parity-tree/PT01.md) -- PATA emptiness: tree-level emptiness that connects to MSO satisfiability
