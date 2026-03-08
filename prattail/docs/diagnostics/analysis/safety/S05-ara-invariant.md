# S05: ara-invariant

**Severity:** Note
**Category:** analysis/safety
**Feature Gate:** `wpds-ara`

## Description

Reports the results of Algebraic Program Analysis with Recurrences (ARA)
applied to the grammar's WPDS model. ARA lifts the WPDS weight domain from
a scalar semiring to an affine relation domain, enabling the discovery of
loop invariants and recurrence relations over parser state variables.

The intuition is that many grammar properties can be expressed as affine
constraints on category-level counters. For example, "the nesting depth of
parenthesized expressions never exceeds the nesting depth of braces" is an
affine invariant involving two counters. ARA discovers such invariants
automatically by analyzing the WPDS transition rules as affine transformations
over a vector space of dimension *dim*.

Formally, an ARA weight is a pair (A, b) where A is a dim x dim matrix over
the tropical semiring and b is a dim-vector. The affine transformation
represented by (A, b) maps a state vector x to:

  x' = A otimes x oplus b

where otimes is tropical matrix-vector multiplication (min-plus) and oplus is
component-wise minimum. The ARA analysis computes the transitive closure of
these transformations along all WPDS paths, yielding invariants of the form:

  x_i <= a_i1 * x_1 + a_i2 * x_2 + ... + a_in * x_n + b_i

Each such invariant constrains the relationship between parser state variables
(e.g., nesting depths, rule invocation counts, category entry counts) at
specific program points.

The S05 diagnostic reports:
- The dimension of the ARA weight domain (number of tracked state variables).
- The number of invariants discovered.

### ARA weight domain structure

```
  State vector x in R^dim (tropical):

    x = [ x_1, x_2, ..., x_dim ]^T

  Affine transformation (A, b):

    ┌                         ┐   ┌     ┐   ┌     ┐
    │ a_11  a_12  ...  a_1d   │   │ x_1 │   │ b_1 │
    │ a_21  a_22  ...  a_2d   │   │ x_2 │   │ b_2 │
    │  .     .    '.    .     │ . │  .  │ + │  .  │
    │ a_d1  a_d2  ...  a_dd   │   │ x_d │   │ b_d │
    └                         ┘   └     ┘   └     ┘

  Semiring operations:
    oplus:  (A1, b1) oplus (A2, b2) = (min(A1, A2), min(b1, b2))
    otimes: (A1, b1) otimes (A2, b2) = (A1 . A2, A1 . b2 + b1)

  where . is tropical matrix multiplication (min-plus).
```

## Trigger Conditions

A note is emitted when **all** of the following conditions hold:

1. The `wpds-ara` feature is enabled.
2. The pipeline's ARA module (`ara.rs`) has been executed, producing an
   `AraAnalysis`.

The lint is silent when:
- The `wpds-ara` feature is not enabled.
- No `AraAnalysis` is available (analysis was not run).

Note that S05 fires even when zero invariants are discovered; in that case,
the message reports `0 invariant(s) discovered`, indicating that the analysis
ran but the grammar's structure did not yield any non-trivial affine
constraints at the analyzed dimension.

## Example

### Grammar

```
language! {
    name: NestedLang;
    primary: Expr;

    category Expr {
        native_type: Integer;
        IntLit  = <int>;
        Add     = Expr "+" Expr;
        Paren   = "(" Expr ")";
        Bracket = "[" Expr "]";
        Brace   = "{" Expr "}";
    }
}
```

The ARA analysis tracks three nesting counters (parentheses, brackets, braces)
as a 3-dimensional weight domain. It discovers invariants relating these
counters, such as the trivial invariant that each counter is non-negative.

### Output

```
note[S05] (NestedLang): ARA weight domain: dimension=3, 2 invariant(s) discovered
```

The invariants might include:
- `Cat_A: x >= 0` (parenthesis depth is non-negative)
- `Cat_B: y <= 1` (bracket depth bounded by 1 in this sub-grammar)

## Resolution

S05 is informational. The discovered invariants can be used for:

1. **Grammar validation.** If an expected invariant is missing, the grammar
   may have a structural issue that prevents the property from holding.

2. **Optimization.** Known invariants can be used to simplify the parser's
   dispatch logic. For example, if a counter is provably bounded, the parser
   can use a fixed-size buffer instead of a dynamic stack.

3. **Safety strengthening.** ARA invariants can be fed into the safety
   verification (S01/S02) as additional constraints on the bad-state
   specification, making the safety check more precise.

4. **Debugging.** If the dimension is unexpectedly large or small, it may
   indicate that the ARA analysis is tracking too many or too few state
   variables. Review the grammar for unnecessary nesting constructs or
   missing category structure.

## Hint Explanation

S05 does not include a hint, as it is purely informational. The dimension and
invariant count provide a concise summary of the ARA analysis scope and
results.

## Related Lints

- [S04](S04-ewpds-merge-site.md) -- EWPDS merge sites where ARA applies affine transformations at call boundaries
- [S01](S01-safety-violation.md) -- Safety verification that can leverage ARA invariants for stronger properties
- [S06](S06-algebraic-summary.md) -- Tarjan path expression summary; the SCC structure determines the shape of ARA recurrences
