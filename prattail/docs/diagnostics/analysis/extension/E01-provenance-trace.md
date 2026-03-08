# E01: provenance-trace

**Severity:** Note
**Category:** analysis/extension
**Feature Gate:** `provenance`

## Description

Reports the results of how-provenance analysis over the grammar's derivation structure. Provenance tracking answers not just WHETHER a parse derivation exists but HOW it was constructed -- which base facts (grammar rules, axioms, input tokens) contributed to each derived fact, and in what combinations.

The provenance analysis computes polynomials in the semiring `N[X]` (natural number polynomials over a set of provenance variables `X`). Each polynomial encodes all possible derivation paths for a fact, with coefficients tracking multiplicity and variables identifying the contributing base facts.

E01 fires when the analysis has computed at least one provenance polynomial, reporting the total count as an informational summary.

### The Provenance Semiring N[X]

The carrier set of `N[X]` consists of multivariate polynomials with natural number coefficients over provenance variables `X = {x_1, x_2, ..., x_n}`, where each `x_i` identifies a base fact (e.g., a grammar rule application or input token match).

**Semiring operations:**

| Operation | Symbol | Semantics | Provenance meaning |
|-----------|--------|-----------|-------------------|
| Addition | p + q | Polynomial addition | Union of derivation alternatives |
| Multiplication | p x q | Polynomial multiplication | Cross-product of derivation steps |
| Zero | 0 | Zero polynomial | No derivation exists |
| One | 1 | Constant polynomial 1 | Trivial derivation (no base facts needed) |

**Provenance hierarchy:**

```
              N[X]  (how-provenance)
               |
     ┌─────────┼──────────┐
     v         v          v
  Powerset  Boolean    Tropical    Viterbi
  (why)     (which)    (cost)      (confidence)
     |         |          |            |
     v         v          v            v
  All trees  Yes/No   Cheapest    Most confident
```

Every provenance type is obtained by a semiring homomorphism from `N[X]`:
- **Which-provenance** (BooleanWeight): `h(p) = (p != 0)` -- is the fact derivable?
- **Why-provenance** (Powerset of monomials): `h(p) = support(p)` -- which combinations suffice?
- **Cost-provenance** (TropicalWeight): `h(p) = min-cost monomial` -- cheapest derivation.
- **Confidence-provenance** (ViterbiWeight): `h(p) = max-confidence monomial` -- most confident derivation.

### Polynomial Example

Given base facts `x_1` (rule `IntLit`), `x_2` (rule `IntAdd`), `x_3` (rule `IntNeg`):

```
provenance(result) = x_1 x_2 x_1 + x_3 x_1
                   = x_1^2 x_2 + x_1 x_3
```

This polynomial tells us the result has two derivations:
1. Apply `IntLit` twice and `IntAdd` once (e.g., `1 + 2`).
2. Apply `IntNeg` once and `IntLit` once (e.g., `-3`).

## Trigger Conditions

E01 fires when all of the following hold:

- The `provenance` feature gate is enabled.
- The pipeline has computed a `ProvenanceAnalysis` result.
- The `provenance_traces` field is non-empty (at least one polynomial was computed).
- A single E01 diagnostic is emitted with the count of computed polynomials.

If no provenance traces are produced (e.g., the grammar has no derivation paths to analyze), E01 is silent.

## Example

### Grammar

```
language! {
    name: ArithLang;
    primary: Expr;

    category Expr {
        native_type: Integer;

        NumLit   = <int>;
        Add      = Expr "+" Expr;
        Mul      = Expr "*" Expr;
        Neg      = "-" Expr;
        Paren    = "(" Expr ")";
    }
}
```

The provenance analysis tracks how each parse fact is derived from the grammar's base rules.

### Output

```
note[E01] (ArithLang): how-provenance: 5 polynomial(s) computed
```

## Resolution

No action is required. E01 is an informational diagnostic confirming that provenance analysis completed successfully. The polynomial count indicates the scope of the analysis -- more polynomials means more derivation paths were tracked.

The computed polynomials are available programmatically for downstream analyses:
- **Debugging ambiguity:** If a fact has a polynomial with multiple monomials, it has multiple derivation paths (potential ambiguity).
- **Cost optimization:** Applying the TropicalWeight homomorphism extracts the cheapest derivation.
- **Lineage tracking:** Each monomial identifies exactly which base facts contribute to the derivation.

## Related Lints

- [E02](E02-cra-cost-anomaly.md) -- CRA cost anomaly detection. Provenance polynomials feed into CRA register initialization; anomalous register values may trace back to specific provenance paths.
- [P06](../P06-analysis-pipeline-cost.md) -- Reports total analysis phase time, which includes provenance computation when the feature is enabled.
