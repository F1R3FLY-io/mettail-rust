# How-Provenance Tracking

| Property       | Value                                  |
|----------------|----------------------------------------|
| Feature gate   | `provenance`                           |
| Source file    | `prattail/src/provenance.rs` (~628 lines) |
| Pipeline phase | Post-analysis diagnostic enrichment    |
| Lint codes     | E01 (missing provenance)               |

## Rationale

Standard analysis tells us WHETHER a fact is derivable (Boolean semiring) or HOW MANY derivations exist (counting semiring). How-provenance goes further: it tracks WHICH combinations of base facts contribute to each derivation, represented as polynomials with natural number coefficients over base-fact variables. This is the `N[X]` polynomial semiring from Green, Karvounarakis & Tannen (2007). In PraTTaIL, provenance polynomials record which grammar rules participate in each derivation, enabling precise attribution of parse results to their contributing rules and actionable diagnostics when rules are missing.

## Theoretical Foundations

**Definition (Provenance Semiring N[X]).** The how-provenance semiring has carrier set `N[X]` -- multivariate polynomials with natural number coefficients over indeterminates `X` (base facts). The semiring operations are:

- `plus` (union): polynomial addition -- combines derivation alternatives
- `times` (conjunction): polynomial multiplication -- combines derivation steps
- `zero`: the zero polynomial `0` -- no derivation exists
- `one`: the constant polynomial `1` -- trivial derivation (no base facts needed)

**Definition (Monomial).** A monomial `m = x_1^{a_1} . x_2^{a_2} . ... . x_n^{a_n}` records a specific combination of base facts with multiplicities. The degree is `sum(a_i)`. The empty product (no variables) is the constant `1`.

**Theorem (Universal Semiring, Green et al. 2007).** `N[X]` is the universal semiring: for any commutative semiring `S` and valuation `v: X -> S`, there exists a unique homomorphism `h_v: N[X] -> S` extending `v`. This means provenance polynomials can be projected to any target semiring:
- `h_v` to `BooleanWeight`: which-provenance (is the fact derivable?)
- `h_v` to `CountingWeight`: counting-provenance (how many derivations?)
- `h_v` to `TropicalWeight`: cost-provenance (cheapest derivation)
- `h_v` to `ViterbiWeight`: confidence-provenance (most confident derivation)

**Definition (Provenance Projections).**
- `to_boolean(p)`: `p != 0` (which-provenance)
- `to_counting(p)`: `sum of all coefficients` (total derivation count)
- `evaluate(p, v)`: the unique homomorphism from `N[X]` to any target semiring `S` given valuation `v: X -> S`

### References

1. Green, T.J., Karvounarakis, G. & Tannen, V. (2007). "Provenance semirings." *PODS*.
2. Green, T.J. (2011). "Containment of conjunctive queries on annotated relations." *Theory of Computing Systems*, 49(2).
3. Deutch, D. et al. (2014). "Provenance for natural language queries." *VLDB*.

## Algorithm Pseudocode

### 1. Polynomial Addition (Union of Alternatives)

```
FUNCTION plus(p1, p2):
    result := copy(p1.terms)
    FOR EACH (monomial, coefficient) in p2.terms:
        result[monomial] := result.get(monomial, 0) + coefficient
    remove zero-coefficient entries from result
    RETURN ProvenanceWeight(result)
```

### 2. Polynomial Multiplication (Conjunction of Steps)

```
FUNCTION times(p1, p2):
    result := empty map
    FOR EACH (m1, c1) in p1.terms:
        FOR EACH (m2, c2) in p2.terms:
            product_mono := monomial_multiply(m1, m2)
            result[product_mono] := result.get(product_mono, 0) + c1 * c2
    remove zero-coefficient entries from result
    RETURN ProvenanceWeight(result)
```

### 3. Homomorphic Evaluation

```
FUNCTION evaluate(polynomial, valuation: X -> W):
    result := W::zero()
    FOR EACH (monomial, coefficient) in polynomial.terms:
        // Evaluate monomial: product of variable valuations^exponents
        mono_val := W::one()
        FOR EACH (var, exponent) in monomial.factors:
            var_val := valuation(var)
            FOR i := 0 TO exponent - 1:
                mono_val := mono_val OTIMES var_val

        // Multiply by coefficient (repeated addition)
        term_val := W::zero()
        FOR i := 0 TO coefficient - 1:
            term_val := term_val OPLUS mono_val

        result := result OPLUS term_val
    RETURN result
```

## Complexity Analysis

| Operation           | Time              | Space            |
|---------------------|-------------------|------------------|
| `plus`              | O(T_1 + T_2)      | O(T_1 + T_2)    |
| `times`             | O(T_1 . T_2)      | O(T_1 . T_2)    |
| `evaluate`          | O(T . D . E)      | O(1)             |
| `to_boolean`        | O(1)              | O(1)             |
| `to_counting`       | O(T)              | O(1)             |
| `all_variables`     | O(T . V)          | O(V)             |
| `num_alternatives`  | O(1)              | O(1)             |

Where T = number of terms (monomials), T_1/T_2 = terms in each operand, D = max monomial degree, E = max exponent, V = distinct variables.

## Provenance Type Hierarchy

```
  ┌──────────────────────────────────────────────────────────┐
  │                  Provenance Semiring N[X]                  │
  │              (most informative — tracks HOW)              │
  │                                                          │
  │  homomorphism        homomorphism        homomorphism    │
  │       │                   │                   │          │
  │       ▼                   ▼                   ▼          │
  │  ┌──────────┐    ┌──────────────┐    ┌──────────────┐   │
  │  │ Counting │    │   Tropical   │    │   Viterbi    │   │
  │  │ N[X]→N   │    │   N[X]→R⁺   │    │  N[X]→[0,1]  │   │
  │  │(#derivs) │    │ (min cost)   │    │(max confid.) │   │
  │  └─────┬────┘    └──────────────┘    └──────────────┘   │
  │        │                                                 │
  │        ▼                                                 │
  │  ┌──────────┐                                            │
  │  │ Boolean  │                                            │
  │  │ N[X]→{0,1}                                           │
  │  │ (exists?) │                                           │
  │  └──────────┘                                            │
  │  (least informative — tracks WHETHER)                    │
  └──────────────────────────────────────────────────────────┘
```

## Polynomial Algebra Diagram

```
  Example: (x₁ + x₂) ⊗ (x₃ + x₄)

  x₁ ─┐                 x₃ ─┐
      ├─ ⊕ ─┐              ├─ ⊕ ─┐
  x₂ ─┘     │          x₄ ─┘     │
             │                     │
             └──────── ⊗ ─────────┘
                       │
                       ▼
              x₁·x₃ + x₁·x₄ + x₂·x₃ + x₂·x₄
              (4 monomials, 4 derivation alternatives)
```

## PraTTaIL Integration

### Pipeline Bridge Functions

- **`track_from_bundle(all_syntax, categories)`** -- For each rule in `all_syntax`, creates a single-variable provenance polynomial (the rule label as a `ProvenanceVar`), capturing base-level how-provenance. Returns `None` if `all_syntax` is empty.

### Lint Emission

- **E01 (missing provenance)**: Emitted when a fact has zero provenance (`ProvenanceWeight::zero()`), indicating that no combination of base facts can derive it. The `missing_for_nonzero()` method identifies which base facts would need to be added.

### Repair Integration

Provenance analysis feeds into the repair engine: when a category has missing rule coverage, the provenance polynomial identifies exactly which base-fact rules are absent, enabling targeted `RepairSuggestion` generation.

## Rust Implementation Notes

| Type                | Role                                                     |
|---------------------|----------------------------------------------------------|
| `ProvenanceVar`     | Base-fact variable: `ProvenanceVar(String)`              |
| `Monomial`          | Product of variables with exponents: `BTreeMap<ProvenanceVar, u32>` |
| `ProvenanceWeight`  | Polynomial: `BTreeMap<Monomial, u64>` (monomial -> coefficient) |
| `ProvenanceAnalysis`| Pipeline result: provenance_traces (label, polynomial string) |

## Worked Example

Track provenance for a grammar with two rules deriving `Expr`.

**Step 1: Assign provenance variables.**

```
Rule "Add": Expr ::= Expr "+" Expr ;  -->  x_Add
Rule "Num": Expr ::= INT ;            -->  x_Num
```

**Step 2: Build provenance polynomial for "Expr is derivable."**

A simple `Expr` can be derived by `Num` alone: `p = x_Num`.
A compound `Expr` via `Add` requires two sub-`Expr`s:
```
p(Expr) = x_Num + x_Add . p(Expr) . p(Expr)
```

For a concrete parse of `1 + 2`:
```
provenance(1)     = x_Num
provenance(2)     = x_Num
provenance(1 + 2) = x_Add . x_Num . x_Num = x_Add . x_Num^2
```

**Step 3: Project to target semirings.**

- `to_boolean(x_Add . x_Num^2)` = `true` (derivation exists)
- `to_counting(x_Add . x_Num^2)` = `1` (one derivation)
- `evaluate(x_Add . x_Num^2, v)` with `v(x_Add) = TropicalWeight(1.0)`, `v(x_Num) = TropicalWeight(0.5)`:
  - `1.0 + 0.5 + 0.5 = 2.0` (tropical cost of this derivation)

**Step 4: Diagnose missing provenance.**

If the grammar lacks `Num`, then `p(Expr) = x_Add . p(Expr)^2` with no base case. For a leaf input like `1`, `provenance(1) = 0` (zero polynomial). The lint emits:

```
[E01-note] fact 'Expr(1)' has zero provenance
  hint: No base-case rule produces Expr for terminal '1'.
  Needed: a rule matching pattern 'Expr ::= INT'.
```

## References

1. Green, T.J., Karvounarakis, G. & Tannen, V. (2007). "Provenance semirings." *PODS*.
2. Green, T.J. (2011). "Containment of conjunctive queries on annotated relations." *Theory of Computing Systems*, 49(2).
3. Deutch, D. et al. (2014). "Provenance for natural language queries." *VLDB*.
4. Amsterdamer, Y., Deutch, D. & Tannen, V. (2011). "Provenance for aggregate queries." *PODS*.
5. Karvounarakis, G. & Green, T.J. (2012). "Semiring-annotated data: queries and provenance." *SIGMOD Record*, 41(3).
