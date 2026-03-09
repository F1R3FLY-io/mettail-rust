# Provenance Semiring: ProvenanceWeight

## 1. Intuition & Motivation

The provenance semiring provides a *symbolic derivation algebra* for
tracking how facts are derived from base facts. Its carrier set
consists of polynomials with natural number coefficients over a set
of indeterminates (provenance variables), and its two operations
correspond directly to derivation composition:

- **Combining alternative derivations** (parallel paths) uses
  polynomial addition -- coefficients of matching monomials are summed.
- **Sequencing derivation steps** (a path through multiple rules) uses
  polynomial multiplication -- cross-products of monomial pairs record
  all conjunctive combinations of base facts.

Within PraTTaIL, provenance tracking answers: "which grammar rules
contributed to this parse, in what combinations, and how many times?"

```
higher detail  =  richer provenance  =  more diagnostic power
```

A Boolean weight tells you *whether* a fact is derivable. A counting
weight tells you *how many* derivations exist. A provenance polynomial
tells you *exactly which base facts* participated in each derivation.
By encoding this information into the most general commutative
semiring, PraTTaIL's proof output, dead-rule detection, repair
suggestions, and lint diagnostics all share the same algebraic
framework -- the algorithms are semiring-generic, while the weight
type determines the information level.

---

## 2. Formal Definition

The provenance semiring is the polynomial semiring over the naturals:

```
P  =  ( N[X],  +,  *,  0,  1 )
```

where:

| Component                   | Symbol | Concrete value          | Meaning                              |
|-----------------------------|--------|-------------------------|--------------------------------------|
| Carrier set                 | K      | N[X]                    | Polynomials with natural coefficients|
| Addition (⊕)                | +      | polynomial addition     | Union of derivation alternatives     |
| Multiplication (⊗)          | *      | polynomial multiplication| Conjunction of derivation steps     |
| Additive identity (0)       | 0      | empty polynomial `{}`   | No derivation exists                 |
| Multiplicative identity (1) | 1      | constant polynomial `1` | Trivial derivation (no base facts)   |

A polynomial `p in N[X]` is a formal sum of *monomials*:

```
p  =  Sigma_i  c_i * m_i
```

where each monomial `m_i = x_1^{a_1} * x_2^{a_2} * ... * x_n^{a_n}`
is a product of indeterminates raised to natural number exponents,
and each coefficient `c_i in N` counts the multiplicity of that
derivation pattern.

The name "provenance" comes from database theory, where this
construction tracks which input tuples contribute to each output
tuple. In the parsing literature, it is the most general commutative
semiring: every other commutative semiring is a quotient of N[X]
under some valuation homomorphism.

---

## 3. Semiring Axiom Verification

We verify all eight semiring axioms with concrete symbolic examples.
Let p_1 = x_1 + x_2, p_2 = x_3, p_3 = x_1 * x_3.

### (A1) Associativity of ⊕

```
(p_1 ⊕ p_2) ⊕ p_3
  = ((x_1 + x_2) + x_3) + x_1*x_3
  = x_1 + x_2 + x_3 + x_1*x_3

p_1 ⊕ (p_2 ⊕ p_3)
  = (x_1 + x_2) + (x_3 + x_1*x_3)
  = x_1 + x_2 + x_3 + x_1*x_3   ✓
```

Holds because polynomial addition is associative (inherited from
the associativity of natural number addition on coefficients).

### (A2) Commutativity of ⊕

```
p_1 ⊕ p_2  =  (x_1 + x_2) + x_3  =  x_1 + x_2 + x_3
p_2 ⊕ p_1  =  x_3 + (x_1 + x_2)  =  x_1 + x_2 + x_3   ✓
```

Holds because polynomial addition is commutative (the BTreeMap
representation ensures canonical ordering regardless of insertion
order).

### (A3) ⊕ Identity

```
0 ⊕ p_1  =  {} + (x_1 + x_2)  =  x_1 + x_2  =  p_1   ✓
p_1 ⊕ 0  =  (x_1 + x_2) + {}  =  x_1 + x_2  =  p_1   ✓
```

The empty polynomial is the identity for polynomial addition
because adding no terms leaves the polynomial unchanged.

### (M1) Associativity of ⊗

```
(p_1 ⊗ p_2) ⊗ p_3
  = ((x_1 + x_2) * x_3) * (x_1*x_3)
  = (x_1*x_3 + x_2*x_3) * (x_1*x_3)
  = x_1^2*x_3^2 + x_1*x_2*x_3^2

p_1 ⊗ (p_2 ⊗ p_3)
  = (x_1 + x_2) * (x_3 * x_1*x_3)
  = (x_1 + x_2) * (x_1*x_3^2)
  = x_1^2*x_3^2 + x_1*x_2*x_3^2   ✓
```

Holds because polynomial multiplication is associative (inherited
from the associativity of monomial exponent addition and natural
number coefficient multiplication).

### (M2) ⊗ Identity

```
1 ⊗ p_1  =  {1 -> 1} * (x_1 + x_2)  =  x_1 + x_2  =  p_1   ✓
p_1 ⊗ 1  =  (x_1 + x_2) * {1 -> 1}  =  x_1 + x_2  =  p_1   ✓
```

The constant polynomial 1 (the empty monomial with coefficient 1)
is the identity for polynomial multiplication because multiplying
any monomial by the empty monomial yields that monomial unchanged.

### (D1) Left Distributivity: ⊗ distributes over ⊕ from the left

```
p_2 ⊗ (p_1 ⊕ p_3)
  = x_3 * ((x_1 + x_2) + x_1*x_3)
  = x_3 * (x_1 + x_2 + x_1*x_3)
  = x_1*x_3 + x_2*x_3 + x_1*x_3^2

(p_2 ⊗ p_1) ⊕ (p_2 ⊗ p_3)
  = (x_3 * (x_1 + x_2)) + (x_3 * x_1*x_3)
  = (x_1*x_3 + x_2*x_3) + x_1*x_3^2
  = x_1*x_3 + x_2*x_3 + x_1*x_3^2   ✓
```

Holds because polynomial multiplication distributes over polynomial
addition (inherited from the distributivity of natural numbers).

### (D2) Right Distributivity: ⊗ distributes over ⊕ from the right

```
(p_1 ⊕ p_3) ⊗ p_2
  = ((x_1 + x_2) + x_1*x_3) * x_3
  = x_1*x_3 + x_2*x_3 + x_1*x_3^2

(p_1 ⊗ p_2) ⊕ (p_3 ⊗ p_2)
  = ((x_1 + x_2) * x_3) + (x_1*x_3 * x_3)
  = (x_1*x_3 + x_2*x_3) + x_1*x_3^2
  = x_1*x_3 + x_2*x_3 + x_1*x_3^2   ✓
```

Symmetric argument to (D1), exploiting commutativity of monomial
multiplication.

### (Z) Zero Annihilation

```
0 ⊗ p_1  =  {} * (x_1 + x_2)  =  {}  =  0   ✓
p_1 ⊗ 0  =  (x_1 + x_2) * {}  =  {}  =  0   ✓
```

Multiplying any polynomial by the empty polynomial produces
the empty polynomial. No cross-product terms are generated when
one operand has no monomials.

All eight axioms are satisfied. P is a valid semiring.

> For the parsing-specific interpretation of these axioms, see
> [Section 4 Why Each Axiom Matters for Parsing](../semirings.md#4-why-each-axiom-matters-for-parsing).

---

## 4. Key Properties

### 4.1 Commutativity

**Claim**: The provenance semiring is commutative (⊗ is commutative).

**Proof**: For all p, q in N[X]:

```
p ⊗ q  =  Sigma_{i,j} (c_i * d_j) * (m_i * m_j)
q ⊗ p  =  Sigma_{j,i} (d_j * c_i) * (m_j * m_i)
```

Since natural number multiplication is commutative (`c_i * d_j = d_j * c_i`)
and monomial multiplication is commutative (exponent addition is
commutative in each variable), we have `p ⊗ q = q ⊗ p`.   ∎

Commutativity means derivation order does not affect the provenance
polynomial -- combining derivation step A then B yields the same
provenance as B then A.

### 4.2 Non-Idempotency

**Claim**: The provenance semiring is *not* idempotent.

**Proof by counterexample**:

```
p = x_1        (coefficient 1)
p ⊕ p = 2*x_1  (coefficient 2)
```

Since `2*x_1 != x_1`, we have `p ⊕ p != p`.   ∎

Non-idempotency is essential: merging a derivation path with itself
*doubles* the coefficient, recording that the same derivation was
discovered twice. This multiplicity information distinguishes
how-provenance from why-provenance (which is idempotent).

### 4.3 Universal Property

**Claim**: N[X] is the free commutative semiring on generators X.

**Consequence**: For every commutative semiring W and every function
`v: X -> W`, there exists a unique semiring homomorphism
`eval_v: N[X] -> W` that extends v.

This universal property means every commutative semiring is a
quotient of N[X]. The homomorphism `eval_v` is implemented as
`ProvenanceWeight::evaluate()`:

```
                N[X]
               ╱  |  ╲
         eval ╱   |   ╲ eval
        (v_1)╱    |    ╲(v_3)
            ╱     |     ╲
           ▼   eval(v_2) ▼
    BooleanWeight  ▼  TropicalWeight
             CountingWeight
```

### 4.4 Heap Allocation

**Claim**: ProvenanceWeight cannot implement `Copy`.

**Reason**: The internal `BTreeMap<Monomial, u64>` is heap-allocated.
The `Monomial` type itself contains a `BTreeMap<ProvenanceVar, u32>`,
and `ProvenanceVar` wraps a `String`. Multiple levels of heap
allocation preclude `Copy` semantics.

ProvenanceWeight implements the `HeapSemiring` trait (defined in
`relational.rs`) rather than the `Copy`-bounded `Semiring` trait.
This constrains its use to `HeapWpds` infrastructure rather than the
standard Viterbi, forward-backward, and lattice algorithms.

---

## 5. Valuation Homomorphism

The universal property gives rise to the `evaluate()` method, which
maps provenance polynomials to any target semiring:

```
eval_v(p)  =  ⊕_W  Sigma_i  c_i *_W  (⊗_W  Sigma_j  v(x_j)^{a_j})
```

where:
- The outer sum uses `W::plus`
- The inner product uses `W::times`
- `c_i *_W w` means `w ⊕_W w ⊕_W ... ⊕_W w` (c_i times)
- `v(x_j)^{a_j}` means `v(x_j) ⊗_W v(x_j) ⊗_W ... ⊗_W v(x_j)` (a_j times)

### Homomorphism Properties

The function `eval_v` preserves semiring structure:

```
eval_v(p ⊕ q)  =  eval_v(p) ⊕_W eval_v(q)
eval_v(p ⊗ q)  =  eval_v(p) ⊗_W eval_v(q)
eval_v(0)      =  0_W
eval_v(1)      =  1_W
```

### Standard Valuations

| Target Semiring | Valuation `v`         | Result                        | Provenance Level   |
|------------------|-----------------------|-------------------------------|--------------------|
| BooleanWeight    | `v(x) = true` for all x | Is the fact derivable?       | Which-provenance   |
| CountingWeight   | `v(x) = 1` for all x   | Total derivation count       | How-many           |
| TropicalWeight   | `v(x) = cost(x)`       | Cheapest derivation cost     | Cost-provenance    |
| ViterbiWeight    | `v(x) = prob(x)`       | Most confident derivation    | Confidence-prov.   |

---

## 6. Zero Annihilation

The zero element (empty polynomial `{}`) represents a state where
no derivation exists. Its annihilation property guarantees that
unreachable derivations remain unreachable regardless of composition:

```
{} ⊗ p  =  {}     for all p in N[X]
p ⊗ {}  =  {}     for all p in N[X]
```

This is the correct semantic for derivation tracking: if any step
along a derivation chain has no base facts (zero provenance), the
entire derivation has no base facts. No subsequent rule application
can rescue a derivation that never started.

In the implementation, `is_zero()` checks whether the `terms`
BTreeMap is empty:

```rust
pub fn is_zero(&self) -> bool {
    self.terms.is_empty()
}
```

The invariant that zero-coefficient entries are stripped after every
operation ensures that `terms.is_empty()` correctly identifies the
zero polynomial.

---

## 7. Path Provenance Computation

### Worked Example

Consider a grammar with three rules:

```
Rule A (label = "Add"):   Expr  ->  Expr "+" Expr
Rule B (label = "Mul"):   Expr  ->  Expr "*" Expr
Rule C (label = "Lit"):   Expr  ->  Int
```

The provenance variables are `x_A`, `x_B`, `x_C`. Parsing the
expression `1 + 2 * 3` has two derivation trees:

```
  Derivation 1:  Add(Lit(1), Mul(Lit(2), Lit(3)))
                 provenance = x_A * x_C^2 * x_B * x_C = x_A * x_B * x_C^3

  Derivation 2:  Mul(Add(Lit(1), Lit(2)), Lit(3))
                 provenance = x_B * x_A * x_C^2 * x_C = x_A * x_B * x_C^3
```

Both derivations produce the same monomial `x_A * x_B * x_C^3`
(commutativity ensures order independence). The combined provenance is:

```
  p  =  2 * x_A * x_B * x_C^3
```

The coefficient 2 records that there are two distinct parse trees
using rules A, B, and C in the same combination.

### Evaluating the Provenance

Assigning costs `cost(A) = 1.0`, `cost(B) = 2.0`, `cost(C) = 0.5`:

```
  eval_tropical(p)  =  min(1.0 + 2.0 + 3*0.5, 1.0 + 2.0 + 3*0.5)
                     =  min(4.5, 4.5)
                     =  4.5
```

Both derivations have the same tropical cost because they use the
same rules (just in different order).

Evaluating to counting:

```
  eval_counting(p)  =  2 * 1 * 1 * 1  =  2
```

Two derivations exist for this input.

---

## 8. Provenance Hierarchy

The Green-Karvounarakis-Tannen hierarchy organizes provenance types
by information content:

```
┌───────────────────────────────────────────────────────────────────┐
│                        N[X]                                       │
│                   (how-provenance)                                 │
│                                                                   │
│   Records which combinations of base facts derive each result.    │
│   Coefficients count derivation multiplicity.                     │
│                                                                   │
├───────────────────────┬───────────────────────────────────────────┤
│         ▼             │              ▼               ▼            │
│   PosBool[X]          │       Trio[X]         N (counting)        │
│   (why-provenance)    │   (3-valued)       (how-many)             │
│   drop multiplicities │                    sum all coeffs         │
├───────────────────────┤───────────────────────────────────────────┤
│         ▼                                    ▼                    │
│      Bool                              TropicalWeight             │
│  (which-provenance)                    (cost-provenance)          │
│  non-zero test                         min-cost derivation        │
└───────────────────────────────────────────────────────────────────┘
```

Each arrow represents a surjective semiring homomorphism. Moving
downward discards information:

- **N[X] -> PosBool[X]**: Drop coefficients (set all to 1). Retains
  which monomials appear but not how many times.
- **N[X] -> N**: Sum all coefficients (`to_counting()`). Retains total
  count but not which base facts contribute.
- **PosBool[X] -> Bool**: Check non-emptiness (`to_boolean()`). Only
  retains whether any derivation exists.
- **N -> TropicalWeight**: Assign costs and minimize. Selects the
  cheapest derivation.

---

## 9. Comparison with BooleanWeight and CountingWeight

The provenance, Boolean, and counting semirings form a hierarchy of
increasing abstraction (decreasing information):

| Property            | ProvenanceWeight        | CountingWeight             | BooleanWeight             |
|---------------------|-------------------------|----------------------------|---------------------------|
| Carrier set         | N[X] (polynomials)      | N (natural numbers)        | {false, true}             |
| ⊕ (addition)        | polynomial addition     | natural addition           | logical OR                |
| ⊗ (multiplication)  | polynomial multiplication| natural multiplication     | logical AND               |
| 0 (zero)            | empty polynomial        | 0                          | false                     |
| 1 (one)             | constant polynomial 1   | 1                          | true                      |
| Idempotent?         | No: x + x = 2x != x    | No: 1 + 1 = 2 != 1        | Yes: true OR true = true  |
| Commutative?        | Yes                     | Yes                        | Yes                       |
| Copy?               | No (heap-allocated)     | Yes                        | Yes                       |
| Information level   | Full derivation history | Derivation count only      | Existence only            |
| Projection to Bool  | `to_boolean()`          | `count > 0`                | identity                  |
| Use case            | Proof certificates,     | Ambiguity detection,       | Reachability analysis,    |
|                     | repair suggestions      | confidence annotations     | dead-rule detection       |

The key distinction is **information granularity**. ProvenanceWeight
records which specific base facts participated in each derivation
and how many times. CountingWeight retains only the total count.
BooleanWeight collapses everything to a single bit.

ProvenanceWeight is the most expensive but most informative. It
should be used when downstream analyses need to trace back to
specific grammar rules (proof certificates, repair suggestions).
For simple ambiguity detection, CountingWeight suffices.

---

## 10. Pseudocode: Provenance Evaluation

The evaluation algorithm projects a provenance polynomial to any
target semiring via a valuation function:

```
ALGORITHM EvaluateProvenance(polynomial, valuation, W)
────────────────────────────────────────────────────────
  Input:  Polynomial p = {m_1 -> c_1, m_2 -> c_2, ...}
          Valuation  v : ProvenanceVar -> W
          Target semiring W with operations ⊕_W, ⊗_W
  Output: Weight w in W

  1.  result <- 0_W                          // additive identity of W

  2.  for each (monomial m_i, coefficient c_i) in p do
  3.      mono_val <- 1_W                    // multiplicative identity of W
  4.      for each (variable x_j, exponent a_j) in m_i do
  5.          var_val <- v(x_j)
  6.          for k = 1 to a_j do
  7.              mono_val <- mono_val ⊗_W var_val
  8.      end for

  9.      term_val <- 0_W                    // scale mono_val by c_i
 10.      for k = 1 to c_i do
 11.          term_val <- term_val ⊕_W mono_val
 12.      end for

 13.      result <- result ⊕_W term_val
 14.  end for

 15.  return result
```

**Complexity**: O(T * (V * E_max + C_max)) where T = number of
monomials, V = max variables per monomial, E_max = max exponent,
C_max = max coefficient. For typical grammar provenance, T is small
(bounded by the number of grammar rules), V is small (bounded by
derivation depth), and exponents/coefficients rarely exceed single
digits.

---

## 11. Rust Implementation

The following shows the core `ProvenanceWeight` implementation from
`prattail/src/provenance.rs`.

```rust
/// Provenance polynomial `N[X]`: a sum of weighted monomials.
///
/// This is the **how-provenance** semiring from Green et al. (2007).
/// Each term tracks a distinct combination of base facts that derives
/// the result.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ProvenanceWeight {
    /// Terms: monomial -> coefficient (natural number).
    /// Zero polynomial has empty terms map.
    pub terms: BTreeMap<Monomial, u64>,
}

impl ProvenanceWeight {
    /// Polynomial addition: p_1 ⊕ p_2 -- union of derivation alternatives.
    pub fn plus(&self, other: &ProvenanceWeight) -> ProvenanceWeight {
        let mut result = self.terms.clone();
        for (mono, &coeff) in &other.terms {
            *result.entry(mono.clone()).or_insert(0) += coeff;
        }
        result.retain(|_, c| *c > 0);
        ProvenanceWeight { terms: result }
    }

    /// Polynomial multiplication: p_1 ⊗ p_2 -- conjunction of derivation steps.
    pub fn times(&self, other: &ProvenanceWeight) -> ProvenanceWeight {
        let mut result = BTreeMap::new();
        for (m1, &c1) in &self.terms {
            for (m2, &c2) in &other.terms {
                let product_mono = m1.multiply(m2);
                *result.entry(product_mono).or_insert(0u64) += c1 * c2;
            }
        }
        result.retain(|_, c| *c > 0);
        ProvenanceWeight { terms: result }
    }

    /// Evaluate the polynomial by substituting each variable with a
    /// value from the given semiring, returning the aggregate weight.
    pub fn evaluate<W: Semiring>(
        &self,
        valuation: &impl Fn(&ProvenanceVar) -> W,
    ) -> W { /* ... */ }
}
```

### Implementation Notes

- **BTreeMap for canonical form**: Both `Monomial::factors` and
  `ProvenanceWeight::terms` use `BTreeMap` to ensure deterministic
  ordering. This guarantees that `x_1 * x_2` and `x_2 * x_1`
  produce identical monomial keys.

- **Zero-coefficient stripping**: After every `plus` and `times`,
  entries with coefficient 0 are removed via `retain(|_, c| *c > 0)`.
  This maintains the invariant that `terms.is_empty()` correctly
  identifies the zero polynomial.

- **Heap-allocated, not Copy**: Due to nested `BTreeMap` and `String`
  allocations, ProvenanceWeight uses `HeapSemiring` rather than
  `Semiring`. This precludes use with standard Viterbi algorithms but
  enables use with `HeapWpds` infrastructure.

- **Default = one()**: A newly created provenance weight represents
  "trivial derivation" (the constant polynomial 1), not "no derivation"
  (the zero polynomial).

---

## 12. Integration into PraTTaIL

ProvenanceWeight is used in three main subsystems:

### 12.1 Pipeline Bridge (provenance.rs)

The `track_from_bundle()` function creates a provenance polynomial
for each grammar rule, mapping rule labels to single-variable
polynomials:

```rust
pub fn track_from_bundle(
    all_syntax: &[(String, String, Vec<SyntaxItemSpec>)],
    _categories: &[CategoryInfo],
) -> Option<ProvenanceAnalysis>
```

For each rule with label `L`, it creates `ProvenanceWeight::var(L)`.
The resulting `ProvenanceAnalysis` contains displayable traces for
diagnostic output.

### 12.2 Proof Certificate Generation (proof_output.rs)

Provenance polynomials justify each derivation step in generated
proof certificates. The proof output module uses provenance to show
which rules contributed to each derived fact.

### 12.3 Lint Layer (lint.rs)

The E01 lint attaches rule-level provenance to parse results. Dead
rules (those that never appear in any derivation polynomial) are
confirmed unreachable. Repair suggestions use `missing_for_nonzero()`
to identify which base facts are absent from zero polynomials.

---

## 13. Source Reference & See Also

### Source Location

- **File**: `prattail/src/provenance.rs`
- **Struct**: `ProvenanceWeight { terms: BTreeMap<Monomial, u64> }`
- **Monomial struct**: `Monomial { factors: BTreeMap<ProvenanceVar, u32> }`
- **ProvenanceVar struct**: `ProvenanceVar(pub String)`
- **Pipeline bridge**: `track_from_bundle()` (lines 339--354)
- **Tests**: 24 tests covering all axioms and API methods

### Cross-References

- [Semiring Algebra Overview](../semirings.md) -- Axiom
  definitions, classification, and comparison of all semirings
- [Boolean Weight Theory](boolean-weight.md) -- Which-provenance:
  the simplest projection of the provenance hierarchy
- [Counting Weight Theory](counting-weight.md) -- How-many
  projection: total derivation count
- [Tropical Weight Theory](tropical-weight.md) -- Cost-provenance:
  cheapest derivation via valuation homomorphism
- [Relational Weight Theory](relational-weight.md) -- Another
  HeapSemiring weight for state-pair reachability
- [Tensor Weight Theory](tensor-weight.md) -- Correlated multi-analysis
  composition compatible with provenance projections
- [Provenance Design Doc](../../../design/wfst/semirings/provenance-weight.md) --
  Implementation decisions and pipeline integration details
- [Proof Output](../../../src/proof_output.rs) -- Provenance-based
  derivation certificates
- [Lint Layer](../../../src/lint.rs) -- E01 provenance-annotated
  diagnostics

### Academic References

- T. J. Green, G. Karvounarakis, and V. Tannen. "Provenance Semirings."
  Proceedings of the 26th ACM SIGMOD-SIGACT-SIGART Symposium on
  Principles of Database Systems (PODS), 2007, pp. 31--40.
