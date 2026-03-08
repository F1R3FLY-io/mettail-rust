# ProvenanceWeight -- Design & Pipeline Integration

> **Date:** 2026-03-08

Most semirings answer "what is the best path?" or "how many paths exist?"
The provenance semiring answers a deeper question: **how was the result
derived?** It records the full algebraic history of a computation as a
polynomial, so you can trace every conclusion back to the base facts that
produced it. Think of it as a symbolic receipt attached to each derived fact.

---

## Table of Contents

1. [Intuition](#1-intuition)
2. [Mathematical Definition](#2-mathematical-definition)
3. [Data Structures](#3-data-structures)
4. [Semiring Operations](#4-semiring-operations)
5. [Valuation Homomorphism](#5-valuation-homomorphism)
6. [Projections to Other Semirings](#6-projections-to-other-semirings)
7. [Connection to Database Provenance](#7-connection-to-database-provenance)
8. [Pipeline Integration](#8-pipeline-integration)
9. [Rust API](#9-rust-api)
10. [Test Coverage](#10-test-coverage)
11. [Source References](#11-source-references)
12. [Cross-References](#12-cross-references)

---

## 1. Intuition

Consider a grammar with three rules for deriving an `Expr`:

```
Rule A:  Expr  ->  Int
Rule B:  Expr  ->  Ident
Rule C:  Expr  ->  Expr "+" Expr
```

If a token stream `1 + x` can be parsed as `C(A, B)`, the provenance
polynomial records exactly that:

```
provenance = a · c
```

meaning "the derivation used base fact A once and base fact C once." If an
alternative derivation existed (say via a macro expansion), the polynomial
would be:

```
provenance = a · c + d
```

This says: "there are two derivation paths -- one uses A and C, the other
uses D alone." No other semiring preserves this level of detail.

The key insight from Green, Karvounarakis & Tannen (2007) is that the
polynomial semiring `N[X]` is the **most general** commutative semiring.
Every other commutative semiring arises as a homomorphic image of `N[X]`
under some valuation. This universality means that provenance tracking
subsumes Boolean reachability, counting, tropical costing, and Viterbi
confidence as special cases.

---

## 2. Mathematical Definition

The provenance semiring is the polynomial ring over the naturals:

```
(N[X],  ⊕,  ⊗,  0,  1)
```

where:

- **Carrier set**: Polynomials with coefficients in N (natural numbers)
  over a set of indeterminates X (provenance variables).
  Each polynomial `p = Σ cᵢ · m_i` is a sum of *monomials* `m_i = x₁^{a₁} · x₂^{a₂} · ... · xₙ^{aₙ}`
  weighted by natural number coefficients `cᵢ`.

- **Plus** (⊕): Polynomial addition. Combines like monomials by summing
  their coefficients:
  ```
  (3·x₁·x₂ + 2·x₃)  ⊕  (x₁·x₂ + x₃)  =  4·x₁·x₂ + 3·x₃
  ```
  Semantics: union of derivation alternatives. Each monomial represents
  a distinct way to derive the fact; coefficients count multiplicity.

- **Times** (⊗): Polynomial multiplication. Cross-product of all
  monomial pairs, combining exponents:
  ```
  (x₁ + x₂)  ⊗  (x₃ + x₄)  =  x₁·x₃ + x₁·x₄ + x₂·x₃ + x₂·x₄
  ```
  Semantics: conjunction of derivation steps. Sequencing two derivation
  stages multiplies their provenance.

- **Zero** (0): The empty polynomial `{}` -- no derivation exists.

- **One** (1): The constant polynomial `{1 -> 1}` -- the trivial
  derivation that requires no base facts.

### Semiring axioms

| Axiom                 | Formula                       | Status     |
|-----------------------|-------------------------------|------------|
| Additive identity     | p ⊕ 0 = p                    | Holds      |
| Additive commutativity| p ⊕ q = q ⊕ p                | Holds      |
| Additive associativity| (p ⊕ q) ⊕ r = p ⊕ (q ⊕ r)    | Holds      |
| Multiplicative identity| p ⊗ 1 = 1 ⊗ p = p           | Holds      |
| Multiplicative assoc. | (p ⊗ q) ⊗ r = p ⊗ (q ⊗ r)    | Holds      |
| Distributivity        | p ⊗ (q ⊕ r) = p⊗q ⊕ p⊗r      | Holds      |
| Zero annihilation     | p ⊗ 0 = 0 ⊗ p = 0            | Holds      |

All seven axioms are verified by unit tests in `provenance.rs`.

---

## 3. Data Structures

### 3a. ProvenanceVar

A named indeterminate representing a single base fact:

```rust
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ProvenanceVar(pub String);
```

Variables are ordered (via `Ord`) to enforce canonical monomial
representation. Two variables with the same name are equal, regardless
of where they were constructed.

### 3b. Monomial

A product of variables with natural-number exponents:

```rust
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Monomial {
    pub factors: BTreeMap<ProvenanceVar, u32>,
}
```

The `BTreeMap` sorts variables by name, ensuring that `x₁·x₂` and
`x₂·x₁` produce identical keys. This canonical form is essential for
correct coefficient combination during `plus`.

| Method       | Signature                         | Semantics                    |
|--------------|-----------------------------------|------------------------------|
| `one()`      | `-> Monomial`                     | Empty product (constant `1`) |
| `var(v)`     | `ProvenanceVar -> Monomial`       | Single variable `v^1`        |
| `multiply()` | `&Monomial, &Monomial -> Monomial`| Exponent addition            |
| `degree()`   | `-> u32`                          | Sum of all exponents         |
| `is_one()`   | `-> bool`                         | Whether factors is empty     |

**Display**: `x₁` for single-variable, `x₁^2` for repeated, `x₁·x₂`
for multi-variable. The empty monomial displays as `1`.

### 3c. ProvenanceWeight

The polynomial itself:

```rust
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ProvenanceWeight {
    pub terms: BTreeMap<Monomial, u64>,
}
```

Each entry maps a monomial to its coefficient. Invariant: no entry has
coefficient zero (zero-coefficient entries are stripped after every
operation).

**Memory layout**: Heap-allocated via `BTreeMap`. `ProvenanceWeight` does
not implement `Copy` and uses the `HeapSemiring` trait rather than the
`Copy`-bounded `Semiring` trait.

---

## 4. Semiring Operations

### 4a. Plus (polynomial addition)

```rust
pub fn plus(&self, other: &ProvenanceWeight) -> ProvenanceWeight {
    let mut result = self.terms.clone();
    for (mono, &coeff) in &other.terms {
        *result.entry(mono.clone()).or_insert(0) += coeff;
    }
    result.retain(|_, c| *c > 0);
    ProvenanceWeight { terms: result }
}
```

**Complexity**: O(m log n) where m = terms in `other`, n = terms in `self`.
The `BTreeMap::entry` lookup is O(log n) per insertion.

**Example**:

```
(x₁ + x₂)  ⊕  (x₁ + x₃)  =  2·x₁ + x₂ + x₃
```

The coefficient of `x₁` doubles because it appears in both operands.

### 4b. Times (polynomial multiplication)

```rust
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
```

**Complexity**: O(m * n * log(m * n)) where m, n are the term counts.
Each of the `m * n` pairwise products requires a `BTreeMap` insertion.

**Example**:

```
(x₁ + x₂)  ⊗  (x₃ + x₄)  =  x₁·x₃ + x₁·x₄ + x₂·x₃ + x₂·x₄
```

Four distinct monomials arise from the cross-product. Each records a
different combination of base facts that jointly derive the result.

### 4c. Identity elements

```
zero()  =  ProvenanceWeight { terms: {} }        // empty polynomial
one()   =  ProvenanceWeight { terms: { 1 -> 1 } } // constant monomial 1
```

---

## 5. Valuation Homomorphism

The `evaluate()` method is the universal homomorphism from `N[X]` to any
target semiring `W`, given a valuation function `v: X -> W`:

```rust
pub fn evaluate<W: Semiring>(
    &self,
    valuation: &impl Fn(&ProvenanceVar) -> W,
) -> W
```

It computes:

```
eval_v(p)  =  ⊕ᵢ  cᵢ · ⊗ⱼ v(xⱼ)^{aⱼ}
```

where the outer sum uses `W::plus`, the inner product uses `W::times`,
and `cᵢ · w` means `w ⊕ w ⊕ ... ⊕ w` (cᵢ times).

### Why this works

The polynomial semiring `N[X]` is the free commutative semiring on
generators X. By the universal property of free algebras, every
function `v: X -> W` extends uniquely to a semiring homomorphism
`eval_v: N[X] -> W`. This means:

- `eval_v(p ⊕ q)  =  eval_v(p)  ⊕_W  eval_v(q)`
- `eval_v(p ⊗ q)  =  eval_v(p)  ⊗_W  eval_v(q)`
- `eval_v(0)  =  0_W`
- `eval_v(1)  =  1_W`

The homomorphism collapses provenance into concrete weights while
preserving the semiring structure.

### Diagram: provenance as universal semiring

```
                N[X]
               ╱  |  ╲
         eval  ╱   |   ╲  eval
        (v₁)  ╱    |    ╲  (v₃)
             ╱     |     ╲
            ▼   eval(v₂)  ▼
     BooleanWeight  ▼  TropicalWeight
              CountingWeight
```

Every concrete semiring is a quotient of `N[X]` under the appropriate
valuation. The provenance polynomial preserves maximal information; each
valuation discards information specific to one analysis mode.

---

## 6. Projections to Other Semirings

ProvenanceWeight includes two convenience projections that bypass the
full `evaluate()` machinery:

| Projection      | Method          | Semantics                           | Equivalent Valuation           |
|-----------------|-----------------|-------------------------------------|--------------------------------|
| Which-provenance| `to_boolean()`  | Is the polynomial non-zero?         | `v(x) = true` for all x       |
| How-many        | `to_counting()` | Total coefficient sum               | `v(x) = 1` for all x          |

The full provenance hierarchy from Green et al. (2007):

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

---

## 7. Connection to Database Provenance

The theoretical foundation comes from:

> T. J. Green, G. Karvounarakis, and V. Tannen. "Provenance Semirings."
> Proceedings of the 26th ACM SIGMOD-SIGACT-SIGART Symposium on
> Principles of Database Systems (PODS), 2007, pp. 31--40.

Green et al. showed that annotating relational algebra with polynomial
semiring coefficients provides a universal provenance model. Query
evaluation becomes semiring arithmetic over provenance polynomials, and
any concrete provenance type (lineage, why-provenance, how-provenance,
confidence, cost) is obtained by applying a homomorphism.

In PraTTaIL's context, the "database" is the grammar rule set, the
"base facts" are individual grammar rules, and the "derived facts" are
parse derivations. Provenance tracking answers: "which rules contributed
to this parse, and in what combinations?"

---

## 8. Pipeline Integration

### 8a. Provenance tracking via `track_from_bundle()`

The pipeline bridge function creates a provenance polynomial for each
grammar rule:

```rust
pub fn track_from_bundle(
    all_syntax: &[(String, String, Vec<SyntaxItemSpec>)],
    _categories: &[CategoryInfo],
) -> Option<ProvenanceAnalysis>
```

For each rule with label `L`, it creates `ProvenanceWeight::var(L)` --
a single-variable polynomial. The resulting `ProvenanceAnalysis` contains
displayable traces `(label, polynomial_string)` for diagnostic output.

Returns `None` when `all_syntax` is empty (no rules to track).

### 8b. Use cases in PraTTaIL

| Use Case                       | How Provenance Helps                                        |
|--------------------------------|-------------------------------------------------------------|
| **E01 provenance tracking**    | Lint E01 attaches rule-level provenance to parse results     |
| **Proof certificate generation**| `proof_output.rs` uses provenance to justify derivation steps|
| **Dead-rule confirmation**     | A rule with zero provenance (never appears in any derivation polynomial) is provably dead |
| **Repair suggestions**         | `missing_for_nonzero()` identifies which base facts are absent from a zero polynomial |
| **Debugging ambiguity**        | Multiple monomials in a provenance polynomial reveal distinct derivation paths |

### 8c. Feature gating

ProvenanceWeight is available unconditionally (no feature gate). It
participates in the mathematical analysis framework behind the
`provenance` feature gate, but the core type and operations are always
compiled.

### 8d. Pipeline data flow

```
┌─────────────────────────────┐
│  language! { ... }          │
│  Rule definitions           │
└──────────┬──────────────────┘
           │
           ▼
┌─────────────────────────────┐
│  track_from_bundle()        │
│  provenance.rs              │
│                             │
│  For each rule label L:     │
│    weight = N[L]            │
│    trace = (L, display(L))  │
└──────────┬──────────────────┘
           │
           ▼
┌─────────────────────────────┐
│  ProvenanceAnalysis         │
│                             │
│  provenance_traces:         │
│    [("Add", "Add"),         │
│     ("Mul", "Mul"), ...]    │
└──────────┬──────────────────┘
           │
           ▼
┌─────────────────────────────┐
│  Lint layer / diagnostics   │
│  E01, proof_output.rs       │
└─────────────────────────────┘
```

---

## 9. Rust API

### Creating provenance weights

```rust
use prattail::provenance::{ProvenanceVar, ProvenanceWeight};

// Base-fact variables
let x = ProvenanceVar::new("rule_A");
let y = ProvenanceVar::new("rule_B");

// Single-variable polynomials
let px = ProvenanceWeight::var(x);
let py = ProvenanceWeight::var(y);

// Constant polynomial
let three = ProvenanceWeight::constant(3);

// Identities
let zero = ProvenanceWeight::zero();  // no derivation
let one  = ProvenanceWeight::one();   // trivial derivation
```

### Combining provenance

```rust
// Alternative derivations (union): x + y
let alt = px.plus(&py);
assert_eq!(alt.num_alternatives(), 2);

// Sequential derivation (conjunction): x * y
let seq = px.times(&py);
assert_eq!(seq.num_alternatives(), 1);
assert_eq!(format!("{}", seq), "rule_A\u{00b7}rule_B");

// Self-conjunction: x * x = x^2
let sq = px.times(&px);
assert_eq!(format!("{}", sq), "rule_A^2");
```

### Evaluating provenance

```rust
use prattail::automata::semiring::{BooleanWeight, CountingWeight, TropicalWeight};

let poly = px.plus(&py);  // rule_A + rule_B

// Which-provenance: is the fact derivable?
let exists = poly.evaluate(&|_| BooleanWeight(true));
assert_eq!(exists, BooleanWeight(true));

// How-many: total derivation count
let count = poly.evaluate(&|_| CountingWeight(1));
assert_eq!(count, CountingWeight(2));

// Cost-provenance: cheapest derivation
let cost = poly.evaluate(&|v| match v.0.as_str() {
    "rule_A" => TropicalWeight::new(1.0),
    "rule_B" => TropicalWeight::new(3.0),
    _ => TropicalWeight::zero(),
});
assert_eq!(cost, TropicalWeight::new(1.0));  // min(1.0, 3.0) = 1.0
```

### Inspection

```rust
let poly = px.plus(&py).times(&ProvenanceWeight::var(ProvenanceVar::new("rule_C")));

// Number of distinct derivation paths
assert_eq!(poly.num_alternatives(), 2);

// Total derivation count (sum of coefficients)
assert_eq!(poly.total_count(), 2);

// All referenced variables
let vars = poly.all_variables();
// ["rule_A", "rule_B", "rule_C"] (sorted)

// Display
assert_eq!(format!("{}", ProvenanceWeight::zero()), "0");
assert_eq!(format!("{}", ProvenanceWeight::one()), "1");
```

---

## 10. Test Coverage

Twenty-two tests in `provenance.rs` cover the full API:

| #  | Test                              | What It Verifies                                          |
|----|-----------------------------------|-----------------------------------------------------------|
| 1  | `test_zero_and_one`               | Identity elements: zero.is_zero, one.is_one               |
| 2  | `test_var`                        | Single-variable polynomial construction                   |
| 3  | `test_plus_union`                 | Plus creates two distinct alternatives                    |
| 4  | `test_plus_combines_like_terms`   | x + x = 2x (coefficient merging)                         |
| 5  | `test_times_conjunction`          | x1 * x2 = single monomial with degree 2                  |
| 6  | `test_times_self_squares`         | x * x = x^2 (exponent addition)                          |
| 7  | `test_zero_annihilates`           | p * 0 = 0 * p = 0                                        |
| 8  | `test_one_identity`               | p * 1 = 1 * p = p                                        |
| 9  | `test_zero_identity_for_plus`     | p + 0 = 0 + p = p                                        |
| 10 | `test_distributive`               | x1 * (x2 + x3) = x1*x2 + x1*x3                          |
| 11 | `test_display`                    | Display format: "0", "1", "a", "2*a"                     |
| 12 | `test_constant`                   | Constant(3) = 3, Constant(0) = zero                      |
| 13 | `test_all_variables`              | Variable collection across monomials                      |
| 14 | `test_evaluate_to_boolean`        | Homomorphism to BooleanWeight                             |
| 15 | `test_evaluate_to_counting`       | Homomorphism to CountingWeight                            |
| 16 | `test_evaluate_to_tropical`       | Homomorphism to TropicalWeight                            |
| 17 | `test_monomial_display`           | Monomial formatting: "1", "x", "x^2"                     |
| 18 | `test_to_boolean_and_counting`    | Convenience projections                                   |
| 19 | `test_complex_polynomial`         | (x1+x2)*(x3+x4) = 4 alternatives                        |
| 20 | `test_commutativity_of_plus`      | a+b = b+a                                                |
| 21 | `test_associativity_of_times`     | (a*b)*c = a*(b*c)                                        |
| 22 | `test_missing_for_nonzero`        | Repair hint for zero polynomials                          |
| 23 | `test_track_from_bundle_basic`    | Pipeline bridge: non-empty syntax produces analysis       |
| 24 | `test_track_from_bundle_empty`    | Pipeline bridge: empty syntax returns None                |

---

## 11. Source References

| Component                      | File             | Lines     |
|--------------------------------|------------------|-----------|
| Module documentation           | `provenance.rs`  | 1-43      |
| `ProvenanceVar` struct         | `provenance.rs`  | 47-65     |
| `Monomial` struct + methods    | `provenance.rs`  | 67-134    |
| `ProvenanceWeight` struct      | `provenance.rs`  | 136-312   |
| `track_from_bundle()` bridge   | `provenance.rs`  | 339-354   |
| `ProvenanceAnalysis` struct    | `provenance.rs`  | 326-329   |
| Tests (24)                     | `provenance.rs`  | 356-628   |

---

## 12. Cross-References

- **Theory**: Green, Karvounarakis & Tannen (2007), "Provenance Semirings" -- foundational paper defining the polynomial semiring hierarchy
- **HeapSemiring trait**: `relational.rs` -- the non-Copy semiring trait that ProvenanceWeight uses for WPDS integration
- **TensorWeight**: `tensor-weight.md` -- models interaction between analyses; can compose with ProvenanceWeight for correlated provenance+cost tracking
- **ProductWeight**: `product-weight.md` -- independent composition (no interaction); compare with TensorWeight for use case selection
- **BooleanWeight**: `boolean-weight.md` -- the simplest projection of provenance (which-provenance)
- **CountingWeight**: `counting-weight.md` -- counting projection (how-many derivations)
- **TropicalWeight**: `tropical-weight.md` -- cost projection (cheapest derivation)
- **Proof output**: `proof_output.rs` -- uses provenance to generate derivation certificates
- **Lint layer**: `lint-layer.md` -- E01 lint emits provenance-annotated diagnostics
