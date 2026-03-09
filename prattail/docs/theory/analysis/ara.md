# ARA -- Affine-Relation Analysis

| Property | Value |
|----------|-------|
| **Feature gate** | `wpds-ara` |
| **Source file** | `prattail/src/ara.rs` (~1659 lines) |
| **Pipeline phase** | WPDS weight domain / interprocedural dataflow |
| **Lint codes** | S05 (`ara-invariant`) |

## 1. Rationale

PraTTaIL grammars with numeric attributes (binding powers, precedence levels,
nesting depths) maintain affine relationships between variables across parse
states. Affine-Relation Analysis (ARA) discovers all such relationships
interprocedurally by modeling the analysis as a WPDS with matrix-valued weights.
ARA strictly subsumes constant propagation, copy-constant propagation, and
linear-constant propagation, making it the most precise analysis in the numeric
domain hierarchy.

## 2. Theoretical Foundations

### 2.1. Affine Relations

**Definition (Affine Relation).** An affine relation over `n` program variables
`x_0, ..., x_{n-1}` is an equation:

```
c_0 * x_0 + c_1 * x_1 + ... + c_{n-1} * x_{n-1} + constant = 0
```

**Definition (Affine Transformation).** An affine transformation is a function
`f(x) = Ax + b` where `A` is an `n x n` matrix and `b` is an `n`-vector. In
homogeneous coordinates, this is represented as an `(n+1) x (n+1)` matrix:

```
    ┌                  ┐   ┌    ┐     ┌                  ┐
    │ a_00  ...  a_0n  │   │ x_0│     │ a_00*x_0 + ... + b_0 │
    │  :          :    │ x │ :  │  =  │        :               │
    │ a_n0  ...  a_nn  │   │x_{n-1}│  │ a_n0*x_0 + ... + b_n │
    │  0    ...   1    │   │  1  │     │          1             │
    └                  ┘   └    ┘     └                        ┘
```

### 2.2. Vector Space Semiring

**Definition (ARA Weight Domain).** The ARA weight domain is
`(VectorSpaces, oplus, otimes, 0, 1)` where:

- Elements are vector spaces of `(n+1) x (n+1)` matrices, represented by
  their basis matrices.
- `oplus` (combine): span of the union of both bases. Computes the join
  (least common superspace).
- `otimes` (extend): span of all pairwise matrix products. Composes two
  affine transformations.
- `0` (zero): empty vector space (no matrices, no affine relations hold).
- `1` (one): vector space spanned by the identity matrix (variables unchanged).

**Theorem (Semiring Laws).** The ARA weight domain satisfies:
1. `(VectorSpaces, oplus, 0)` is a commutative monoid
2. `(VectorSpaces, otimes, 1)` is a monoid
3. `otimes` distributes over `oplus`
4. `0 otimes w = w otimes 0 = 0` (zero annihilation)

### 2.3. Basis Reduction

After each semiring operation, the basis is reduced to canonical form via
Gaussian elimination on the flattened matrix representations. Each
`(n+1) x (n+1)` matrix is flattened to a row vector of length `(n+1)^2`,
and row echelon form is computed.

**Invariant.** After `basis_reduce()`:
1. No basis element is a linear combination of others (minimality).
2. The representation is canonical up to floating-point tolerance `epsilon = 10^{-10}`.
3. The number of basis elements is bounded by `(n+1)^2`.

### 2.4. Subsumption Hierarchy

```
    ┌───────────────────────────────────────────────┐
    │       ARA (Affine-Relation Analysis)          │
    │       ─────────────────────────────           │
    │       x_i = c_0 + c_1*x_1 + ... + c_n*x_n   │
    │                                               │
    │       ┌───────────────────────────────────┐   │
    │       │ Linear-Constant Propagation       │   │
    │       │ x_i = c_0 + c_1*x_1 + ... + c_n*x_n │
    │       │                                   │   │
    │       │  ┌────────────────────────────┐   │   │
    │       │  │ Copy-Constant Propagation  │   │   │
    │       │  │ x_i = x_j + c             │   │   │
    │       │  │                            │   │   │
    │       │  │  ┌─────────────────────┐   │   │   │
    │       │  │  │ Constant Propagation│   │   │   │
    │       │  │  │ x_i = c             │   │   │   │
    │       │  │  └─────────────────────┘   │   │   │
    │       │  └────────────────────────────┘   │   │
    │       └───────────────────────────────────┘   │
    └───────────────────────────────────────────────┘
```

## 3. Algorithm Pseudocode

### 3.1. Combine (Join of Vector Spaces)

```
function combine(self: AraWeight, other: AraWeight) -> AraWeight:
    assert self.dim == other.dim
    combined_bases := self.bases ++ other.bases
    result := AraWeight(combined_bases, self.dim)
    result.basis_reduce()
    return result
```

### 3.2. Extend (Composition of Affine Transformations)

```
function extend(self: AraWeight, other: AraWeight) -> AraWeight:
    if self.bases is empty or other.bases is empty:
        return AraWeight::zero(self.dim)

    products := []
    for A in self.bases:
        for B in other.bases:
            products.push(A * B)    // matrix multiplication

    result := AraWeight(products, self.dim)
    result.basis_reduce()
    return result
```

### 3.3. Basis Reduction (Gaussian Elimination)

```
function basis_reduce(self: AraWeight):
    flat_len := self.dim * self.dim
    // Flatten each basis matrix to a row vector
    mat := Matrix(self.bases.len(), flat_len)
    for i, basis in enumerate(self.bases):
        mat[i] := flatten(basis)

    // Partial-pivoting Gaussian elimination
    pivot_row := 0
    for col in 0..flat_len:
        // Find best pivot in column
        best_row := argmax(|mat[row][col]| for row in pivot_row..num_rows)
        if |mat[best_row][col]| < epsilon: continue

        swap rows best_row and pivot_row
        scale pivot row to make pivot = 1.0
        eliminate all other rows in this column

        pivot_row += 1

    // Extract non-zero rows as reduced basis
    self.bases := [unflatten(mat[i]) for i in 0..pivot_row if norm(mat[i]) > epsilon]
```

## 4. Complexity Analysis

| Operation | Time | Space |
|-----------|------|-------|
| `combine` | O(k * d^4) | O(k * d^2) |
| `extend` | O(k1 * k2 * d^3 + k * d^4) | O(k1 * k2 * d^2) |
| `basis_reduce` | O(k * d^4) | O(k * d^2) |
| `extract_affine_relations` | O(k * d^3) | O(k * d^2) |
| `from_assignment` | O(d^2) | O(d^2) |

Where: k = number of basis matrices (bounded by `d^2`), d = `dim = n + 1`,
n = number of program variables.

The cubic factor `d^3` comes from matrix multiplication; the `d^4` factor in
basis reduction comes from Gaussian elimination on `k` rows of length `d^2`.

## 5. Unicode Diagrams

### 5.1. ARA Weight Domain Architecture

```
    Program variables: x_0, x_1, ..., x_{n-1}

    ┌──────────────────────────────────────────────────┐
    │                AraWeight                         │
    │  ┌────────────────────────────────────────────┐  │
    │  │  bases: Vec<DMatrix<f64>>                  │  │
    │  │                                            │  │
    │  │  M_1 = ┌─────────┐   M_2 = ┌─────────┐   │  │
    │  │        │ a  b  c │         │ d  e  f │   │  │
    │  │        │ g  h  i │         │ j  k  l │   │  │
    │  │        │ 0  0  1 │         │ 0  0  1 │   │  │
    │  │        └─────────┘         └─────────┘   │  │
    │  │                                            │  │
    │  │  dim = n + 1                               │  │
    │  └────────────────────────────────────────────┘  │
    │                                                  │
    │  Semiring operations:                            │
    │    oplus:  span(bases_1 union bases_2)            │
    │    otimes: span({A*B | A in bases_1, B in bases_2}) │
    │    0:      {} (empty basis)                      │
    │    1:      {I} (identity matrix)                 │
    └──────────────────────────────────────────────────┘
```

### 5.2. Affine Relation Extraction

```
    AraWeight with bases M_1, M_2, ...

           ┌──────────────────────────┐
           │  Stack M_1^T, M_2^T, ... │
           │  vertically              │
           └────────────┬─────────────┘
                        │
                        v
           ┌──────────────────────────┐
           │  Compute null space      │
           │  of stacked system       │
           └────────────┬─────────────┘
                        │
                        v
           ┌──────────────────────────┐
           │  Each null vector r =    │
           │  [r_0, ..., r_n]         │
           │                          │
           │  Affine relation:        │
           │  r_0*x_0' + ... + r_n = 0│
           └──────────────────────────┘
```

## 6. PraTTaIL Integration

### 6.1. Pipeline Bridge Functions

- `AraWeight::new(bases, dim)` -- Construct from basis matrices with reduction.
- `AraWeight::from_assignment(var_idx, coefficients, constant, dim)` -- Encode
  a single affine assignment.
- `AraWeight::combine(other)` -- Join of two vector spaces.
- `AraWeight::extend(other)` -- Composition of affine transformations.
- `AraWeight::extract_affine_relations()` -- Discover affine invariants.
- `AraWeight::basis_reduce()` -- Gaussian elimination to canonical form.

### 6.2. Lint Emission

- **S05** (`ara-invariant`): Reports discovered affine invariants at program
  points. Severity: Info. Diagnostic includes the relation in human-readable
  form (e.g., `x_1 = 2*x_0 + 5`).

### 6.3. Repair Integration

ARA results feed into downstream analyses. When an expected invariant does not
hold, the absence is reported as an S05 diagnostic. No automated repair is
generated because affine invariant violations typically indicate semantic issues
in the grammar specification.

## 7. Rust Implementation Notes

| Type | Role |
|------|------|
| `AraWeight` | Vector space of `(n+1) x (n+1)` matrices: `bases: Vec<DMatrix<f64>>`, `dim: usize` |
| `AffineRelation` | Extracted relation: `coefficients: Vec<f64>`, `constant: f64` |
| `HeapSemiring` | Trait from `relational` module, implemented by `AraWeight` |

External dependency: `nalgebra` crate (`DMatrix<f64>`) for matrix operations.

The floating-point tolerance `ARA_EPSILON = 1e-10` is used throughout for
numerical stability. All comparisons in `basis_reduce` and
`extract_affine_relations` respect this tolerance.

The `is_zero()` check tests whether the basis is empty (no matrices). The
`is_one()` check tests whether the basis contains exactly the identity matrix.

## 8. Worked Example

**Program:** 2 variables, `x_0` and `x_1`. Dimension `d = 3` (homogeneous).

```
Statement 1: x_1 = 2 * x_0 + 5
```

**ARA weight for Statement 1:**
```
Matrix M = ┌─────────┐
           │ 1  0  0 │   (x_0 unchanged)
           │ 2  0  5 │   (x_1 = 2*x_0 + 5)
           │ 0  0  1 │   (homogeneous row)
           └─────────┘
AraWeight { bases: [M], dim: 3 }
```

**Composition with identity (no-op statement):**
```
AraWeight::one(3).extend(&w1)
  = span({I * M}) = span({M})
  = AraWeight { bases: [M], dim: 3 }
```

**Extracting affine relations:**
```
Stack M^T:
  ┌─────────┐
  │ 1  2  0 │
  │ 0  0  0 │
  │ 0  5  1 │
  └─────────┘

Null space: r = [c_0, c_1, c_2] such that M^T * r = 0.
  Row 1: c_0 + 2*c_1 = 0  =>  c_0 = -2*c_1
  Row 2: 0 = 0 (trivially satisfied)
  Row 3: 5*c_1 + c_2 = 0  =>  c_2 = -5*c_1

Setting c_1 = 1: r = [-2, 1, -5]
Relation: -2*x_0 + x_1 - 5 = 0  =>  x_1 = 2*x_0 + 5  (correct!)
```

## 9. References

1. Reps, T., Lal, A. & Kidd, N. (2007).
   "Program Analysis Using Weighted Pushdown Systems."
   *Proc. 27th International Conference on Foundations of Software Technology
   and Theoretical Computer Science (FSTTCS)*, LNCS 4855, Springer.

2. Muller-Olm, M. & Seidl, H. (2004).
   "Precise Interprocedural Analysis Through Linear Algebra."
   *Proc. 31st ACM SIGPLAN-SIGACT Symposium on Principles of Programming
   Languages (POPL)*, pp. 330--341.

3. Muller-Olm, M. & Seidl, H. (2005).
   "Analysis of Modular Arithmetic."
   *ACM Transactions on Programming Languages and Systems (TOPLAS)*, 27(3),
   pp. 547--585.

4. Lal, A. & Reps, T. (2006).
   "Improving Pushdown System Model Checking."
   *Proc. 18th International Conference on Computer Aided Verification (CAV)*,
   LNCS 4144, Springer.

5. Kidd, N., Lal, A. & Reps, T. (2007).
   "WALi: the Weighted Automaton Library."
   University of Wisconsin--Madison, Technical Report.
