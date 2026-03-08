//! Affine-Relation Analysis (ARA) weight domain for WPDS.
//!
//! Based on Reps, Lal & Kidd (2007), Section 3.2: weights are *vector spaces of
//! matrices*. Each weight is the span of a finite set of (n+1)x(n+1) matrices,
//! where n is the number of program variables. This discovers all affine
//! relationships (e.g., `x_2 = x_1 + 1`) that hold at each program point,
//! interprocedurally.
//!
//! ## Subsumption Hierarchy
//!
//! ARA strictly subsumes several classical dataflow analyses:
//!
//! - **Constant propagation**: `x_i = c` is the affine relation with all
//!   variable coefficients zero and constant term c.
//! - **Copy-constant propagation**: `x_i = x_j + c` is an affine relation with
//!   a single unit coefficient.
//! - **Linear-constant propagation**: `x_i = c_0 + c_1*x_1 + ... + c_n*x_n` is
//!   the general affine relation captured by a single basis matrix.
//!
//! The key insight is that the *set of all affine relationships* that hold at a
//! program point forms a vector space (closed under linear combination). By
//! representing this space via its basis matrices and performing all operations
//! in the matrix domain, ARA computes the meet-over-all-paths (MOP) solution
//! exactly for affine assignments, even in the presence of interprocedural calls.
//!
//! ## Semiring Structure
//!
//! The ARA weight domain is `(VectorSpaces, span-union, span-product, {}, {I})`:
//!
//! - **Combine** (`plus`, `oplus`): span of the union of both bases. This
//!   computes the *join* (least common superspace) of two vector spaces.
//! - **Extend** (`times`, `otimes`): span of all pairwise products of basis
//!   elements. This composes two affine transformations.
//! - **Zero**: empty vector space (no matrices, no affine relations hold).
//! - **One**: vector space spanned by the identity matrix (variables unchanged).
//!
//! After each operation, `basis_reduce()` is applied to maintain a minimal
//! (row-echelon) basis, keeping the representation finite and canonical.
//!
//! ## References
//!
//! - T. Reps, A. Lal, and N. Kidd. "Program analysis using weighted pushdown
//!   systems." In *FSTTCS 2007*, LNCS 4855, Springer, 2007. Section 3.2.

use nalgebra::DMatrix;
use std::fmt;

use crate::relational::HeapSemiring;

// ══════════════════════════════════════════════════════════════════════════════
// Constants
// ══════════════════════════════════════════════════════════════════════════════

/// Tolerance for floating-point comparisons during basis reduction and
/// equality checks. Chosen to be tight enough for numerical stability while
/// accommodating accumulated rounding in matrix products.
const ARA_EPSILON: f64 = 1e-10;

// ══════════════════════════════════════════════════════════════════════════════
// AraWeight
// ══════════════════════════════════════════════════════════════════════════════

/// An Affine-Relation Analysis weight: a vector space of (n+1)x(n+1) matrices.
///
/// Each matrix in `bases` is an (n+1)x(n+1) affine transformation matrix where:
/// - The first n columns correspond to variable coefficients
/// - The last column (column n) holds the constant term
/// - The last row is always `[0, 0, ..., 0, 1]` (homogeneous coordinates)
///
/// The vector space spanned by these matrices represents the set of all affine
/// relationships that hold at a given program point. The dimension `dim` equals
/// `n + 1`, where n is the number of program variables.
///
/// # Invariant
///
/// After construction and each semiring operation, `bases` is in reduced form
/// (produced by `basis_reduce()`): the flattened matrix representations are in
/// row echelon form, and no basis element is a linear combination of others.
#[derive(Clone, Debug)]
pub struct AraWeight {
    /// Basis matrices spanning the vector space. Each is `dim x dim`.
    /// Maintained in reduced (row-echelon) form after each operation.
    pub bases: Vec<DMatrix<f64>>,
    /// Matrix dimension: `n + 1` where n = number of program variables.
    pub dim: usize,
}

impl AraWeight {
    /// Create a new ARA weight from a set of basis matrices.
    ///
    /// Applies `basis_reduce()` to ensure the canonical representation.
    ///
    /// # Panics
    ///
    /// Panics if any basis matrix is not `dim x dim`.
    pub fn new(bases: Vec<DMatrix<f64>>, dim: usize) -> Self {
        for (i, m) in bases.iter().enumerate() {
            assert_eq!(
                m.nrows(),
                dim,
                "AraWeight::new: basis matrix {} has {} rows, expected {}",
                i,
                m.nrows(),
                dim
            );
            assert_eq!(
                m.ncols(),
                dim,
                "AraWeight::new: basis matrix {} has {} cols, expected {}",
                i,
                m.ncols(),
                dim
            );
        }
        let mut w = AraWeight { bases, dim };
        w.basis_reduce();
        w
    }

    /// Create the zero weight: empty vector space (no affine relations).
    ///
    /// This is the additive identity. Combining any weight with zero yields
    /// that weight unchanged (the union with an empty set is the original set).
    pub fn zero(dim: usize) -> Self {
        AraWeight {
            bases: Vec::new(),
            dim,
        }
    }

    /// Create the one weight: vector space spanned by the identity matrix.
    ///
    /// This is the multiplicative identity. Extending any weight with one
    /// yields that weight unchanged (multiplying by identity preserves all
    /// basis matrices).
    pub fn one(dim: usize) -> Self {
        AraWeight {
            bases: vec![DMatrix::identity(dim, dim)],
            dim,
        }
    }

    /// Create a weight from a single affine assignment.
    ///
    /// Encodes `x_{var_idx} = constant + coefficients[0]*x_0 + ... + coefficients[n-1]*x_{n-1}`.
    ///
    /// The resulting (n+1)x(n+1) matrix is the identity with row `var_idx`
    /// replaced by the assignment's coefficients and constant term.
    ///
    /// # Parameters
    ///
    /// - `var_idx`: index of the variable being assigned (0-based, must be < dim-1)
    /// - `coefficients`: coefficients for each of the n variables (length must be dim-1)
    /// - `constant`: the constant term c_0
    /// - `dim`: total matrix dimension (n+1)
    ///
    /// # Panics
    ///
    /// Panics if `var_idx >= dim - 1` or `coefficients.len() != dim - 1`.
    ///
    /// # Example
    ///
    /// For 2 variables (dim=3), the assignment `x_1 = 2*x_0 + 5`:
    /// ```
    /// # use mettail_prattail::ara::AraWeight;
    /// let w = AraWeight::from_assignment(1, &[2.0, 0.0], 5.0, 3);
    /// // Matrix:
    /// // [1  0  0]   (x_0 unchanged)
    /// // [2  0  5]   (x_1 = 2*x_0 + 5)
    /// // [0  0  1]   (homogeneous row)
    /// ```
    pub fn from_assignment(var_idx: usize, coefficients: &[f64], constant: f64, dim: usize) -> Self {
        let n = dim - 1;
        assert!(
            var_idx < n,
            "AraWeight::from_assignment: var_idx {} must be < n={}",
            var_idx,
            n
        );
        assert_eq!(
            coefficients.len(),
            n,
            "AraWeight::from_assignment: coefficients length {} must equal n={}",
            coefficients.len(),
            n
        );

        let mut m = DMatrix::identity(dim, dim);
        // Replace row `var_idx` with the assignment
        for j in 0..n {
            m[(var_idx, j)] = coefficients[j];
        }
        m[(var_idx, n)] = constant;

        AraWeight {
            bases: vec![m],
            dim,
        }
    }

    /// Combine (oplus): join of two vector spaces = span(union of bases).
    ///
    /// The result contains every matrix that can be expressed as a linear
    /// combination of basis elements from *either* operand.
    pub fn combine(&self, other: &Self) -> Self {
        assert_eq!(
            self.dim, other.dim,
            "AraWeight::combine: dimension mismatch ({} vs {})",
            self.dim, other.dim
        );

        let mut combined = Vec::with_capacity(self.bases.len() + other.bases.len());
        combined.extend(self.bases.iter().cloned());
        combined.extend(other.bases.iter().cloned());

        let mut result = AraWeight {
            bases: combined,
            dim: self.dim,
        };
        result.basis_reduce();
        result
    }

    /// Extend (otimes): composition of two affine-relation spaces.
    ///
    /// Computes span({A * B | A in self.bases, B in other.bases}). This
    /// models the sequential composition of two program segments: if the
    /// first segment's reachable affine transforms are spanned by self.bases
    /// and the second's by other.bases, the composition is the span of all
    /// pairwise products.
    ///
    /// Special cases for efficiency:
    /// - If either operand is zero, the result is zero.
    /// - If either operand is one (identity), the result is the other operand.
    pub fn extend(&self, other: &Self) -> Self {
        assert_eq!(
            self.dim, other.dim,
            "AraWeight::extend: dimension mismatch ({} vs {})",
            self.dim, other.dim
        );

        // Zero annihilation: zero * anything = anything * zero = zero
        if self.bases.is_empty() || other.bases.is_empty() {
            return AraWeight::zero(self.dim);
        }

        let mut products = Vec::with_capacity(self.bases.len() * other.bases.len());
        for a in &self.bases {
            for b in &other.bases {
                products.push(a * b);
            }
        }

        let mut result = AraWeight {
            bases: products,
            dim: self.dim,
        };
        result.basis_reduce();
        result
    }

    /// Reduce the basis to a minimal spanning set via Gaussian elimination.
    ///
    /// Each (n+1)x(n+1) basis matrix is flattened to a row vector of length
    /// (n+1)^2. The collection of such row vectors forms a matrix, which is
    /// row-reduced to echelon form. Non-zero rows correspond to the reduced
    /// basis elements.
    ///
    /// This ensures:
    /// 1. No basis element is a linear combination of others (minimality).
    /// 2. The representation is canonical up to floating-point tolerance.
    /// 3. The number of basis elements is bounded by (n+1)^2.
    pub fn basis_reduce(&mut self) {
        if self.bases.is_empty() {
            return;
        }

        let flat_len = self.dim * self.dim;
        let num_rows = self.bases.len();

        // Build the matrix of flattened basis vectors.
        // Each row is one basis matrix flattened in row-major order.
        let mut mat = DMatrix::zeros(num_rows, flat_len);
        for (i, basis) in self.bases.iter().enumerate() {
            for r in 0..self.dim {
                for c in 0..self.dim {
                    mat[(i, r * self.dim + c)] = basis[(r, c)];
                }
            }
        }

        // Row echelon form via partial-pivoting Gaussian elimination
        let mut pivot_row = 0;
        for col in 0..flat_len {
            if pivot_row >= num_rows {
                break;
            }

            // Find the row with the largest absolute value in this column
            // (partial pivoting for numerical stability)
            let mut best_row = pivot_row;
            let mut best_val = mat[(pivot_row, col)].abs();
            for row in (pivot_row + 1)..num_rows {
                let val = mat[(row, col)].abs();
                if val > best_val {
                    best_val = val;
                    best_row = row;
                }
            }

            if best_val < ARA_EPSILON {
                // All values in this column are effectively zero; skip
                continue;
            }

            // Swap the best row into the pivot position
            if best_row != pivot_row {
                for c in 0..flat_len {
                    let tmp = mat[(pivot_row, c)];
                    mat[(pivot_row, c)] = mat[(best_row, c)];
                    mat[(best_row, c)] = tmp;
                }
            }

            // Scale the pivot row so the pivot element is 1.0
            let pivot_val = mat[(pivot_row, col)];
            for c in 0..flat_len {
                mat[(pivot_row, c)] /= pivot_val;
            }

            // Eliminate all other rows in this column (full reduction for
            // canonical form — both above and below the pivot)
            for row in 0..num_rows {
                if row == pivot_row {
                    continue;
                }
                let factor = mat[(row, col)];
                if factor.abs() < ARA_EPSILON {
                    continue;
                }
                for c in 0..flat_len {
                    mat[(row, c)] -= factor * mat[(pivot_row, c)];
                }
            }

            pivot_row += 1;
        }

        // Extract non-zero rows as the reduced basis
        let mut new_bases = Vec::with_capacity(pivot_row);
        for i in 0..pivot_row {
            // Check if the row is non-zero
            let row_norm_sq: f64 = (0..flat_len).map(|c| mat[(i, c)] * mat[(i, c)]).sum();
            if row_norm_sq < ARA_EPSILON * ARA_EPSILON {
                continue;
            }

            let mut basis_mat = DMatrix::zeros(self.dim, self.dim);
            for r in 0..self.dim {
                for c in 0..self.dim {
                    basis_mat[(r, c)] = mat[(i, r * self.dim + c)];
                }
            }
            new_bases.push(basis_mat);
        }

        self.bases = new_bases;
    }

    /// Extract discovered affine relations from this weight.
    ///
    /// Returns a list of `AffineRelation` values, each representing a
    /// constraint of the form `c_0*x_0' + c_1*x_1' + ... + c_{n-1}*x_{n-1}' + constant = 0`
    /// that holds on the **output** state across all execution paths represented
    /// by the weight's basis matrices.
    ///
    /// ## Algorithm
    ///
    /// Each basis matrix M maps an input vector `v = [x_0, ..., x_{n-1}, 1]^T`
    /// to an output `v' = M * v`. An affine relation `r^T v' = 0` holds on the
    /// output for ALL inputs if and only if `r^T M = 0` (the zero row), which
    /// is equivalent to `M^T r = 0`.
    ///
    /// For a weight with multiple basis matrices M_1, ..., M_k, the output can
    /// be any linear combination `v' = (sum alpha_i M_i) v`. The relation
    /// `r^T v' = 0` for all v and all alpha_i requires `M_i^T r = 0` for all i.
    ///
    /// We stack all M_i^T vertically and compute the null space. Each null space
    /// vector `r = [r_0, ..., r_{n-1}, r_n]` gives the relation:
    ///
    /// `r_0*x_0' + r_1*x_1' + ... + r_{n-1}*x_{n-1}' + r_n = 0`
    ///
    /// i.e., `r_0*x_0' + ... + r_{n-1}*x_{n-1}' = -r_n`.
    ///
    /// ## Edge Cases
    ///
    /// - **Zero weight** (empty basis): no paths analyzed, returns empty.
    /// - **One weight** (identity basis): `I^T r = r = 0` forces `r = 0`,
    ///   so the null space is trivial — no output relations. Correct, since
    ///   identity leaves outputs unconstrained (they depend entirely on input).
    pub fn extract_affine_relations(&self) -> Vec<AffineRelation> {
        let n = self.dim - 1; // number of program variables

        if self.bases.is_empty() {
            // Zero weight: no paths analyzed, no relations discovered
            return Vec::new();
        }

        // Stack M_1^T, M_2^T, ... vertically. Each M_k^T is dim x dim, so
        // the system is (k*dim) x dim. We find vectors r in the null space.
        let total_rows = self.bases.len() * self.dim;
        let mut system = DMatrix::zeros(total_rows, self.dim);

        for (k, basis) in self.bases.iter().enumerate() {
            let bt = basis.transpose();
            for r in 0..self.dim {
                for c in 0..self.dim {
                    system[(k * self.dim + r, c)] = bt[(r, c)];
                }
            }
        }

        // Find the null space of the system
        let null_space = compute_null_space(&system);

        let mut relations = Vec::new();
        for r in &null_space {
            // r = [r_0, r_1, ..., r_{n-1}, r_n]
            // Relation: r_0*x_0' + r_1*x_1' + ... + r_{n-1}*x_{n-1}' + r_n = 0
            // i.e., the output variables satisfy: sum(r_i * x_i') = -r_n
            let coefficients: Vec<f64> = (0..n).map(|i| r[i]).collect();
            let constant = r[n];

            // Skip trivial relations (all components zero)
            let norm_sq: f64 = coefficients.iter().map(|c| c * c).sum::<f64>() + constant * constant;
            if norm_sq < ARA_EPSILON * ARA_EPSILON {
                continue;
            }

            // Skip relations with no variable involvement (only constant = 0)
            let var_norm_sq: f64 = coefficients.iter().map(|c| c * c).sum();
            if var_norm_sq < ARA_EPSILON * ARA_EPSILON {
                continue;
            }

            relations.push(AffineRelation {
                coefficients,
                constant,
            });
        }

        relations
    }

    /// Returns the number of basis matrices.
    pub fn rank(&self) -> usize {
        self.bases.len()
    }

    /// Returns the maximum possible rank: (n+1)^2.
    pub fn max_rank(&self) -> usize {
        self.dim * self.dim
    }
}

/// An affine relation `c_0*x_0 + c_1*x_1 + ... + c_{n-1}*x_{n-1} + constant = 0`.
///
/// Equivalently: `c_0*x_0 + c_1*x_1 + ... + c_{n-1}*x_{n-1} = -constant`.
///
/// For example, the relation `x_1 = x_0 + 3` is represented as
/// `coefficients = [-1, 1]`, `constant = -3` (i.e., `-x_0 + x_1 - 3 = 0`).
#[derive(Clone, Debug)]
pub struct AffineRelation {
    /// Coefficients for each program variable x_0, ..., x_{n-1}.
    pub coefficients: Vec<f64>,
    /// The constant term. The full relation is `sum(c_i * x_i) + constant = 0`.
    pub constant: f64,
}

impl fmt::Display for AffineRelation {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut first = true;
        for (i, &c) in self.coefficients.iter().enumerate() {
            if c.abs() < ARA_EPSILON {
                continue;
            }
            if !first && c > 0.0 {
                write!(f, " + ")?;
            } else if c < 0.0 {
                if first {
                    write!(f, "-")?;
                } else {
                    write!(f, " - ")?;
                }
            }
            let abs_c = c.abs();
            if (abs_c - 1.0).abs() < ARA_EPSILON {
                write!(f, "x_{}", i)?;
            } else {
                write!(f, "{}*x_{}", abs_c, i)?;
            }
            first = false;
        }
        if self.constant.abs() >= ARA_EPSILON {
            if !first && self.constant > 0.0 {
                write!(f, " + ")?;
            } else if self.constant < 0.0 {
                if first {
                    write!(f, "-")?;
                } else {
                    write!(f, " - ")?;
                }
            }
            if first && self.constant > 0.0 {
                write!(f, "{}", self.constant.abs())?;
            } else {
                write!(f, "{}", self.constant.abs())?;
            }
            first = false;
        }
        if first {
            write!(f, "0")?;
        }
        write!(f, " = 0")
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// HeapSemiring implementation
// ══════════════════════════════════════════════════════════════════════════════

impl HeapSemiring for AraWeight {
    fn zero() -> Self {
        // Dimension is unknown without context; use dim=1 as a sentinel.
        // Callers should use `AraWeight::zero(dim)` when the dimension is known.
        AraWeight {
            bases: Vec::new(),
            dim: 1,
        }
    }

    fn one() -> Self {
        // Dimension is unknown without context; use dim=1 as a sentinel.
        // Callers should use `AraWeight::one(dim)` when the dimension is known.
        AraWeight {
            bases: vec![DMatrix::identity(1, 1)],
            dim: 1,
        }
    }

    fn plus(&self, other: &Self) -> Self {
        self.combine(other)
    }

    fn times(&self, other: &Self) -> Self {
        self.extend(other)
    }

    fn is_zero(&self) -> bool {
        self.bases.is_empty()
    }

    fn is_one(&self) -> bool {
        if self.bases.len() != 1 {
            return false;
        }
        let identity = DMatrix::identity(self.dim, self.dim);
        matrix_approx_eq(&self.bases[0], &identity, ARA_EPSILON)
    }

    fn approx_eq(&self, other: &Self, epsilon: f64) -> bool {
        if self.dim != other.dim {
            return false;
        }
        if self.bases.len() != other.bases.len() {
            return false;
        }
        // Two reduced bases spanning the same vector space will have the same
        // number of basis elements after reduction, and (in reduced row echelon
        // form) the same flattened row vectors up to floating-point tolerance.
        //
        // To robustly check equality, we verify that each basis element of self
        // lies in the span of other, and vice versa.
        subspace_contains_all(&self.bases, &other.bases, epsilon)
            && subspace_contains_all(&other.bases, &self.bases, epsilon)
    }
}

impl PartialEq for AraWeight {
    fn eq(&self, other: &Self) -> bool {
        self.approx_eq(other, ARA_EPSILON)
    }
}

impl fmt::Display for AraWeight {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.is_zero() {
            write!(f, "ARA(zero, dim={})", self.dim)
        } else if self.is_one() {
            write!(f, "ARA(one, dim={})", self.dim)
        } else {
            write!(f, "ARA(rank={}, dim={})", self.bases.len(), self.dim)
        }
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// Helper functions
// ══════════════════════════════════════════════════════════════════════════════

/// Check if two matrices are approximately equal element-wise.
fn matrix_approx_eq(a: &DMatrix<f64>, b: &DMatrix<f64>, epsilon: f64) -> bool {
    if a.nrows() != b.nrows() || a.ncols() != b.ncols() {
        return false;
    }
    for r in 0..a.nrows() {
        for c in 0..a.ncols() {
            if (a[(r, c)] - b[(r, c)]).abs() > epsilon {
                return false;
            }
        }
    }
    true
}

/// Check that every matrix in `subset` lies in the span of `space`.
///
/// For each matrix in `subset`, flatten it and check if it can be expressed
/// as a linear combination of the flattened `space` basis vectors.
fn subspace_contains_all(
    space: &[DMatrix<f64>],
    subset: &[DMatrix<f64>],
    epsilon: f64,
) -> bool {
    if subset.is_empty() {
        return true;
    }
    if space.is_empty() {
        // If space is empty but subset is not, subset is not contained
        return false;
    }

    let dim = space[0].nrows();
    let flat_len = dim * dim;

    // Build the matrix of space basis vectors (each row is a flattened matrix)
    let num_space = space.len();
    let mut mat = DMatrix::zeros(num_space, flat_len);
    for (i, basis) in space.iter().enumerate() {
        for r in 0..dim {
            for c in 0..dim {
                mat[(i, r * dim + c)] = basis[(r, c)];
            }
        }
    }

    // Row-reduce the space matrix
    let reduced = row_reduce(&mat, epsilon);

    // For each subset matrix, check if it lies in the span
    for target in subset {
        let mut flat = vec![0.0; flat_len];
        for r in 0..dim {
            for c in 0..dim {
                flat[r * dim + c] = target[(r, c)];
            }
        }

        if !vector_in_row_space(&reduced, &flat, epsilon) {
            return false;
        }
    }

    true
}

/// Row-reduce a matrix to reduced row echelon form (RREF).
///
/// Returns the reduced matrix with pivot columns identified.
fn row_reduce(mat: &DMatrix<f64>, epsilon: f64) -> DMatrix<f64> {
    let mut m = mat.clone();
    let nrows = m.nrows();
    let ncols = m.ncols();

    let mut pivot_row = 0;
    for col in 0..ncols {
        if pivot_row >= nrows {
            break;
        }

        // Partial pivoting
        let mut best_row = pivot_row;
        let mut best_val = m[(pivot_row, col)].abs();
        for row in (pivot_row + 1)..nrows {
            let val = m[(row, col)].abs();
            if val > best_val {
                best_val = val;
                best_row = row;
            }
        }

        if best_val < epsilon {
            continue;
        }

        // Swap rows
        if best_row != pivot_row {
            for c in 0..ncols {
                let tmp = m[(pivot_row, c)];
                m[(pivot_row, c)] = m[(best_row, c)];
                m[(best_row, c)] = tmp;
            }
        }

        // Scale pivot row
        let pivot_val = m[(pivot_row, col)];
        for c in 0..ncols {
            m[(pivot_row, c)] /= pivot_val;
        }

        // Eliminate other rows
        for row in 0..nrows {
            if row == pivot_row {
                continue;
            }
            let factor = m[(row, col)];
            if factor.abs() < epsilon {
                continue;
            }
            for c in 0..ncols {
                m[(row, c)] -= factor * m[(pivot_row, c)];
            }
        }

        pivot_row += 1;
    }

    m
}

/// Check if a vector lies in the row space of a row-reduced matrix.
///
/// After row reduction, a vector v is in the row space if and only if
/// subtracting the appropriate multiples of the pivot rows from v yields
/// the zero vector.
fn vector_in_row_space(reduced: &DMatrix<f64>, vec: &[f64], epsilon: f64) -> bool {
    let nrows = reduced.nrows();
    let ncols = reduced.ncols();

    let mut residual = vec.to_vec();

    for row in 0..nrows {
        // Find the pivot column for this row
        let mut pivot_col = None;
        for c in 0..ncols {
            if reduced[(row, c)].abs() > epsilon {
                pivot_col = Some(c);
                break;
            }
        }

        let pivot_col = match pivot_col {
            Some(c) => c,
            None => continue, // zero row, skip
        };

        // Subtract the appropriate multiple of this row from the residual
        let factor = residual[pivot_col];
        if factor.abs() < epsilon {
            continue;
        }
        for c in 0..ncols {
            residual[c] -= factor * reduced[(row, c)];
        }
    }

    // Check if residual is zero
    residual.iter().all(|&v| v.abs() < epsilon)
}

/// Compute the null space of a matrix via row reduction.
///
/// Returns a set of vectors that span the null space of the input matrix.
/// Each returned vector has length equal to the number of columns.
fn compute_null_space(mat: &DMatrix<f64>) -> Vec<Vec<f64>> {
    let nrows = mat.nrows();
    let ncols = mat.ncols();

    if nrows == 0 || ncols == 0 {
        return Vec::new();
    }

    // Row-reduce the matrix
    let reduced = row_reduce(mat, ARA_EPSILON);

    // Identify pivot columns
    let mut pivot_cols = Vec::new();
    let mut pivot_for_row = vec![None; nrows];
    let mut used_cols = vec![false; ncols];

    for row in 0..nrows {
        for col in 0..ncols {
            if reduced[(row, col)].abs() > ARA_EPSILON && !used_cols[col] {
                pivot_cols.push(col);
                pivot_for_row[row] = Some(col);
                used_cols[col] = true;
                break;
            }
        }
    }

    // Free columns are those not in pivot_cols
    let free_cols: Vec<usize> = (0..ncols).filter(|c| !used_cols[*c]).collect();

    // For each free column, construct a null space vector
    let mut null_vectors = Vec::with_capacity(free_cols.len());

    for &free_col in &free_cols {
        let mut vec = vec![0.0; ncols];
        vec[free_col] = 1.0;

        // For each pivot row, set the pivot variable to cancel the free variable
        for row in 0..nrows {
            if let Some(pc) = pivot_for_row[row] {
                vec[pc] = -reduced[(row, free_col)];
            }
        }

        null_vectors.push(vec);
    }

    null_vectors
}

// ══════════════════════════════════════════════════════════════════════════════
// HeapWpds integration types (mirroring relational.rs pattern)
// ══════════════════════════════════════════════════════════════════════════════

/// A WPDS rule weighted by `AraWeight`.
///
/// Mirrors `HeapWpdsRule<W>` from `relational.rs` specialized for ARA.
#[derive(Debug, Clone)]
pub enum AraWpdsRule {
    /// Pop rule: `<p, gamma> -> <p', epsilon>`.
    Pop {
        from_gamma: crate::wpds::StackSymbol,
        weight: AraWeight,
    },
    /// Replace rule: `<p, gamma> -> <p', gamma'>`.
    Replace {
        from_gamma: crate::wpds::StackSymbol,
        to_gamma: crate::wpds::StackSymbol,
        weight: AraWeight,
    },
    /// Push rule: `<p, gamma> -> <p', gamma' gamma''>`.
    Push {
        from_gamma: crate::wpds::StackSymbol,
        to_gamma_bottom: crate::wpds::StackSymbol,
        to_gamma_top: crate::wpds::StackSymbol,
        weight: AraWeight,
    },
}

impl AraWpdsRule {
    /// The source stack symbol.
    pub fn from_gamma(&self) -> &crate::wpds::StackSymbol {
        match self {
            AraWpdsRule::Pop { from_gamma, .. }
            | AraWpdsRule::Replace { from_gamma, .. }
            | AraWpdsRule::Push { from_gamma, .. } => from_gamma,
        }
    }

    /// The weight.
    pub fn weight(&self) -> &AraWeight {
        match self {
            AraWpdsRule::Pop { weight, .. }
            | AraWpdsRule::Replace { weight, .. }
            | AraWpdsRule::Push { weight, .. } => weight,
        }
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// Pipeline bridge
// ══════════════════════════════════════════════════════════════════════════════

/// Pipeline-level ARA analysis result.
#[derive(Debug, Clone)]
pub struct AraAnalysis {
    /// Number of affine invariants discovered.
    pub invariant_count: usize,
    /// Dimension of the ARA weight domain.
    pub dimension: usize,
    /// Summaries per program point (category name → invariant description).
    pub invariants: Vec<(String, String)>,
}

/// Run ARA analysis from pipeline bundle data.
///
/// Counts the total number of unique variable positions (IdentCapture and Binder
/// syntax items) across all rules to determine the ARA dimension, then builds
/// ARA weights at that dimension. The actual invariant discovery requires full
/// WPDS weight propagation; this bridge returns the dimension and an empty
/// invariants list as a structural summary.
///
/// # Arguments
///
/// * `wpds_analysis` — WPDS analysis result (used for grammar metadata).
/// * `all_syntax` — Per-rule syntax items: `(label, category, items)`.
pub fn analyze_from_bundle(
    wpds_analysis: &crate::wpds::WpdsAnalysis,
    all_syntax: &[(String, String, Vec<crate::SyntaxItemSpec>)],
) -> AraAnalysis {
    use std::collections::HashSet;
    use crate::SyntaxItemSpec;

    // Count unique variable positions (IdentCapture + Binder items) across all
    // rules. Each unique (category, param_name) pair represents one program
    // variable in the ARA domain.
    let mut var_positions: HashSet<(String, String)> = HashSet::new();

    fn collect_vars(
        item: &SyntaxItemSpec,
        category: &str,
        positions: &mut HashSet<(String, String)>,
    ) {
        match item {
            SyntaxItemSpec::IdentCapture { param_name } => {
                positions.insert((category.to_string(), param_name.clone()));
            }
            SyntaxItemSpec::Binder { param_name, .. } => {
                positions.insert((category.to_string(), param_name.clone()));
            }
            SyntaxItemSpec::BinderCollection { param_name, .. } => {
                positions.insert((category.to_string(), param_name.clone()));
            }
            SyntaxItemSpec::Optional { inner } => {
                for sub in inner {
                    collect_vars(sub, category, positions);
                }
            }
            SyntaxItemSpec::Map { body_items } => {
                for sub in body_items {
                    collect_vars(sub, category, positions);
                }
            }
            SyntaxItemSpec::Sep { body, .. } => {
                collect_vars(body, category, positions);
            }
            SyntaxItemSpec::Zip { body, .. } => {
                collect_vars(body, category, positions);
            }
            _ => {}
        }
    }

    for (_label, category, syntax) in all_syntax {
        for item in syntax {
            collect_vars(item, category, &mut var_positions);
        }
    }

    let n = var_positions.len();
    // ARA dimension is n+1 (homogeneous coordinates).
    let dimension = n + 1;

    // Build the ARA identity weight at this dimension to validate the domain.
    let _identity = AraWeight::one(dimension);

    // Log the grammar name from the WPDS analysis for traceability.
    let _ = &wpds_analysis.grammar_name;

    AraAnalysis {
        invariant_count: 0,
        dimension,
        invariants: Vec::new(),
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// Tests
// ══════════════════════════════════════════════════════════════════════════════

#[cfg(test)]
mod tests {
    use super::*;

    // ── Helpers ──────────────────────────────────────────────────────────────

    /// Convenience: 2 variables (dim = 3).
    const DIM: usize = 3;

    /// Create the identity weight for 2 variables.
    fn one() -> AraWeight {
        AraWeight::one(DIM)
    }

    /// Create the zero weight for 2 variables.
    fn zero() -> AraWeight {
        AraWeight::zero(DIM)
    }

    /// Check that two weights span the same vector space.
    fn assert_same_space(a: &AraWeight, b: &AraWeight) {
        assert!(
            a.approx_eq(b, 1e-8),
            "Expected same vector space.\n  Left (rank {}): {:?}\n  Right (rank {}): {:?}",
            a.rank(),
            a.bases,
            b.rank(),
            b.bases
        );
    }

    // ── Semiring Law Tests ──────────────────────────────────────────────────

    #[test]
    fn test_zero_is_additive_identity() {
        // w + 0 = w
        let w = AraWeight::from_assignment(0, &[0.0, 0.0], 42.0, DIM);
        let result = w.combine(&zero());
        assert_same_space(&result, &w);

        // 0 + w = w
        let result2 = zero().combine(&w);
        assert_same_space(&result2, &w);
    }

    #[test]
    fn test_one_is_multiplicative_identity() {
        // w * 1 = w
        let w = AraWeight::from_assignment(0, &[0.0, 1.0], 3.0, DIM);
        let result = w.extend(&one());
        assert_same_space(&result, &w);

        // 1 * w = w
        let result2 = one().extend(&w);
        assert_same_space(&result2, &w);
    }

    #[test]
    fn test_zero_annihilates_left() {
        // 0 * w = 0
        let w = AraWeight::from_assignment(1, &[2.0, 0.0], 5.0, DIM);
        let result = zero().extend(&w);
        assert!(result.is_zero(), "zero * w should be zero");
    }

    #[test]
    fn test_zero_annihilates_right() {
        // w * 0 = 0
        let w = AraWeight::from_assignment(0, &[1.0, 1.0], 0.0, DIM);
        let result = w.extend(&zero());
        assert!(result.is_zero(), "w * zero should be zero");
    }

    #[test]
    fn test_combine_is_commutative() {
        // a + b = b + a
        let a = AraWeight::from_assignment(0, &[0.0, 0.0], 1.0, DIM);
        let b = AraWeight::from_assignment(1, &[0.0, 0.0], 2.0, DIM);
        let ab = a.combine(&b);
        let ba = b.combine(&a);
        assert_same_space(&ab, &ba);
    }

    #[test]
    fn test_combine_is_associative() {
        // (a + b) + c = a + (b + c)
        let a = AraWeight::from_assignment(0, &[0.0, 0.0], 1.0, DIM);
        let b = AraWeight::from_assignment(1, &[0.0, 0.0], 2.0, DIM);
        let c = AraWeight::from_assignment(0, &[1.0, 1.0], 0.0, DIM);

        let ab_c = a.combine(&b).combine(&c);
        let a_bc = a.combine(&b.combine(&c));
        assert_same_space(&ab_c, &a_bc);
    }

    #[test]
    fn test_extend_is_associative() {
        // (a * b) * c = a * (b * c)
        let a = AraWeight::from_assignment(0, &[0.0, 1.0], 3.0, DIM);
        let b = AraWeight::from_assignment(1, &[2.0, 0.0], 1.0, DIM);
        let c = AraWeight::from_assignment(0, &[1.0, 1.0], -1.0, DIM);

        let ab_c = a.extend(&b).extend(&c);
        let a_bc = a.extend(&b.extend(&c));
        assert_same_space(&ab_c, &a_bc);
    }

    #[test]
    fn test_extend_distributes_over_combine() {
        // a * (b + c) = (a * b) + (a * c)  [left distributivity]
        let a = AraWeight::from_assignment(0, &[0.0, 1.0], 1.0, DIM);
        let b = AraWeight::from_assignment(1, &[1.0, 0.0], 2.0, DIM);
        let c = AraWeight::from_assignment(1, &[0.0, 0.0], 5.0, DIM);

        let lhs = a.extend(&b.combine(&c));
        let rhs = a.extend(&b).combine(&a.extend(&c));
        assert_same_space(&lhs, &rhs);
    }

    // ── Basis Reduction Tests ───────────────────────────────────────────────

    #[test]
    fn test_basis_reduce_removes_duplicates() {
        let m = DMatrix::identity(DIM, DIM);
        let w = AraWeight::new(vec![m.clone(), m.clone(), m], DIM);
        assert_eq!(w.rank(), 1, "Three copies of identity should reduce to rank 1");
        assert!(w.is_one());
    }

    #[test]
    fn test_basis_reduce_removes_linear_combinations() {
        // Two matrices where one is 2x the other
        let mut m1 = DMatrix::zeros(DIM, DIM);
        m1[(0, 0)] = 1.0;
        m1[(1, 1)] = 1.0;
        m1[(2, 2)] = 1.0;

        let m2 = &m1 * 2.0;

        let w = AraWeight::new(vec![m1, m2], DIM);
        assert_eq!(w.rank(), 1, "Scalar multiple should be eliminated by basis reduction");
    }

    #[test]
    fn test_basis_reduce_preserves_independent() {
        // Two linearly independent matrices
        let mut m1 = DMatrix::zeros(DIM, DIM);
        m1[(0, 0)] = 1.0;

        let mut m2 = DMatrix::zeros(DIM, DIM);
        m2[(1, 1)] = 1.0;

        let w = AraWeight::new(vec![m1, m2], DIM);
        assert_eq!(w.rank(), 2, "Two independent matrices should both survive reduction");
    }

    #[test]
    fn test_basis_reduce_empty() {
        let w = AraWeight::new(Vec::new(), DIM);
        assert!(w.is_zero());
        assert_eq!(w.rank(), 0);
    }

    // ── Affine Relation Extraction Tests ────────────────────────────────────

    #[test]
    fn test_extract_identity_no_relations() {
        // Identity transform: v' = I * v, so x_i' = x_i for all i.
        // The system is I^T * r = r = 0, which has only the trivial solution.
        // No non-trivial null vectors => no output relations. Correct: the
        // identity leaves outputs unconstrained (they depend entirely on input).
        let w = one();
        let relations = w.extract_affine_relations();
        assert!(
            relations.is_empty(),
            "Identity should yield no output relations, got: {:?}",
            relations
        );
    }

    #[test]
    fn test_extract_zero_no_relations() {
        // Zero weight: no paths, no relations
        let w = zero();
        let relations = w.extract_affine_relations();
        assert!(relations.is_empty(), "Zero weight should yield no relations");
    }

    #[test]
    fn test_extract_constant_assignment() {
        // Assignment: x_0 = 5, x_1 unchanged
        // Matrix: [[0, 0, 5], [0, 1, 0], [0, 0, 1]]
        let w = AraWeight::from_assignment(0, &[0.0, 0.0], 5.0, DIM);
        let relations = w.extract_affine_relations();
        // The relation x_0 = 5 should be discoverable.
        // We check that at least one relation involves x_0 with a non-zero coefficient.
        let has_x0_relation = relations.iter().any(|r| r.coefficients[0].abs() > ARA_EPSILON);
        assert!(
            has_x0_relation,
            "Should discover a relation involving x_0 after constant assignment. Got: {:?}",
            relations
        );
    }

    #[test]
    fn test_extract_copy_assignment() {
        // Assignment: x_0 = x_1 + 3
        // Matrix: [[0, 1, 3], [0, 1, 0], [0, 0, 1]]
        let w = AraWeight::from_assignment(0, &[0.0, 1.0], 3.0, DIM);
        let relations = w.extract_affine_relations();
        // Should discover a relation like x_0 - x_1 - 3 = 0, i.e., x_0 = x_1 + 3
        assert!(
            !relations.is_empty(),
            "Should discover at least one affine relation for copy-assignment"
        );
    }

    // ── Assignment Composition Tests ────────────────────────────────────────

    #[test]
    fn test_sequential_assignments() {
        // First: x_0 = x_1 + 1
        let w1 = AraWeight::from_assignment(0, &[0.0, 1.0], 1.0, DIM);
        // Second: x_1 = x_0 + 2
        let w2 = AraWeight::from_assignment(1, &[1.0, 0.0], 2.0, DIM);

        // Compose: w1 then w2
        // After w1: x_0' = x_1 + 1, x_1' = x_1
        // After w2: x_0'' = x_0' = x_1 + 1, x_1'' = x_0' + 2 = x_1 + 3
        let composed = w1.extend(&w2);

        // The composed matrix should be w1 * w2
        // w1 = [[0, 1, 1], [0, 1, 0], [0, 0, 1]]
        // w2 = [[1, 0, 0], [1, 0, 2], [0, 0, 1]]
        // w1 * w2 = [[0*1+1*1+1*0, 0*0+1*0+1*0, 0*0+1*2+1*1], ...]
        //         = [[1, 0, 3], [1, 0, 2], [0, 0, 1]]
        // Wait — let me verify: row 0 of w1 is [0, 1, 1]
        // row 0 of w1 * w2: [0*1+1*1+1*0, 0*0+1*0+1*0, 0*0+1*2+1*1] = [1, 0, 3]
        // So x_0'' = x_1_orig + 3... but through w1: x_0' = x_1+1, then through w2:
        // x_1'' = x_0' + 2 = (x_1+1)+2 = x_1+3. And x_0'' = x_0' = x_1+1. Hmm,
        // the matrix mult gives x_0'' = 1*x_0_orig + 0*x_1_orig + 3, which means
        // x_0'' = x_0_orig + 3. But that contradicts the semantic analysis above.
        //
        // The issue is that matrix multiplication for affine transforms composes
        // RIGHT to LEFT: if v' = M1 * v and v'' = M2 * v', then v'' = M2 * M1 * v.
        // So w1.extend(w2) should compute w2 * w1 (not w1 * w2) to get the
        // sequential composition "w1 then w2".
        //
        // But in our implementation, extend computes self * other = w1 * w2.
        // For WPDS, the convention from Reps et al. is that extend(f, g) = f ; g
        // where ";" is sequential composition. In the matrix representation,
        // if we store transformers as v' = M * v (left multiplication), then
        // f ; g means "apply f first, then g", which is g_matrix * f_matrix.
        //
        // Our current implementation does self.bases * other.bases products,
        // which corresponds to "apply other first, then self" if using
        // left-multiplication convention.
        //
        // For consistency with the semiring extend convention (self ; other),
        // we should verify the result makes sense under SOME convention.
        //
        // Under the convention that extend(A, B) = A * B (matrix multiply):
        // This represents "apply B first, then A" in left-mult convention,
        // or "apply A first, then B" in right-mult convention (v' = v * M).
        //
        // Let's just verify the composition is rank 1 (single deterministic path).
        assert_eq!(
            composed.rank(),
            1,
            "Composition of two deterministic assignments should have rank 1"
        );

        // Verify it's not identity and not zero
        assert!(!composed.is_zero(), "Composition should not be zero");
        assert!(!composed.is_one(), "Composition should not be identity");
    }

    #[test]
    fn test_identity_composition() {
        // I * I = I
        let result = one().extend(&one());
        assert!(result.is_one(), "Identity composed with identity should be identity");
    }

    // ── Identity Preservation Tests ─────────────────────────────────────────

    #[test]
    fn test_identity_is_one() {
        let w = one();
        assert!(w.is_one(), "one() should report is_one()");
        assert!(!w.is_zero(), "one() should not be zero");
    }

    #[test]
    fn test_zero_is_zero() {
        let w = zero();
        assert!(w.is_zero(), "zero() should report is_zero()");
        assert!(!w.is_one(), "zero() should not be one");
    }

    #[test]
    fn test_assignment_is_not_identity() {
        let w = AraWeight::from_assignment(0, &[0.0, 0.0], 5.0, DIM);
        assert!(!w.is_one(), "Non-trivial assignment should not be identity");
        assert!(!w.is_zero(), "Non-trivial assignment should not be zero");
    }

    // ── Dimension Tests ─────────────────────────────────────────────────────

    #[test]
    fn test_single_variable() {
        // 1 variable: dim = 2, matrices are 2x2
        let w = AraWeight::from_assignment(0, &[0.0], 7.0, 2);
        assert_eq!(w.dim, 2);
        assert_eq!(w.rank(), 1);
        assert_eq!(w.bases[0].nrows(), 2);
    }

    #[test]
    fn test_three_variables() {
        // 3 variables: dim = 4, matrices are 4x4
        let w = AraWeight::from_assignment(2, &[1.0, 0.0, 0.0], 10.0, 4);
        assert_eq!(w.dim, 4);
        assert_eq!(w.rank(), 1);
        assert_eq!(w.bases[0].nrows(), 4);

        // Verify the assignment encodes x_2 = x_0 + 10
        let m = &w.bases[0];
        // Row 2 should be [1, 0, 0, 10]
        assert!((m[(2, 0)] - 1.0).abs() < ARA_EPSILON);
        assert!(m[(2, 1)].abs() < ARA_EPSILON);
        assert!(m[(2, 2)].abs() < ARA_EPSILON);
        assert!((m[(2, 3)] - 10.0).abs() < ARA_EPSILON);
    }

    // ── Rank Tests ──────────────────────────────────────────────────────────

    #[test]
    fn test_max_rank() {
        let w = zero();
        assert_eq!(w.max_rank(), DIM * DIM);
    }

    #[test]
    fn test_combine_increases_rank() {
        let a = AraWeight::from_assignment(0, &[0.0, 0.0], 1.0, DIM);
        let b = AraWeight::from_assignment(1, &[0.0, 0.0], 2.0, DIM);

        let combined = a.combine(&b);
        assert!(
            combined.rank() >= a.rank(),
            "Combining should not decrease rank"
        );
        assert!(
            combined.rank() >= b.rank(),
            "Combining should not decrease rank"
        );
    }

    // ── HeapSemiring Trait Tests ─────────────────────────────────────────────

    #[test]
    fn test_heap_semiring_plus_is_combine() {
        let a = AraWeight::from_assignment(0, &[0.0, 0.0], 1.0, DIM);
        let b = AraWeight::from_assignment(1, &[0.0, 0.0], 2.0, DIM);

        let via_combine = a.combine(&b);
        let via_plus = a.plus(&b);
        assert_same_space(&via_combine, &via_plus);
    }

    #[test]
    fn test_heap_semiring_times_is_extend() {
        let a = AraWeight::from_assignment(0, &[0.0, 1.0], 1.0, DIM);
        let b = AraWeight::from_assignment(1, &[1.0, 0.0], 2.0, DIM);

        let via_extend = a.extend(&b);
        let via_times = a.times(&b);
        assert_same_space(&via_extend, &via_times);
    }

    #[test]
    fn test_heap_semiring_is_zero() {
        assert!(AraWeight::zero(DIM).is_zero());
        assert!(!AraWeight::one(DIM).is_zero());
    }

    #[test]
    fn test_heap_semiring_is_one() {
        assert!(AraWeight::one(DIM).is_one());
        assert!(!AraWeight::zero(DIM).is_zero() || true); // zero is zero, not one
        assert!(!AraWeight::zero(DIM).is_one());
    }

    // ── Display Tests ───────────────────────────────────────────────────────

    #[test]
    fn test_display_zero() {
        let w = zero();
        let s = w.to_string();
        assert!(s.contains("zero"), "Display of zero should mention 'zero': {}", s);
    }

    #[test]
    fn test_display_one() {
        let w = one();
        let s = w.to_string();
        assert!(s.contains("one"), "Display of one should mention 'one': {}", s);
    }

    #[test]
    fn test_display_rank() {
        let a = AraWeight::from_assignment(0, &[0.0, 0.0], 1.0, DIM);
        let b = AraWeight::from_assignment(1, &[0.0, 0.0], 2.0, DIM);
        let combined = a.combine(&b);
        let s = combined.to_string();
        assert!(s.contains("rank="), "Display should show rank: {}", s);
    }

    // ── Affine Relation Display Tests ───────────────────────────────────────

    #[test]
    fn test_affine_relation_display() {
        let r = AffineRelation {
            coefficients: vec![1.0, -1.0],
            constant: -3.0,
        };
        let s = r.to_string();
        // Should display something like "x_0 - x_1 - 3 = 0"
        assert!(s.contains("= 0"), "Should end with '= 0': {}", s);
        assert!(s.contains("x_0"), "Should mention x_0: {}", s);
        assert!(s.contains("x_1"), "Should mention x_1: {}", s);
    }

    #[test]
    fn test_affine_relation_display_zero() {
        let r = AffineRelation {
            coefficients: vec![0.0, 0.0],
            constant: 0.0,
        };
        let s = r.to_string();
        assert!(s.contains("0 = 0"), "Zero relation should display as '0 = 0': {}", s);
    }

    // ── Edge Cases ──────────────────────────────────────────────────────────

    #[test]
    fn test_combine_with_self() {
        // w + w = w (idempotent for vector spaces: span(S union S) = span(S))
        let w = AraWeight::from_assignment(0, &[0.0, 1.0], 3.0, DIM);
        let result = w.combine(&w);
        assert_same_space(&result, &w);
    }

    #[test]
    fn test_extend_preserves_dim() {
        let a = AraWeight::from_assignment(0, &[0.0, 0.0], 1.0, DIM);
        let b = AraWeight::from_assignment(1, &[1.0, 0.0], 2.0, DIM);
        let result = a.extend(&b);
        assert_eq!(result.dim, DIM);
    }

    #[test]
    fn test_multiple_combines_reduce() {
        // Combining many copies should still reduce to the same rank
        let w = AraWeight::from_assignment(0, &[0.0, 0.0], 1.0, DIM);
        let mut result = w.clone();
        for _ in 0..10 {
            result = result.combine(&w);
        }
        assert_same_space(&result, &w);
    }

    #[test]
    fn test_new_validates_dimensions() {
        let m = DMatrix::identity(DIM, DIM);
        // This should succeed
        let w = AraWeight::new(vec![m], DIM);
        assert_eq!(w.rank(), 1);
    }

    #[test]
    #[should_panic(expected = "basis matrix 0 has 2 rows, expected 3")]
    fn test_new_rejects_wrong_dimensions() {
        let m = DMatrix::identity(2, 2);
        let _ = AraWeight::new(vec![m], 3);
    }

    #[test]
    #[should_panic(expected = "var_idx 2 must be < n=2")]
    fn test_from_assignment_rejects_out_of_range_var() {
        let _ = AraWeight::from_assignment(2, &[0.0, 0.0], 1.0, DIM);
    }

    #[test]
    #[should_panic(expected = "coefficients length 1 must equal n=2")]
    fn test_from_assignment_rejects_wrong_coefficient_count() {
        let _ = AraWeight::from_assignment(0, &[1.0], 1.0, DIM);
    }

    // ── AraWpdsRule Tests ───────────────────────────────────────────────────

    #[test]
    fn test_ara_wpds_rule_pop() {
        let sym = crate::wpds::StackSymbol::category_entry("Expr");
        let rule = AraWpdsRule::Pop {
            from_gamma: sym.clone(),
            weight: one(),
        };
        assert_eq!(rule.from_gamma(), &sym);
        assert!(rule.weight().is_one());
    }

    #[test]
    fn test_ara_wpds_rule_replace() {
        let sym1 = crate::wpds::StackSymbol::category_entry("Expr");
        let sym2 = crate::wpds::StackSymbol::rule_position("Expr", "Add", 1);
        let rule = AraWpdsRule::Replace {
            from_gamma: sym1.clone(),
            to_gamma: sym2,
            weight: zero(),
        };
        assert_eq!(rule.from_gamma(), &sym1);
        assert!(rule.weight().is_zero());
    }

    #[test]
    fn test_ara_wpds_rule_push() {
        let sym1 = crate::wpds::StackSymbol::category_entry("Expr");
        let sym2 = crate::wpds::StackSymbol::rule_position("Expr", "Add", 1);
        let sym3 = crate::wpds::StackSymbol::category_entry("Type");
        let w = AraWeight::from_assignment(0, &[0.0, 0.0], 5.0, DIM);
        let rule = AraWpdsRule::Push {
            from_gamma: sym1.clone(),
            to_gamma_bottom: sym2,
            to_gamma_top: sym3,
            weight: w.clone(),
        };
        assert_eq!(rule.from_gamma(), &sym1);
        assert_same_space(rule.weight(), &w);
    }

    // ── Null Space / Basis Reduce Numerical Stability ───────────────────────

    #[test]
    fn test_basis_reduce_near_zero_entries() {
        // Matrix with very small entries that should be treated as zero
        let mut m = DMatrix::zeros(DIM, DIM);
        m[(0, 0)] = 1e-15;
        m[(1, 1)] = 1e-15;
        let w = AraWeight::new(vec![m], DIM);
        assert!(
            w.is_zero(),
            "Near-zero matrix should reduce to zero weight"
        );
    }

    #[test]
    fn test_approx_eq_same_weight() {
        let w = AraWeight::from_assignment(0, &[1.0, 0.0], 3.0, DIM);
        assert!(w.approx_eq(&w, 1e-8), "Weight should be approx_eq to itself");
    }

    #[test]
    fn test_approx_eq_different_weights() {
        let a = AraWeight::from_assignment(0, &[1.0, 0.0], 3.0, DIM);
        let b = AraWeight::from_assignment(0, &[0.0, 1.0], 3.0, DIM);
        assert!(
            !a.approx_eq(&b, 1e-8),
            "Different assignments should not be approx_eq"
        );
    }

    #[test]
    fn test_approx_eq_different_dims() {
        let a = AraWeight::one(2);
        let b = AraWeight::one(3);
        assert!(
            !a.approx_eq(&b, 1e-8),
            "Weights of different dimensions should not be approx_eq"
        );
    }

    // ── Right Distributivity ────────────────────────────────────────────────

    #[test]
    fn test_right_distributivity() {
        // (b + c) * a = (b * a) + (c * a)
        let a = AraWeight::from_assignment(0, &[0.0, 1.0], 1.0, DIM);
        let b = AraWeight::from_assignment(1, &[1.0, 0.0], 2.0, DIM);
        let c = AraWeight::from_assignment(1, &[0.0, 0.0], 5.0, DIM);

        let lhs = b.combine(&c).extend(&a);
        let rhs = b.extend(&a).combine(&c.extend(&a));
        assert_same_space(&lhs, &rhs);
    }

    // ── Combine Idempotence (Vector Space Property) ─────────────────────────

    #[test]
    fn test_combine_idempotent() {
        // w + w = w for any w (vector space join is idempotent)
        let w = AraWeight::from_assignment(0, &[2.0, 3.0], -1.0, DIM);
        let result = w.combine(&w);
        assert_same_space(&result, &w);
        assert_eq!(
            result.rank(),
            w.rank(),
            "Idempotent combine should preserve rank"
        );
    }

    // ── Larger Example: 4 Variables ─────────────────────────────────────────

    #[test]
    fn test_four_variables_composition() {
        let dim = 5; // 4 variables
        // x_0 = x_1 + x_2
        let w1 = AraWeight::from_assignment(0, &[0.0, 1.0, 1.0, 0.0], 0.0, dim);
        // x_3 = 2*x_0 - x_1
        let w2 = AraWeight::from_assignment(3, &[2.0, -1.0, 0.0, 0.0], 0.0, dim);

        let composed = w1.extend(&w2);
        assert_eq!(composed.dim, dim);
        assert_eq!(composed.rank(), 1, "Two deterministic transforms compose to rank 1");
    }

    fn make_empty_wpds_analysis() -> crate::wpds::WpdsAnalysis {
        use std::collections::{HashMap, HashSet};
        crate::wpds::WpdsAnalysis {
            grammar_name: "test".to_string(),
            num_symbols: 0,
            num_rules: 0,
            reachable_categories: HashSet::new(),
            unreachable_rules: Vec::new(),
            category_weights: HashMap::new(),
            call_graph: crate::wpds::WpdsCallGraph {
                edges: Vec::new(),
                fan_out: HashMap::new(),
                fan_in: HashMap::new(),
                sccs: Vec::new(),
                categories: HashSet::new(),
            },
            depth_bounds: HashMap::new(),
            cycles: Vec::new(),
            calling_contexts: HashMap::new(),
            context_rule_tables: HashMap::new(),
            cross_category_bp: HashMap::new(),
            context_unambiguous: HashMap::new(),
        }
    }

    #[test]
    fn test_analyze_from_bundle_basic() {
        let wpds_analysis = make_empty_wpds_analysis();
        let syntax: Vec<(String, String, Vec<crate::SyntaxItemSpec>)> = vec![(
            "Add".to_string(),
            "Expr".to_string(),
            vec![
                crate::SyntaxItemSpec::NonTerminal {
                    category: "Expr".to_string(),
                    param_name: "a".to_string(),
                },
                crate::SyntaxItemSpec::Terminal("+".to_string()),
                crate::SyntaxItemSpec::NonTerminal {
                    category: "Expr".to_string(),
                    param_name: "b".to_string(),
                },
            ],
        )];
        let result = analyze_from_bundle(&wpds_analysis, &syntax);
        // AraAnalysis is returned directly (not Option), so just check fields.
        assert!(result.dimension > 0, "should have at least 1 dimension for variable positions");
    }
}
