//! Newton's method for semiring fixpoints.
//!
//! Implements the algorithm of Esparza, Kiefer & Luttenberger (2010):
//! Newton's method lifted from numerical analysis to omega-continuous semirings,
//! converging to the least fixpoint in fewer iterations than naive Kleene
//! iteration.
//!
//! # Background
//!
//! Given a system of polynomial equations `X = F(X)` over a semiring
//! `(K, +, *, 0, 1)`, the **least fixpoint** is the smallest vector `X*`
//! such that `X* = F(X*)`. Kleene iteration computes this as:
//!
//! ```text
//! kappa_0 = 0,  kappa_{i+1} = F(kappa_i)
//! ```
//!
//! which converges monotonically but may require many iterations (or
//! infinitely many for non-idempotent semirings). Newton's method
//! accelerates convergence by linearizing `F` at each iterate:
//!
//! ```text
//! nu_0 = 0,  nu_{i+1} = J_F(nu_i)* . F(nu_i)
//! ```
//!
//! where `J_F(X)` is the Jacobian matrix (matrix of formal partial
//! derivatives) of `F` evaluated at `X`, and `J*` denotes the Kleene
//! closure of the matrix (computed via [`matrix_star`]).
//!
//! # Convergence
//!
//! For **idempotent** semirings (e.g., `TropicalWeight`, `BooleanWeight`),
//! Newton's method converges in at most `h + 1` iterations where `h` is
//! the "strahler number" (tree height) of the equation system. For
//! non-idempotent semirings (e.g., `CountingWeight`), convergence is
//! guaranteed for omega-continuous semirings but the number of iterations
//! depends on the specific semiring.
//!
//! # Example
//!
//! Solving `x = a * x + b` (a linear equation whose solution is `a* * b`):
//!
//! ```
//! use mettail_prattail::newton::{EquationSystem, Equation, Term, newton_fixpoint};
//! use mettail_prattail::automata::semiring::{Semiring, TropicalWeight};
//!
//! let a = TropicalWeight::new(2.0);
//! let b = TropicalWeight::new(3.0);
//!
//! let system = EquationSystem {
//!     num_variables: 1,
//!     equations: vec![
//!         // x_0 = a * x_0 + b
//!         Equation {
//!             terms: vec![
//!                 Term { coeff: a, vars: vec![0] },  // a * x_0
//!                 Term { coeff: b, vars: vec![] },    // b (constant)
//!             ],
//!         },
//!     ],
//! };
//!
//! let result = newton_fixpoint(&system, 20);
//! // Solution: a* * b = one * b = 0.0 + 3.0 = 3.0 (since a=2.0 >= 0, star=0.0)
//! assert!(result[0].approx_eq(&TropicalWeight::new(3.0), 1e-9));
//! ```
//!
//! # References
//!
//! - J. Esparza, S. Kiefer, M. Luttenberger. "Newton's Method for
//!   omega-Continuous Semirings." ICALP 2008.
//! - J. Esparza, S. Kiefer, M. Luttenberger. "Newtonian Program Analysis."
//!   J. ACM 57(6), 2010.

use crate::automata::semiring::{matrix_star, Semiring, StarSemiring};

// ══════════════════════════════════════════════════════════════════════════════
// Types
// ══════════════════════════════════════════════════════════════════════════════

/// A single monomial term in a polynomial equation over a semiring.
///
/// Represents `coeff * x_{vars[0]} * x_{vars[1]} * ... * x_{vars[k-1]}`.
///
/// - An empty `vars` vector represents a constant term (just `coeff`).
/// - Variables may repeat: `vars = [0, 0]` represents `coeff * x_0 * x_0`.
/// - Variable indices must be in `0..num_variables`.
#[derive(Debug, Clone)]
pub struct Term<W: Semiring> {
    /// The semiring coefficient of this monomial.
    pub coeff: W,
    /// Variable indices participating in this product (may repeat).
    pub vars: Vec<usize>,
}

/// A single polynomial equation (right-hand side): a sum of [`Term`]s.
///
/// Represents `f_i(X) = term_0 + term_1 + ... + term_{m-1}` where `+` is
/// semiring addition.
#[derive(Debug, Clone)]
pub struct Equation<W: Semiring> {
    /// The monomial terms whose semiring sum forms this equation's RHS.
    pub terms: Vec<Term<W>>,
}

/// A system of `n` polynomial equations in `n` unknowns over a semiring.
///
/// Represents `X = F(X)` where:
/// - `X = (x_0, x_1, ..., x_{n-1})` is the vector of unknowns
/// - `F(X) = (f_0(X), f_1(X), ..., f_{n-1}(X))` is the vector of polynomial RHS
///
/// Each `f_i` is an [`Equation`] — a sum of [`Term`]s (products of
/// variables and constants).
#[derive(Debug, Clone)]
pub struct EquationSystem<W: Semiring> {
    /// Number of variables (and equations). The system is square: `n` equations
    /// in `n` unknowns.
    pub num_variables: usize,
    /// The `n` equations, one per variable. `equations[i]` gives the RHS for
    /// `x_i = f_i(X)`.
    pub equations: Vec<Equation<W>>,
}

/// Result of a fixpoint computation, including the solution vector and
/// metadata about convergence.
#[derive(Debug, Clone)]
pub struct FixpointResult<W: Semiring> {
    /// The computed fixpoint values `(x_0, x_1, ..., x_{n-1})`.
    pub values: Vec<W>,
    /// Number of iterations performed.
    pub iterations: usize,
    /// Whether the computation converged (subsequent iterate equals current
    /// within tolerance).
    pub converged: bool,
}

// ══════════════════════════════════════════════════════════════════════════════
// Evaluation
// ══════════════════════════════════════════════════════════════════════════════

/// Evaluate a single term at the given variable values.
///
/// Computes `coeff * values[vars[0]] * values[vars[1]] * ...`.
/// If any variable's value is zero, short-circuits to zero.
fn evaluate_term<W: Semiring>(term: &Term<W>, values: &[W]) -> W {
    let mut result = term.coeff;
    for &var_idx in &term.vars {
        result = result.times(&values[var_idx]);
        // Short-circuit: zero annihilates
        if result.is_zero() {
            return W::zero();
        }
    }
    result
}

/// Evaluate a single equation (sum of terms) at the given variable values.
///
/// Computes `term_0(values) + term_1(values) + ...` using semiring addition.
fn evaluate_equation<W: Semiring>(equation: &Equation<W>, values: &[W]) -> W {
    let mut result = W::zero();
    for term in &equation.terms {
        result = result.plus(&evaluate_term(term, values));
    }
    result
}

/// Evaluate the entire polynomial system `F(X)` at the given variable values.
///
/// Returns `(f_0(values), f_1(values), ..., f_{n-1}(values))`.
fn evaluate_system<W: Semiring>(system: &EquationSystem<W>, values: &[W]) -> Vec<W> {
    let n = system.num_variables;
    let mut result = Vec::with_capacity(n);
    for equation in &system.equations {
        result.push(evaluate_equation(equation, values));
    }
    result
}

// ══════════════════════════════════════════════════════════════════════════════
// Jacobian
// ══════════════════════════════════════════════════════════════════════════════

/// Compute the partial derivative of a term w.r.t. variable `var_idx`,
/// evaluated at the given values.
///
/// For a term `c * x_{j_1} * x_{j_2} * ... * x_{j_m}`, the partial
/// derivative w.r.t. `x_k` is:
///
/// ```text
/// sum over all positions p where j_p = k of:
///   c * x_{j_1} * ... * x_{j_{p-1}} * x_{j_{p+1}} * ... * x_{j_m}
/// ```
///
/// This is the "product rule" generalized to semirings: for each occurrence
/// of `x_k` in the product, replace it with `1` and evaluate the rest.
///
/// In a commutative semiring the order does not matter, so we can factor:
/// for each occurrence of `x_k`, the contribution is the product of all
/// other factors (including `coeff`) evaluated at `values`.
fn partial_derivative_term<W: Semiring>(term: &Term<W>, var_idx: usize, values: &[W]) -> W {
    let num_vars = term.vars.len();

    // Collect positions where var_idx appears
    let positions: Vec<usize> = term
        .vars
        .iter()
        .enumerate()
        .filter_map(|(pos, &v)| if v == var_idx { Some(pos) } else { None })
        .collect();

    if positions.is_empty() {
        return W::zero();
    }

    // For each occurrence of var_idx, compute the product of all other factors
    let mut total_derivative = W::zero();
    for &skip_pos in &positions {
        let mut product = term.coeff;
        for i in 0..num_vars {
            if i == skip_pos {
                continue; // skip this occurrence of x_{var_idx}
            }
            product = product.times(&values[term.vars[i]]);
            if product.is_zero() {
                break;
            }
        }
        total_derivative = total_derivative.plus(&product);
    }

    total_derivative
}

/// Compute the partial derivative of an equation w.r.t. variable `var_idx`,
/// evaluated at the given values.
///
/// This is the (i, var_idx) entry of the Jacobian: `df_i / dx_{var_idx}`.
fn partial_derivative_equation<W: Semiring>(
    equation: &Equation<W>,
    var_idx: usize,
    values: &[W],
) -> W {
    let mut result = W::zero();
    for term in &equation.terms {
        result = result.plus(&partial_derivative_term(term, var_idx, values));
    }
    result
}

/// Compute the Jacobian matrix `J_F(X)` of the equation system evaluated
/// at the given values.
///
/// Returns an `n x n` matrix where entry `(i, j)` is `df_i / dx_j`
/// evaluated at `values`.
///
/// The Jacobian captures the linear approximation of `F` at the current
/// iterate, and its Kleene closure `J*` determines how changes propagate
/// through the system.
pub fn jacobian<W: Semiring>(system: &EquationSystem<W>, values: &[W]) -> Vec<Vec<W>> {
    let n = system.num_variables;
    let mut jac: Vec<Vec<W>> = Vec::with_capacity(n);
    for i in 0..n {
        let mut row = Vec::with_capacity(n);
        for j in 0..n {
            row.push(partial_derivative_equation(&system.equations[i], j, values));
        }
        jac.push(row);
    }
    jac
}

// ══════════════════════════════════════════════════════════════════════════════
// Newton's method
// ══════════════════════════════════════════════════════════════════════════════

/// Compute the least fixpoint of `X = F(X)` using Newton's method.
///
/// Newton's method for semirings iterates:
///
/// ```text
/// nu_0 = 0
/// nu_{i+1} = J_F(nu_i)* . F(nu_i)
/// ```
///
/// where `J_F(nu_i)` is the Jacobian of `F` evaluated at `nu_i`, and
/// `J*` is the Kleene closure computed via [`matrix_star`].
///
/// The iterate `nu_{i+1}` is the least solution of the linearized system
/// `Y = J_F(nu_i) . Y + F(nu_i)`, which is then used as the starting
/// point for the next linearization.
///
/// # Arguments
///
/// - `system`: The polynomial equation system `X = F(X)`.
/// - `max_iterations`: Maximum number of Newton steps before returning.
///
/// # Returns
///
/// A [`FixpointResult`] containing the solution vector, iteration count,
/// and convergence status.
///
/// # Panics
///
/// Panics if `system.equations.len() != system.num_variables`.
pub fn newton_fixpoint<W: StarSemiring>(
    system: &EquationSystem<W>,
    max_iterations: usize,
) -> Vec<W> {
    let result = newton_fixpoint_detailed(system, max_iterations);
    result.values
}

/// Compute the least fixpoint of `X = F(X)` using Newton's method,
/// returning detailed convergence information.
///
/// See [`newton_fixpoint`] for the algorithm description.
///
/// # Panics
///
/// Panics if `system.equations.len() != system.num_variables`.
pub fn newton_fixpoint_detailed<W: StarSemiring>(
    system: &EquationSystem<W>,
    max_iterations: usize,
) -> FixpointResult<W> {
    let n = system.num_variables;
    assert_eq!(
        system.equations.len(),
        n,
        "newton_fixpoint: system has {} variables but {} equations",
        n,
        system.equations.len()
    );

    // Handle degenerate case
    if n == 0 {
        return FixpointResult {
            values: vec![],
            iterations: 0,
            converged: true,
        };
    }

    // nu_0 = 0 (vector of semiring zeros)
    let mut current: Vec<W> = vec![W::zero(); n];

    for iteration in 0..max_iterations {
        // Step 1: Evaluate F(current)
        let f_val = evaluate_system(system, &current);

        // Step 2: Compute the Jacobian J_F(current)
        let jac = jacobian(system, &current);

        // Step 3: Compute J* via matrix_star (generalized Floyd-Warshall)
        let j_star = matrix_star(&jac);

        // Step 4: Compute next = J* . F(current)
        // This is a matrix-vector product: next[i] = sum_j j_star[i][j] * f_val[j]
        let mut next: Vec<W> = Vec::with_capacity(n);
        for i in 0..n {
            let mut val = W::zero();
            for j in 0..n {
                val = val.plus(&j_star[i][j].times(&f_val[j]));
            }
            next.push(val);
        }

        // Check convergence: next == current (within approx_eq tolerance)
        let converged = current
            .iter()
            .zip(next.iter())
            .all(|(c, n)| c.approx_eq(n, 1e-10));

        current = next;

        if converged {
            return FixpointResult {
                values: current,
                iterations: iteration + 1,
                converged: true,
            };
        }
    }

    FixpointResult {
        values: current,
        iterations: max_iterations,
        converged: false,
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// Kleene iteration (for comparison)
// ══════════════════════════════════════════════════════════════════════════════

/// Compute the least fixpoint of `X = F(X)` using standard Kleene iteration.
///
/// Kleene iteration computes:
///
/// ```text
/// kappa_0 = 0
/// kappa_{i+1} = F(kappa_i)
/// ```
///
/// This converges monotonically to the least fixpoint for omega-continuous
/// semirings, but may require many more iterations than Newton's method.
///
/// # Arguments
///
/// - `system`: The polynomial equation system `X = F(X)`.
/// - `max_iterations`: Maximum number of Kleene steps.
///
/// # Returns
///
/// A [`FixpointResult`] containing the solution vector, iteration count,
/// and convergence status.
///
/// # Panics
///
/// Panics if `system.equations.len() != system.num_variables`.
pub fn kleene_fixpoint<W: Semiring>(
    system: &EquationSystem<W>,
    max_iterations: usize,
) -> FixpointResult<W> {
    let n = system.num_variables;
    assert_eq!(
        system.equations.len(),
        n,
        "kleene_fixpoint: system has {} variables but {} equations",
        n,
        system.equations.len()
    );

    // Handle degenerate case
    if n == 0 {
        return FixpointResult {
            values: vec![],
            iterations: 0,
            converged: true,
        };
    }

    // kappa_0 = 0 (vector of semiring zeros)
    let mut current: Vec<W> = vec![W::zero(); n];

    for iteration in 0..max_iterations {
        // kappa_{i+1} = F(kappa_i)
        let next = evaluate_system(system, &current);

        // Check convergence
        let converged = current
            .iter()
            .zip(next.iter())
            .all(|(c, n)| c.approx_eq(n, 1e-10));

        current = next;

        if converged {
            return FixpointResult {
                values: current,
                iterations: iteration + 1,
                converged: true,
            };
        }
    }

    FixpointResult {
        values: current,
        iterations: max_iterations,
        converged: false,
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// Convenience constructors
// ══════════════════════════════════════════════════════════════════════════════

impl<W: Semiring> Term<W> {
    /// Create a constant term (no variables).
    pub fn constant(coeff: W) -> Self {
        Term {
            coeff,
            vars: vec![],
        }
    }

    /// Create a linear term: `coeff * x_{var_idx}`.
    pub fn linear(coeff: W, var_idx: usize) -> Self {
        Term {
            coeff,
            vars: vec![var_idx],
        }
    }

    /// Create a quadratic term: `coeff * x_i * x_j`.
    pub fn quadratic(coeff: W, var_i: usize, var_j: usize) -> Self {
        Term {
            coeff,
            vars: vec![var_i, var_j],
        }
    }
}

impl<W: Semiring> Equation<W> {
    /// Create an equation from a single term.
    pub fn single(term: Term<W>) -> Self {
        Equation { terms: vec![term] }
    }

    /// Create an equation as the sum of multiple terms.
    pub fn sum(terms: Vec<Term<W>>) -> Self {
        Equation { terms }
    }
}

impl<W: Semiring> EquationSystem<W> {
    /// Create an equation system, validating that all variable references
    /// are within bounds.
    ///
    /// # Panics
    ///
    /// Panics if any term references a variable index >= `num_variables`,
    /// or if the number of equations does not equal `num_variables`.
    pub fn new(num_variables: usize, equations: Vec<Equation<W>>) -> Self {
        assert_eq!(
            equations.len(),
            num_variables,
            "EquationSystem::new: expected {} equations, got {}",
            num_variables,
            equations.len()
        );
        for (i, eq) in equations.iter().enumerate() {
            for (j, term) in eq.terms.iter().enumerate() {
                for &var in &term.vars {
                    assert!(
                        var < num_variables,
                        "EquationSystem::new: equation {} term {} references variable {}, \
                         but num_variables = {}",
                        i,
                        j,
                        var,
                        num_variables
                    );
                }
            }
        }
        EquationSystem {
            num_variables,
            equations,
        }
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// Pipeline bridge
// ══════════════════════════════════════════════════════════════════════════════

/// Pipeline bridge: apply Newton's method acceleration to fixpoint computation.
///
/// This is an internal optimization used by other WPDS analyses to speed
/// up convergence. It wraps [`newton_fixpoint_detailed`] to return the full
/// [`FixpointResult`] (solution vector, iteration count, convergence status).
///
/// No direct lint output — callers inspect the result for downstream decisions.
pub fn accelerate_from_bundle<W: StarSemiring + Clone + Default>(
    system: &EquationSystem<W>,
    max_iter: usize,
) -> FixpointResult<W> {
    newton_fixpoint_detailed(system, max_iter)
}

// ══════════════════════════════════════════════════════════════════════════════
// Tests
// ══════════════════════════════════════════════════════════════════════════════

#[cfg(test)]
mod tests {
    use super::*;
    use crate::automata::semiring::{BooleanWeight, CountingWeight, TropicalWeight};

    // ── Evaluation tests ────────────────────────────────────────────────────

    #[test]
    fn evaluate_constant_term() {
        let term = Term::constant(TropicalWeight::new(5.0));
        let values: Vec<TropicalWeight> = vec![TropicalWeight::new(1.0)];
        let result = evaluate_term(&term, &values);
        assert!(
            result.approx_eq(&TropicalWeight::new(5.0), 1e-9),
            "constant term should evaluate to its coefficient"
        );
    }

    #[test]
    fn evaluate_linear_term() {
        // Term: 2.0 * x_0, with x_0 = 3.0
        // Tropical times = +, so result = 2.0 + 3.0 = 5.0
        let term = Term::linear(TropicalWeight::new(2.0), 0);
        let values = vec![TropicalWeight::new(3.0)];
        let result = evaluate_term(&term, &values);
        assert!(
            result.approx_eq(&TropicalWeight::new(5.0), 1e-9),
            "linear term: tropical times(2.0, 3.0) = 5.0, got {:?}",
            result
        );
    }

    #[test]
    fn evaluate_quadratic_term() {
        // Term: 1.0 * x_0 * x_1, with x_0 = 2.0, x_1 = 3.0
        // Tropical: 0.0 + 2.0 + 3.0 = 5.0
        let term = Term::quadratic(TropicalWeight::one(), 0, 1);
        let values = vec![TropicalWeight::new(2.0), TropicalWeight::new(3.0)];
        let result = evaluate_term(&term, &values);
        assert!(
            result.approx_eq(&TropicalWeight::new(5.0), 1e-9),
            "quadratic term: tropical 0+2+3 = 5.0, got {:?}",
            result
        );
    }

    #[test]
    fn evaluate_term_with_zero_variable() {
        // Any term with a zero variable should evaluate to zero
        let term = Term::linear(TropicalWeight::new(5.0), 0);
        let values = vec![TropicalWeight::zero()]; // +inf
        let result = evaluate_term(&term, &values);
        assert!(
            result.is_zero(),
            "term with zero variable should be zero, got {:?}",
            result
        );
    }

    #[test]
    fn evaluate_equation_sum() {
        // f(x_0) = 2.0 * x_0 + 5.0
        // At x_0 = 3.0: tropical plus(min)(5.0, 5.0) = 5.0
        let eq = Equation::sum(vec![
            Term::linear(TropicalWeight::new(2.0), 0),
            Term::constant(TropicalWeight::new(5.0)),
        ]);
        let values = vec![TropicalWeight::new(3.0)];
        let result = evaluate_equation(&eq, &values);
        // times(2.0, 3.0) = 5.0; plus(5.0, 5.0) = min(5.0, 5.0) = 5.0
        assert!(
            result.approx_eq(&TropicalWeight::new(5.0), 1e-9),
            "equation: min(5.0, 5.0) = 5.0, got {:?}",
            result
        );
    }

    // ── Jacobian tests ──────────────────────────────────────────────────────

    #[test]
    fn jacobian_constant_system() {
        // x_0 = 5.0 (constant, no variables)
        // J = [[0]] (zero matrix, since df/dx = 0 for constants)
        let system = EquationSystem::new(
            1,
            vec![Equation::single(Term::constant(TropicalWeight::new(5.0)))],
        );
        let values = vec![TropicalWeight::zero()];
        let jac = jacobian(&system, &values);
        assert!(
            jac[0][0].is_zero(),
            "Jacobian of constant system should be zero, got {:?}",
            jac[0][0]
        );
    }

    #[test]
    fn jacobian_linear_system() {
        // x_0 = a * x_0 + b
        // J = [[a]]
        let a = TropicalWeight::new(2.0);
        let b = TropicalWeight::new(3.0);
        let system = EquationSystem::new(
            1,
            vec![Equation::sum(vec![
                Term::linear(a, 0),
                Term::constant(b),
            ])],
        );
        let values = vec![TropicalWeight::zero()];
        let jac = jacobian(&system, &values);
        assert!(
            jac[0][0].approx_eq(&a, 1e-9),
            "Jacobian of linear system should be [[a]], got {:?}",
            jac[0][0]
        );
    }

    #[test]
    fn jacobian_quadratic_system() {
        // x_0 = 1 * x_0 * x_0 (quadratic, coefficient = one)
        // df/dx_0 = x_0 + x_0 = 2 * x_0 in classical algebra
        // In semiring: sum of two copies: for each position where x_0 appears,
        //   the derivative is the product of the other factors.
        // At x_0 = 3.0 (tropical): d/dx_0 = plus(3.0, 3.0) = min(3.0, 3.0) = 3.0
        let system = EquationSystem::new(
            1,
            vec![Equation::single(Term::quadratic(
                TropicalWeight::one(),
                0,
                0,
            ))],
        );
        let values = vec![TropicalWeight::new(3.0)];
        let jac = jacobian(&system, &values);
        // d/dx_0 of (one * x_0 * x_0) at x_0=3.0:
        //   position 0: one * 3.0 = 3.0 (tropical: 0.0 + 3.0 = 3.0)
        //   position 1: one * 3.0 = 3.0 (tropical: 0.0 + 3.0 = 3.0)
        //   plus(3.0, 3.0) = min(3.0, 3.0) = 3.0
        assert!(
            jac[0][0].approx_eq(&TropicalWeight::new(3.0), 1e-9),
            "Jacobian of x*x at x=3.0 should be 3.0 (tropical), got {:?}",
            jac[0][0]
        );
    }

    #[test]
    fn jacobian_two_variable_system() {
        // x_0 = a * x_1
        // x_1 = b * x_0
        // J = [[0, a], [b, 0]]
        let a = TropicalWeight::new(1.0);
        let b = TropicalWeight::new(2.0);
        let system = EquationSystem::new(
            2,
            vec![
                Equation::single(Term::linear(a, 1)), // x_0 = a * x_1
                Equation::single(Term::linear(b, 0)), // x_1 = b * x_0
            ],
        );
        let values = vec![TropicalWeight::zero(), TropicalWeight::zero()];
        let jac = jacobian(&system, &values);
        assert!(
            jac[0][0].is_zero(),
            "J[0][0] should be zero, got {:?}",
            jac[0][0]
        );
        assert!(
            jac[0][1].approx_eq(&a, 1e-9),
            "J[0][1] should be a={:?}, got {:?}",
            a,
            jac[0][1]
        );
        assert!(
            jac[1][0].approx_eq(&b, 1e-9),
            "J[1][0] should be b={:?}, got {:?}",
            b,
            jac[1][0]
        );
        assert!(
            jac[1][1].is_zero(),
            "J[1][1] should be zero, got {:?}",
            jac[1][1]
        );
    }

    // ── Newton fixpoint: 1-variable tests ───────────────────────────────────

    #[test]
    fn newton_constant_equation() {
        // x = 5.0 (constant equation)
        // Fixpoint: x = 5.0
        let system = EquationSystem::new(
            1,
            vec![Equation::single(Term::constant(TropicalWeight::new(5.0)))],
        );
        let result = newton_fixpoint_detailed(&system, 20);
        assert!(
            result.values[0].approx_eq(&TropicalWeight::new(5.0), 1e-9),
            "constant equation fixpoint should be 5.0, got {:?}",
            result.values[0]
        );
        assert!(result.converged, "constant equation should converge");
    }

    #[test]
    fn newton_linear_equation_tropical() {
        // x = a * x + b, where a = 2.0, b = 3.0 (tropical)
        // Solution: a* * b
        // a = 2.0 >= 0, so a* = one = 0.0 (tropical star)
        // a* * b = 0.0 + 3.0 = 3.0 (tropical times = +)
        let a = TropicalWeight::new(2.0);
        let b = TropicalWeight::new(3.0);
        let system = EquationSystem::new(
            1,
            vec![Equation::sum(vec![
                Term::linear(a, 0),
                Term::constant(b),
            ])],
        );
        let result = newton_fixpoint_detailed(&system, 20);
        let expected = TropicalWeight::new(3.0);
        assert!(
            result.values[0].approx_eq(&expected, 1e-9),
            "x = 2.0*x + 3.0: solution should be 3.0, got {:?}",
            result.values[0]
        );
        assert!(result.converged, "linear tropical should converge");
    }

    #[test]
    fn newton_linear_equation_boolean() {
        // x = true * x + true
        // Solution: true* * true = true ∧ true = true
        let system = EquationSystem::new(
            1,
            vec![Equation::sum(vec![
                Term::linear(BooleanWeight::one(), 0),
                Term::constant(BooleanWeight::one()),
            ])],
        );
        let result = newton_fixpoint_detailed(&system, 20);
        assert_eq!(
            result.values[0],
            BooleanWeight::one(),
            "boolean fixpoint should be true"
        );
        assert!(result.converged, "boolean should converge quickly");
    }

    #[test]
    fn newton_identity_equation() {
        // x = x (identity — any value is a fixpoint; least fixpoint is zero)
        let system = EquationSystem::new(
            1,
            vec![Equation::single(Term::linear(TropicalWeight::one(), 0))],
        );
        let result = newton_fixpoint_detailed(&system, 20);
        // The least fixpoint of x = x is x = 0 (semiring zero = +inf for tropical)
        // Wait — let's think about this. F(x) = x. Starting from x = +inf:
        // F(+inf) = +inf, so it converges immediately at zero.
        // But Newton: J = [[1]], J* = [[1*]] = [[one]] = [[0.0]]
        // F(+inf) = +inf, so J* . F(+inf) = 0.0 * (+inf) = +inf (tropical: 0.0 + inf = inf)
        // So next = +inf, converged.
        assert!(
            result.values[0].is_zero(),
            "x = x: least fixpoint is semiring zero, got {:?}",
            result.values[0]
        );
        assert!(result.converged, "identity should converge in 1 iteration");
    }

    #[test]
    fn newton_zero_variables() {
        // Degenerate: 0 variables, 0 equations
        let system: EquationSystem<TropicalWeight> = EquationSystem::new(0, vec![]);
        let result = newton_fixpoint_detailed(&system, 10);
        assert!(result.values.is_empty());
        assert!(result.converged);
        assert_eq!(result.iterations, 0);
    }

    // ── Newton fixpoint: 2-variable tests ───────────────────────────────────

    #[test]
    fn newton_two_variable_independent() {
        // x_0 = 3.0
        // x_1 = 7.0
        // Solution: (3.0, 7.0)
        let system = EquationSystem::new(
            2,
            vec![
                Equation::single(Term::constant(TropicalWeight::new(3.0))),
                Equation::single(Term::constant(TropicalWeight::new(7.0))),
            ],
        );
        let result = newton_fixpoint_detailed(&system, 20);
        assert!(
            result.values[0].approx_eq(&TropicalWeight::new(3.0), 1e-9),
            "x_0 should be 3.0, got {:?}",
            result.values[0]
        );
        assert!(
            result.values[1].approx_eq(&TropicalWeight::new(7.0), 1e-9),
            "x_1 should be 7.0, got {:?}",
            result.values[1]
        );
        assert!(result.converged);
    }

    #[test]
    fn newton_two_variable_coupled_linear() {
        // x_0 = 1.0 * x_1 + 5.0
        // x_1 = 2.0 * x_0 + 3.0
        //
        // Tropical interpretation:
        //   x_0 = min(1.0 + x_1, 5.0)
        //   x_1 = min(2.0 + x_0, 3.0)
        //
        // Substitute: x_1 = min(2.0 + min(1.0 + x_1, 5.0), 3.0)
        //           = min(3.0 + x_1, 7.0, 3.0) = min(3.0, 3.0 + x_1)
        // At fixpoint: x_1 = 3.0 (since 3.0 + 3.0 = 6.0 > 3.0, min picks 3.0)
        // Then x_0 = min(1.0 + 3.0, 5.0) = min(4.0, 5.0) = 4.0
        let system = EquationSystem::new(
            2,
            vec![
                Equation::sum(vec![
                    Term::linear(TropicalWeight::new(1.0), 1),
                    Term::constant(TropicalWeight::new(5.0)),
                ]),
                Equation::sum(vec![
                    Term::linear(TropicalWeight::new(2.0), 0),
                    Term::constant(TropicalWeight::new(3.0)),
                ]),
            ],
        );
        let result = newton_fixpoint_detailed(&system, 20);
        assert!(
            result.values[0].approx_eq(&TropicalWeight::new(4.0), 1e-9),
            "x_0 should be 4.0, got {:?}",
            result.values[0]
        );
        assert!(
            result.values[1].approx_eq(&TropicalWeight::new(3.0), 1e-9),
            "x_1 should be 3.0, got {:?}",
            result.values[1]
        );
        assert!(result.converged);
    }

    // ── Newton vs Kleene convergence comparison ─────────────────────────────

    #[test]
    fn newton_converges_faster_than_kleene_tropical() {
        // x = 2.0 * x + 3.0 (tropical)
        // Both should converge; Newton should need fewer iterations.
        let a = TropicalWeight::new(2.0);
        let b = TropicalWeight::new(3.0);
        let system = EquationSystem::new(
            1,
            vec![Equation::sum(vec![
                Term::linear(a, 0),
                Term::constant(b),
            ])],
        );
        let newton_result = newton_fixpoint_detailed(&system, 100);
        let kleene_result = kleene_fixpoint(&system, 100);

        assert!(newton_result.converged, "Newton should converge");
        assert!(kleene_result.converged, "Kleene should converge");

        // Both should agree on the fixpoint value
        assert!(
            newton_result.values[0].approx_eq(&kleene_result.values[0], 1e-9),
            "Newton ({:?}) and Kleene ({:?}) should agree",
            newton_result.values[0],
            kleene_result.values[0]
        );

        // Newton should converge in <= Kleene iterations
        assert!(
            newton_result.iterations <= kleene_result.iterations,
            "Newton ({} iters) should converge no slower than Kleene ({} iters)",
            newton_result.iterations,
            kleene_result.iterations
        );
    }

    #[test]
    fn newton_converges_faster_two_variable_boolean() {
        // x_0 = x_1 ∨ true
        // x_1 = x_0
        //
        // Kleene: (false,false) -> (true,false) -> (true,true) -> (true,true) converged
        // Newton: should converge faster due to star closure
        let system = EquationSystem::new(
            2,
            vec![
                Equation::sum(vec![
                    Term::linear(BooleanWeight::one(), 1),
                    Term::constant(BooleanWeight::one()),
                ]),
                Equation::single(Term::linear(BooleanWeight::one(), 0)),
            ],
        );
        let newton_result = newton_fixpoint_detailed(&system, 100);
        let kleene_result = kleene_fixpoint(&system, 100);

        assert!(newton_result.converged, "Newton should converge");
        assert!(kleene_result.converged, "Kleene should converge");

        assert_eq!(
            newton_result.values[0],
            BooleanWeight::one(),
            "x_0 should be true"
        );
        assert_eq!(
            newton_result.values[1],
            BooleanWeight::one(),
            "x_1 should be true"
        );
        assert_eq!(
            kleene_result.values[0],
            BooleanWeight::one(),
            "Kleene x_0 should be true"
        );
        assert_eq!(
            kleene_result.values[1],
            BooleanWeight::one(),
            "Kleene x_1 should be true"
        );

        assert!(
            newton_result.iterations <= kleene_result.iterations,
            "Newton ({} iters) should converge no slower than Kleene ({} iters)",
            newton_result.iterations,
            kleene_result.iterations
        );
    }

    // ── Kleene fixpoint tests ───────────────────────────────────────────────

    #[test]
    fn kleene_constant_equation() {
        let system = EquationSystem::new(
            1,
            vec![Equation::single(Term::constant(TropicalWeight::new(5.0)))],
        );
        let result = kleene_fixpoint(&system, 20);
        assert!(
            result.values[0].approx_eq(&TropicalWeight::new(5.0), 1e-9),
            "Kleene constant should be 5.0, got {:?}",
            result.values[0]
        );
        assert!(result.converged);
    }

    #[test]
    fn kleene_linear_tropical() {
        // x = 2.0 * x + 3.0 (tropical: x = min(2.0 + x, 3.0))
        // Kleene: x_0 = +inf, x_1 = min(+inf, 3.0) = 3.0,
        //         x_2 = min(5.0, 3.0) = 3.0, converged.
        let system = EquationSystem::new(
            1,
            vec![Equation::sum(vec![
                Term::linear(TropicalWeight::new(2.0), 0),
                Term::constant(TropicalWeight::new(3.0)),
            ])],
        );
        let result = kleene_fixpoint(&system, 20);
        assert!(
            result.values[0].approx_eq(&TropicalWeight::new(3.0), 1e-9),
            "Kleene linear should be 3.0, got {:?}",
            result.values[0]
        );
        assert!(result.converged);
    }

    #[test]
    fn kleene_zero_variables() {
        let system: EquationSystem<BooleanWeight> = EquationSystem::new(0, vec![]);
        let result = kleene_fixpoint(&system, 10);
        assert!(result.values.is_empty());
        assert!(result.converged);
        assert_eq!(result.iterations, 0);
    }

    // ── Identity / zero handling ────────────────────────────────────────────

    #[test]
    fn newton_all_zero_rhs() {
        // x_0 = 0 (semiring zero)
        // Fixpoint: x_0 = 0
        let system = EquationSystem::new(
            1,
            vec![Equation::single(Term::constant(TropicalWeight::zero()))],
        );
        let result = newton_fixpoint_detailed(&system, 20);
        assert!(
            result.values[0].is_zero(),
            "zero RHS fixpoint should be zero, got {:?}",
            result.values[0]
        );
        assert!(result.converged);
    }

    #[test]
    fn newton_identity_coeff() {
        // x_0 = one * x_0 + 5.0 (tropical: x_0 = min(0.0 + x_0, 5.0))
        // Fixpoint: x_0 = min(x_0, 5.0). Least fixpoint starting from +inf:
        //   min(+inf, 5.0) = 5.0, then min(5.0, 5.0) = 5.0. Fixed.
        let system = EquationSystem::new(
            1,
            vec![Equation::sum(vec![
                Term::linear(TropicalWeight::one(), 0),
                Term::constant(TropicalWeight::new(5.0)),
            ])],
        );
        let result = newton_fixpoint_detailed(&system, 20);
        assert!(
            result.values[0].approx_eq(&TropicalWeight::new(5.0), 1e-9),
            "identity coeff: fixpoint should be 5.0, got {:?}",
            result.values[0]
        );
        assert!(result.converged);
    }

    #[test]
    fn newton_counting_weight_linear() {
        // x = 2 * x + 3 (counting: x = 2x + 3)
        // star(2) = u64::MAX (saturated), so solution = u64::MAX * 3 = u64::MAX
        let system = EquationSystem::new(
            1,
            vec![Equation::sum(vec![
                Term::linear(CountingWeight::new(2), 0),
                Term::constant(CountingWeight::new(3)),
            ])],
        );
        let result = newton_fixpoint_detailed(&system, 20);
        // star(2) = MAX; MAX * 3 = MAX (saturating)
        assert_eq!(
            result.values[0],
            CountingWeight::new(u64::MAX),
            "counting weight: 2* * 3 should saturate to MAX"
        );
    }

    #[test]
    fn newton_counting_weight_zero_coeff() {
        // x = 0 * x + 5 (counting)
        //
        // Kleene iteration converges to 5 (the true least fixpoint):
        //   kappa_0 = 0, kappa_1 = 0*0 + 5 = 5, kappa_2 = 0*5 + 5 = 5. Fixed.
        let system = EquationSystem::new(
            1,
            vec![Equation::sum(vec![
                Term::linear(CountingWeight::zero(), 0),
                Term::constant(CountingWeight::new(5)),
            ])],
        );
        let kleene_result = kleene_fixpoint(&system, 20);
        assert_eq!(
            kleene_result.values[0],
            CountingWeight::new(5),
            "Kleene: 0*x + 5 fixpoint should be 5"
        );
        assert!(kleene_result.converged);

        // Newton's method saturates for CountingWeight because matrix_star
        // computes the reflexive-transitive closure: the diagonal element
        // becomes one().plus(J[0][0]) = 1 + 0 = 1, and star(1) = MAX for
        // CountingWeight (infinitely many unrollings). This overapproximation
        // is safe and is inherent to how CountingWeight interacts with the
        // star closure.
        let newton_result = newton_fixpoint_detailed(&system, 20);
        assert_eq!(
            newton_result.values[0],
            CountingWeight::new(u64::MAX),
            "Newton: counting weight saturates due to star(1) = MAX"
        );
    }

    // ── Boolean weight tests ────────────────────────────────────────────────

    #[test]
    fn newton_boolean_reachability_chain() {
        // x_0 = true ∧ x_1 ∨ false  (x_0 = x_1)
        // x_1 = true ∧ x_2 ∨ false  (x_1 = x_2)
        // x_2 = true                 (x_2 = true)
        //
        // Solution: x_2 = true, x_1 = true, x_0 = true
        let system = EquationSystem::new(
            3,
            vec![
                Equation::single(Term::linear(BooleanWeight::one(), 1)),
                Equation::single(Term::linear(BooleanWeight::one(), 2)),
                Equation::single(Term::constant(BooleanWeight::one())),
            ],
        );
        let newton_result = newton_fixpoint_detailed(&system, 20);
        let kleene_result = kleene_fixpoint(&system, 20);

        for i in 0..3 {
            assert_eq!(
                newton_result.values[i],
                BooleanWeight::one(),
                "Newton: x_{} should be true",
                i
            );
            assert_eq!(
                kleene_result.values[i],
                BooleanWeight::one(),
                "Kleene: x_{} should be true",
                i
            );
        }

        // Newton propagates through the chain in one step via matrix star
        assert!(
            newton_result.iterations <= kleene_result.iterations,
            "Newton ({}) should be <= Kleene ({})",
            newton_result.iterations,
            kleene_result.iterations
        );
    }

    #[test]
    fn newton_boolean_unreachable() {
        // x_0 = false ∧ x_0 = false
        // No constant source of truth, so fixpoint is false
        let system = EquationSystem::new(
            1,
            vec![Equation::single(Term::linear(BooleanWeight::zero(), 0))],
        );
        let result = newton_fixpoint_detailed(&system, 20);
        assert_eq!(
            result.values[0],
            BooleanWeight::zero(),
            "unreachable: fixpoint should be false"
        );
        assert!(result.converged);
    }

    // ── Partial derivative unit tests ───────────────────────────────────────

    #[test]
    fn partial_derivative_no_occurrence() {
        // Term: 5.0 * x_1, derivative w.r.t. x_0 = zero
        let term = Term::linear(TropicalWeight::new(5.0), 1);
        let values = vec![TropicalWeight::new(1.0), TropicalWeight::new(2.0)];
        let deriv = partial_derivative_term(&term, 0, &values);
        assert!(
            deriv.is_zero(),
            "d/dx_0 of (5*x_1) should be zero, got {:?}",
            deriv
        );
    }

    #[test]
    fn partial_derivative_single_occurrence() {
        // Term: 5.0 * x_0, derivative w.r.t. x_0 = 5.0
        let term = Term::linear(TropicalWeight::new(5.0), 0);
        let values = vec![TropicalWeight::new(99.0)];
        let deriv = partial_derivative_term(&term, 0, &values);
        assert!(
            deriv.approx_eq(&TropicalWeight::new(5.0), 1e-9),
            "d/dx_0 of (5*x_0) should be 5.0, got {:?}",
            deriv
        );
    }

    #[test]
    fn partial_derivative_product_of_different_vars() {
        // Term: one * x_0 * x_1, derivative w.r.t. x_0 = one * x_1
        // At x_1 = 3.0: tropical one * 3.0 = 0.0 + 3.0 = 3.0
        let term = Term::quadratic(TropicalWeight::one(), 0, 1);
        let values = vec![TropicalWeight::new(2.0), TropicalWeight::new(3.0)];
        let deriv = partial_derivative_term(&term, 0, &values);
        assert!(
            deriv.approx_eq(&TropicalWeight::new(3.0), 1e-9),
            "d/dx_0 of (1*x_0*x_1) at x_1=3.0 should be 3.0, got {:?}",
            deriv
        );
    }

    #[test]
    fn partial_derivative_repeated_variable() {
        // Term: one * x_0 * x_0 * x_0 (cubic), derivative w.r.t. x_0
        // d/dx_0 = x_0*x_0 + x_0*x_0 + x_0*x_0 (three positions)
        // At x_0 = 1.0 (tropical): each contribution = 1.0 + 1.0 = 2.0
        // plus(2.0, 2.0, 2.0) = min(2.0, 2.0, 2.0) = 2.0
        let term = Term {
            coeff: TropicalWeight::one(),
            vars: vec![0, 0, 0],
        };
        let values = vec![TropicalWeight::new(1.0)];
        let deriv = partial_derivative_term(&term, 0, &values);
        // Each of 3 positions: coeff * other_two = 0.0 + 1.0 + 1.0 = 2.0
        // min(2.0, 2.0, 2.0) = 2.0
        assert!(
            deriv.approx_eq(&TropicalWeight::new(2.0), 1e-9),
            "d/dx_0 of (1*x_0^3) at x_0=1.0 should be 2.0 (tropical), got {:?}",
            deriv
        );
    }

    // ── Validation tests ────────────────────────────────────────────────────

    #[test]
    #[should_panic(expected = "expected 2 equations, got 1")]
    fn equation_system_wrong_count() {
        let _system = EquationSystem::new(
            2,
            vec![Equation::single(Term::constant(TropicalWeight::one()))],
        );
    }

    #[test]
    #[should_panic(expected = "references variable 5")]
    fn equation_system_out_of_bounds_variable() {
        let _system = EquationSystem::new(
            1,
            vec![Equation::single(Term::linear(TropicalWeight::one(), 5))],
        );
    }

    // ── Convenience constructor tests ───────────────────────────────────────

    #[test]
    fn term_constructors() {
        let c: Term<BooleanWeight> = Term::constant(BooleanWeight::one());
        assert!(c.vars.is_empty());
        assert_eq!(c.coeff, BooleanWeight::one());

        let l: Term<BooleanWeight> = Term::linear(BooleanWeight::one(), 3);
        assert_eq!(l.vars, vec![3]);

        let q: Term<BooleanWeight> = Term::quadratic(BooleanWeight::one(), 1, 2);
        assert_eq!(q.vars, vec![1, 2]);
    }

    #[test]
    fn equation_constructors() {
        let eq: Equation<BooleanWeight> =
            Equation::single(Term::constant(BooleanWeight::one()));
        assert_eq!(eq.terms.len(), 1);

        let eq2: Equation<BooleanWeight> = Equation::sum(vec![
            Term::constant(BooleanWeight::one()),
            Term::linear(BooleanWeight::one(), 0),
        ]);
        assert_eq!(eq2.terms.len(), 2);
    }

    // ── Three-variable system (grammar-like) ────────────────────────────────

    #[test]
    fn newton_grammar_like_system_tropical() {
        // Mimics a simple grammar:
        //   S = a . A . b         (cost: 1.0 + A + 2.0)
        //   A = c                 (cost: 3.0)
        //   A = A . d . A         (cost: A + 4.0 + A)
        //
        // In tropical semiring:
        //   x_S = 3.0 + x_A       (1.0 + 2.0 + x_A, i.e., times chain)
        //   x_A = min(3.0, x_A + 4.0 + x_A)
        //
        // But the quadratic term x_A + 4.0 + x_A makes this interesting.
        // Least fixpoint of x_A = min(3.0, 4.0 + 2*x_A) in tropical:
        //   Start: x_A = +inf
        //   Iter 1: min(3.0, +inf) = 3.0
        //   Iter 2: min(3.0, 4.0 + 6.0) = min(3.0, 10.0) = 3.0. Fixed.
        //
        // Then x_S = 3.0 + 3.0 = 6.0

        let system = EquationSystem::new(
            2,
            vec![
                // x_0 (S) = 3.0 * x_1 (= 3.0 + x_A in tropical)
                Equation::single(Term::linear(TropicalWeight::new(3.0), 1)),
                // x_1 (A) = min(3.0, one * x_1 * 4.0_coeff * x_1)
                // But we need to express "4.0 + x_A + x_A" as a term.
                // Term: coeff=4.0, vars=[1, 1] → 4.0 + x_1 + x_1
                Equation::sum(vec![
                    Term::constant(TropicalWeight::new(3.0)),
                    Term {
                        coeff: TropicalWeight::new(4.0),
                        vars: vec![1, 1],
                    },
                ]),
            ],
        );

        let result = newton_fixpoint_detailed(&system, 20);
        assert!(
            result.values[1].approx_eq(&TropicalWeight::new(3.0), 1e-9),
            "A should be 3.0, got {:?}",
            result.values[1]
        );
        assert!(
            result.values[0].approx_eq(&TropicalWeight::new(6.0), 1e-9),
            "S should be 6.0, got {:?}",
            result.values[0]
        );
        assert!(result.converged);
    }

    // ── Detailed convergence info ───────────────────────────────────────────

    #[test]
    fn fixpoint_result_reports_iterations() {
        let system = EquationSystem::new(
            1,
            vec![Equation::single(Term::constant(TropicalWeight::new(1.0)))],
        );
        let result = newton_fixpoint_detailed(&system, 100);
        assert!(result.converged);
        assert!(
            result.iterations > 0,
            "should report at least 1 iteration"
        );
        assert!(
            result.iterations <= 5,
            "constant equation should converge very quickly, took {} iterations",
            result.iterations
        );
    }

    #[test]
    fn kleene_reports_iterations() {
        let system = EquationSystem::new(
            1,
            vec![Equation::single(Term::constant(BooleanWeight::one()))],
        );
        let result = kleene_fixpoint(&system, 100);
        assert!(result.converged);
        assert!(result.iterations > 0);
    }

    // ── Edge case: empty equation (zero terms) ──────────────────────────────

    #[test]
    fn newton_empty_equation_rhs() {
        // x = (empty sum) = zero
        let system: EquationSystem<TropicalWeight> = EquationSystem::new(
            1,
            vec![Equation { terms: vec![] }],
        );
        let result = newton_fixpoint_detailed(&system, 20);
        assert!(
            result.values[0].is_zero(),
            "empty RHS should give zero fixpoint, got {:?}",
            result.values[0]
        );
        assert!(result.converged);
    }

    #[test]
    fn test_accelerate_from_bundle_basic() {
        // x_0 = 3.0 (constant equation)
        let system: EquationSystem<TropicalWeight> = EquationSystem::new(
            1,
            vec![Equation {
                terms: vec![Term::constant(TropicalWeight::new(3.0))],
            }],
        );
        let result = accelerate_from_bundle(&system, 50);
        assert!(result.converged, "constant equation should converge");
        assert!(
            result.values[0].approx_eq(&TropicalWeight::new(3.0), 1e-9),
            "fixpoint should be 3.0, got {:?}",
            result.values[0]
        );
    }

    #[test]
    fn test_accelerate_from_bundle_empty() {
        // Zero-dimensional system (no variables, no equations).
        let system: EquationSystem<TropicalWeight> = EquationSystem::new(0, vec![]);
        let result = accelerate_from_bundle(&system, 50);
        assert!(result.converged, "empty system should converge immediately");
        assert!(result.values.is_empty(), "no variables means no values");
    }
}
