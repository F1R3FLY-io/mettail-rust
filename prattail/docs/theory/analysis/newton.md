# Newton's Method for Semiring Fixpoints

| Property | Value |
|----------|-------|
| **Feature gate** | `newton` |
| **Source file** | `prattail/src/newton.rs` (~1459 lines) |
| **Pipeline phase** | Fixpoint acceleration (internal optimization) |
| **Lint codes** | (internal -- no direct lint output) |

## 1. Rationale

Many PraTTaIL analyses reduce to computing the least fixpoint of a system of
polynomial equations over a semiring. Naive Kleene iteration (`kappa_0 = 0,
kappa_{i+1} = F(kappa_i)`) converges monotonically but may require many
iterations (or infinitely many for non-idempotent semirings). Newton's method,
adapted from numerical analysis to the semiring setting by Esparza, Kiefer &
Luttenberger (2010), accelerates convergence by linearizing `F` at each iterate
and solving the linearized system via Jacobian closure.

## 2. Theoretical Foundations

### 2.1. Polynomial Equation Systems

**Definition (Polynomial Equation System).** Given a semiring
`(S, oplus, otimes, 0, 1)`, a system of `n` equations in `n` unknowns:

```
X_0 = F_0(X_0, ..., X_{n-1})
X_1 = F_1(X_0, ..., X_{n-1})
...
X_{n-1} = F_{n-1}(X_0, ..., X_{n-1})
```

where each `F_i` is a polynomial: a finite sum of terms, each term being a
product of a coefficient and zero or more variables.

**Definition (Term).** A term `c * X_{i_1} * X_{i_2} * ... * X_{i_k}` has:
- Coefficient `c in S`
- Variables `X_{i_1}, ..., X_{i_k}` (with repetition allowed)
- Degree `k` (number of variable occurrences)

### 2.2. Jacobian Matrix

**Definition (Semiring Jacobian).** The Jacobian `J_F(X)` is the `n x n` matrix
where entry `J[i][j]` is the formal partial derivative of `F_i` with respect
to `X_j`:

```
d(c * X_{i_1} * ... * X_{i_k}) / dX_j =
    oplus over positions p where i_p = j:
        c * X_{i_1} * ... * X_{i_{p-1}} * X_{i_{p+1}} * ... * X_{i_k}
```

In semiring terms, the derivative of a product `a * x * b` with respect to `x`
is `a otimes b` (remove one occurrence of `x` and multiply the rest).

### 2.3. Newton's Method

**Algorithm (Newton Iteration).**

```
nu_0 = 0  (the zero vector)
nu_{i+1} = J_F(nu_i)^* . F(nu_i)
```

where `J^*` is the Kleene closure of the Jacobian matrix (computed via
`matrix_star`).

**Theorem (Convergence; Esparza, Kiefer & Luttenberger 2010).**

1. For **omega-continuous** semirings, Newton's method converges monotonically
   to the least fixpoint.
2. For **idempotent** semirings (`a oplus a = a`, e.g., Tropical, Boolean),
   Newton converges in at most `h + 1` iterations, where `h` is the Strahler
   number (tree height) of the equation system.
3. Each Newton iterate `nu_i` is a lower bound: `nu_i <= mu` where `mu` is
   the least fixpoint.
4. Newton "dominates" Kleene: `kappa_i <= nu_i` for all `i >= 0`.

### 2.4. Matrix Star Computation

The Kleene closure `J^*` of an `n x n` matrix is computed via the
Floyd-Warshall generalization for semirings (from `semiring.rs::matrix_star`):

```
J^* = I oplus J oplus J^2 oplus J^3 oplus ...
```

For a `StarSemiring`, this is computed in O(n^3) via:

```
for k in 0..n:
    for i in 0..n:
        for j in 0..n:
            M[i][j] = M[i][j] oplus (M[i][k] otimes star(M[k][k]) otimes M[k][j])
```

## 3. Algorithm Pseudocode

### 3.1. Newton Fixpoint (Detailed)

```
function newton_fixpoint_detailed(system: EquationSystem<W>, max_iter: usize)
    -> FixpointResult<W>:

    n := system.num_variables
    if n == 0: return ([], 0, true)

    values := [W::zero(); n]   // nu_0 = 0

    for iter in 0..max_iter:
        // Step 1: Evaluate F(values)
        f_values := [evaluate_equation(eq, values) for eq in system.equations]

        // Step 2: Compute Jacobian J_F(values)
        jac := jacobian(system, values)   // n x n matrix

        // Step 3: Compute J^* via matrix_star
        j_star := matrix_star(jac)

        // Step 4: Compute new_values = J^* . F(values)
        new_values := [W::zero(); n]
        for i in 0..n:
            for j in 0..n:
                new_values[i] oplus= j_star[i][j] otimes f_values[j]

        // Step 5: Check convergence
        if new_values == values:
            return (new_values, iter + 1, true)  // converged

        values := new_values

    return (values, max_iter, false)  // did not converge
```

### 3.2. Jacobian Computation

```
function jacobian(system: EquationSystem<W>, values: [W; n]) -> [[W; n]; n]:
    jac := [[W::zero(); n]; n]

    for (i, equation) in system.equations:
        for term in equation.terms:
            for (pos, var_j) in term.vars.enumerate():
                // Derivative: remove var at position pos, multiply the rest
                deriv := term.coefficient
                for (p, var_v) in term.vars.enumerate():
                    if p != pos:
                        deriv := deriv otimes values[var_v]
                jac[i][var_j] oplus= deriv

    return jac
```

### 3.3. Term Evaluation

```
function evaluate_term(term: Term<W>, values: [W; n]) -> W:
    result := term.coefficient
    for var in term.vars:
        result := result otimes values[var]
    return result

function evaluate_equation(eq: Equation<W>, values: [W; n]) -> W:
    result := W::zero()
    for term in eq.terms:
        result := result oplus evaluate_term(term, values)
    return result
```

## 4. Complexity Analysis

| Operation | Time | Space |
|-----------|------|-------|
| `evaluate_term` | O(k) | O(1) |
| `evaluate_equation` | O(T * k) | O(1) |
| `jacobian` | O(n * T * k) | O(n^2) |
| `matrix_star` | O(n^3) | O(n^2) |
| Newton iteration (per step) | O(n^3 + n * T * k) | O(n^2) |
| Newton fixpoint (total) | O(I * (n^3 + n * T * k)) | O(n^2) |

Where: n = number of variables/equations, T = max terms per equation,
k = max degree per term, I = number of iterations (at most `h + 1` for
idempotent semirings, `max_iter` otherwise).

## 5. Unicode Diagrams

### 5.1. Newton vs. Kleene Convergence

```
    Value
    ^
    |           ┌──── mu (least fixpoint)
    |     ......|.....................................
    |    /      |
    |   /    nu_2 ─── Newton converges in 3 steps
    |  /     /  |
    | /  nu_1   |     kappa_5 ─── Kleene needs 6 steps
    |/   / kappa_4
    | nu_0  kappa_3
    |/  kappa_2
    |  kappa_1
    | kappa_0
    └──────────────────────────────────> iteration
         0  1  2  3  4  5  6

    Newton dominates: nu_i >= kappa_i for all i.
```

### 5.2. Algorithm Flow

```
    EquationSystem<W>
          │
          v
    ┌──────────────────────┐
    │  Initialize nu_0 = 0 │
    └──────────┬───────────┘
               │
     ┌─────────v──────────┐
     │  Evaluate F(nu_i)  │<──────────────┐
     └─────────┬──────────┘               │
               │                          │
     ┌─────────v──────────┐               │
     │  Compute Jacobian  │               │
     │  J_F(nu_i)         │               │
     └─────────┬──────────┘               │
               │                          │
     ┌─────────v──────────┐               │
     │  matrix_star(J)    │               │
     │  -> J^*            │               │
     └─────────┬──────────┘               │
               │                          │
     ┌─────────v──────────┐               │
     │  nu_{i+1} =        │               │
     │  J^* . F(nu_i)     │               │
     └─────────┬──────────┘               │
               │                          │
        ┌──────v──────┐                   │
        │ Converged?  │──── no ──────────>│
        └──────┬──────┘                   │
               │ yes                      │
               v
    ┌──────────────────────┐
    │  Return FixpointResult│
    │  (values, iters, ok) │
    └──────────────────────┘
```

### 5.3. Jacobian Example

```
    System: x_0 = a * x_0 + b * x_1
            x_1 = c * x_0^2

    Jacobian J[i][j] = dF_i / dX_j:

    J = ┌──────────────────────────┐
        │ dF_0/dX_0 = a           │ dF_0/dX_1 = b           │
        │ dF_1/dX_0 = c*x_0 + c*x_0│ dF_1/dX_1 = 0          │
        └──────────────────────────┘

    At x_0 = v0, x_1 = v1:
    J(v) = ┌────────────────────────┐
           │   a        b           │
           │ 2c*v0      0           │
           └────────────────────────┘
```

## 6. PraTTaIL Integration

### 6.1. Pipeline Bridge Functions

- `newton_fixpoint(system, max_iter)` -- Returns the fixpoint value vector.
- `newton_fixpoint_detailed(system, max_iter)` -- Returns full `FixpointResult`
  (values, iterations, converged flag).
- `accelerate_from_bundle(system, max_iter)` -- Pipeline bridge wrapping
  `newton_fixpoint_detailed`.
- `evaluate_term(term, values)` -- Evaluates a single polynomial term.
- `evaluate_equation(eq, values)` -- Evaluates a sum of terms.
- `jacobian(system, values)` -- Computes the `n x n` Jacobian matrix.

### 6.2. Lint Emission

No direct lint output. Newton acceleration is an internal optimization used by
other analyses (WPDS dataflow, algebraic analysis). Callers inspect the
`FixpointResult` and produce their own diagnostics.

### 6.3. Repair Integration

No repairs. Newton is a solver, not a verifier.

## 7. Rust Implementation Notes

| Type | Role |
|------|------|
| `Term<W>` | Polynomial term: `coefficient: W`, `vars: Vec<usize>` (variable indices, with repetition for degree > 1) |
| `Equation<W>` | Sum of terms: `terms: Vec<Term<W>>` |
| `EquationSystem<W>` | System: `num_variables: usize`, `equations: Vec<Equation<W>>` |
| `FixpointResult<W>` | Result: `values: Vec<W>`, `iterations: usize`, `converged: bool` |

Smart constructors:
- `Term::constant(w)` -- Degree-0 term (just a coefficient).
- `Term::linear(w, var)` -- Degree-1 term `w * X_var`.
- `Term::quadratic(w, v1, v2)` -- Degree-2 term `w * X_v1 * X_v2`.

The `EquationSystem::new` constructor validates that all variable references
are within bounds and that the number of equations equals `num_variables`.

## 8. Worked Example

**System:** `x = 2 * x + 3` (tropical semiring).

```
Tropical interpretation: x = min(2 + x, 3)
Fixpoint: x = 3 (since min(2 + 3, 3) = min(5, 3) = 3)
```

**Newton iteration:**

```
nu_0 = +inf (tropical zero)

Iteration 1:
  F(nu_0) = min(2 + inf, 3) = 3
  J(nu_0) = [a] = [2]  (derivative of "a * x" w.r.t. x = a)
  J* = [star(2)] = [0]  (tropical star: value >= 0 -> 0)
  nu_1 = J* * F(nu_0) = 0 + 3 = 3  (tropical times = +)

Iteration 2:
  F(nu_1) = min(2 + 3, 3) = 3
  J(nu_1) = [2]
  J* = [0]
  nu_2 = 0 + 3 = 3

  nu_2 == nu_1: converged!
  Result: x = 3, iterations = 2, converged = true.
```

**Two-variable system:** `x_0 = min(1 + x_1, 5)`, `x_1 = min(2 + x_0, 3)`.

```
Tropical encoding:
  x_0 = 1 * x_1 + 5   (min of two terms)
  x_1 = 2 * x_0 + 3

nu_0 = (+inf, +inf)

Iteration 1:
  F(nu_0) = (min(1+inf, 5), min(2+inf, 3)) = (5, 3)
  J = [[0, 1], [2, 0]]
  J* via matrix_star = [[0, 1], [2, 0+1+2]] = approx [[0, 1], [2, 3]]
  Actually: J* = [[star(1*2), 1*star(2*1)], [2*star(1*2), star(2*1)]]
           = [[0, 1+0], [2+0, 0]] = [[0, 1], [2, 0]]
  nu_1 = J* * F:
    nu_1[0] = min(0+5, 1+3) = min(5, 4) = 4
    nu_1[1] = min(2+5, 0+3) = min(7, 3) = 3

Iteration 2:
  F(nu_1) = (min(1+3, 5), min(2+4, 3)) = (4, 3)
  nu_2 = J* * F:
    nu_2[0] = min(0+4, 1+3) = 4
    nu_2[1] = min(2+4, 0+3) = 3
  nu_2 == nu_1: converged!
  Result: (x_0 = 4, x_1 = 3), iterations = 2.
```

## 9. References

1. Esparza, J., Kiefer, S. & Luttenberger, M. (2010).
   "Newtonian Program Analysis."
   *Journal of the ACM*, 57(6), Article 33.

2. Esparza, J., Kiefer, S. & Luttenberger, M. (2007).
   "An Extension of Newton's Method to omega-Continuous Semirings."
   *Proc. 11th International Conference on Developments in Language Theory
   (DLT)*, LNCS 4588, Springer, pp. 157--168.

3. Hopkins, M.W. & Kozen, D. (1999).
   "Parikh's Theorem in Commutative Kleene Algebra."
   *Proc. 14th Annual IEEE Symposium on Logic in Computer Science (LICS)*,
   pp. 394--401.

4. Luttenberger, M. (2012).
   "Semiring-Based Programming and Verification."
   PhD thesis, Technical University of Munich.

5. Reps, T., Turetsky, E. & Prabhu, P. (2016).
   "Newtonian Program Analysis via Tensor Product."
   *Proc. 43rd ACM SIGPLAN-SIGACT Symposium on Principles of Programming
   Languages (POPL)*, pp. 663--677.
