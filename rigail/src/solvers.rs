use super::*;

// ══════════════════════════════════════════════════════════════════════════════
// matrix_star_ref — Lehmann's algorithm (1977) for closed semirings,
// SemiringRef variant
// ══════════════════════════════════════════════════════════════════════════════

/// Compute `A* = (I ⊕ A)*` via Lehmann's algorithm (1977) over a
/// closed semiring, using the `SemiringRef` interface (no `Copy`
/// requirement on the weight type).
///
/// Phase C-bis (2026-05-17, per
/// `docs/design/plans/closed-semiring-cycle-handling.md` §7 Step 4 &
/// §8): the parallel of [`matrix_star`] for heap-allocated semirings
/// such as `FreeWeight`. Both share the identical Kleene-Floyd-Warshall
/// triple-nested loop:
///
/// ```text
/// for k in 0..n:
///     k_star = A[k][k].star()
///     for i in 0..n:
///         for j in 0..n:
///             A[i][j] = A[i][j] ⊕ A[i][k] ⊗ k_star ⊗ A[k][j]
/// ```
///
/// **Complexity**: O(n³) time, O(n²) space.
///
/// **Output**: a fresh `Vec<Vec<W>>` such that `A*[i][j]` is the
/// `⊕`-aggregation of all paths from vertex `i` to vertex `j`
/// (including paths that loop arbitrarily many times through any
/// vertex).
///
/// **Usage in PraTTaIL**: the per-iteration linear solver inside
/// `solve_scc_weights_newton`. Also serves directly for the
/// linear-fast-path (single-call SCCs where the Newton iteration
/// reduces to one Lehmann step).
///
/// **Panics**: if `adj` is non-square (some row length differs from `adj.len()`).
/// [`try_matrix_star_ref`] is the same computation reporting that as a value.
pub fn matrix_star_ref<W: StarSemiringRef>(adj: &[Vec<W>]) -> Vec<Vec<W>> {
    match try_matrix_star_ref(adj) {
        Ok(closure) => closure,
        Err(err) => panic!("matrix_star_ref: adj must be square (n × n) — {}", err),
    }
}

/// The row whose length disagrees with the matrix's order.
///
/// Squareness of a `&[Vec<W>]` is not expressible in Rust's type system, so it is a
/// *precondition* — and a precondition a caller can violate is a value, not a panic.
/// The offending row is carried so the diagnostic names WHICH row is wrong rather than
/// only that some row is.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct NonSquareMatrix {
    /// `adj.len()` — the order the matrix claims by its row count.
    pub order: usize,
    /// Index of the first row whose length is not `order`.
    pub row: usize,
    /// That row's actual length.
    pub row_len: usize,
}

impl std::fmt::Display for NonSquareMatrix {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "row {} has {} entries, not {}",
            self.row, self.row_len, self.order
        )
    }
}

impl std::error::Error for NonSquareMatrix {}

/// [`matrix_star_ref`], returning [`NonSquareMatrix`] rather than raising it.
///
/// # Errors
///
/// `Err(NonSquareMatrix)` iff some row of `adj` has a length other than `adj.len()`.
/// Lehmann's algorithm indexes `dist[i][j]` for every `i, j < n`, so a short row is
/// an out-of-bounds read and a long row is a silently ignored tail — neither has a
/// meaningful closure, and both must be refused rather than approximated.
pub fn try_matrix_star_ref<W: StarSemiringRef>(
    adj: &[Vec<W>],
) -> Result<Vec<Vec<W>>, NonSquareMatrix> {
    let n = adj.len();
    if let Some((row, cells)) = adj.iter().enumerate().find(|(_, row)| row.len() != n) {
        return Err(NonSquareMatrix {
            order: n,
            row,
            row_len: cells.len(),
        });
    }
    // Initialize: dist[i][j] = (I ⊕ A)[i][j].
    // The diagonal carries `one_ref() ⊕ adj[i][i]` (the zero-length-path
    // identity contribution); off-diagonal entries are just `adj[i][j]`.
    // This matches `matrix_star`'s convention (semiring.rs:2865-2878) so
    // that the two functions return numerically-equivalent closures on
    // the same input.
    let mut dist: Vec<Vec<W>> = Vec::with_capacity(n);
    for (i, adj_row) in adj.iter().enumerate().take(n) {
        let mut row = Vec::with_capacity(n);
        for (j, cell) in adj_row.iter().enumerate().take(n) {
            if i == j {
                row.push(W::one_ref().plus_ref(cell));
            } else {
                row.push(cell.clone());
            }
        }
        dist.push(row);
    }
    // Floyd-Warshall over star semiring (Lehmann 1977).
    for k in 0..n {
        let k_star = dist[k][k].star_ref();
        for i in 0..n {
            for j in 0..n {
                // dist[i][j] = dist[i][j] ⊕ dist[i][k] ⊗ k_star ⊗ dist[k][j]
                let aik = dist[i][k].clone();
                let akj = dist[k][j].clone();
                let term = aik.times_ref(&k_star).times_ref(&akj);
                dist[i][j] = dist[i][j].plus_ref(&term);
            }
        }
    }
    Ok(dist)
}

// ══════════════════════════════════════════════════════════════════════════════
// Newton's method on ω-continuous semirings (Esparza-Kiefer-Luttenberger 2007)
// for multi-call SCC fixpoints in the SPPF realize path.
//
// Per `docs/design/plans/closed-semiring-cycle-handling.md` §7 Step 4
// and `docs/design/plans/multi-call-scc-linearization.md`.
// ══════════════════════════════════════════════════════════════════════════════

/// Phase C-bis (2026-05-17, per
/// `docs/design/plans/multi-call-scc-linearization.md` §6): solve
/// `Y = f(Y)` for the inside-weight vector of one SCC, via Newton's
/// method on ω-continuous semirings.
///
/// **Algorithm**:
/// ```text
/// Y^{(0)} = 0 (semiring zero)
/// for n = 0..max_iters:
///     Df = build_differential_matrix(Y^{(n)})
///     Df* = matrix_star_ref(Df)
///     f_Y = evaluate_f(Y^{(n)})
///     Y^{(n+1)} = Df* ⊗ f_Y    (matrix-vector product)
///     if Y^{(n+1)} = Y^{(n)}: return (fixpoint reached)
/// return Y^{(max_iters)} (capped; geometric convergence for probability semirings)
/// ```
///
/// **Linear fast-path**: if every packing has `in_scc_children.len()
/// ≤ 1`, the differential `Df` is constant in `Y`. The first
/// iteration produces the exact closed form via single-shot Lehmann;
/// detected and short-circuited (zero overhead vs the original
/// Lehmann-only design).
///
/// **Inputs**:
/// - `scc_size`: dimension `k` of the per-SCC weight vector `Y ∈ W^k`.
/// - `packings`: ALL packings whose parent Symbol is in this SCC,
///   pre-factored via the parser's `factor_scc_packing`. The
///   slice may contain "exit packings" (those with `in_scc_children
///   .is_empty()`); they contribute to the `b` vector, not the
///   recursive system.
/// - `max_iters`: convergence cap. For idempotent semirings convergence
///   in `O(scc_size)` iterations (Esparza Thm 5.1); for `LogWeight` /
///   `EntropyWeight` convergence is geometric — recommended cap is 64
///   for ε ≈ 10⁻¹⁵ precision under typical probability inputs. For
///   `CountingWeight` (saturating `u64`), saturates to `u64::MAX` in
///   1 iteration on cycles.
///
/// **Output**: `Vec<W>` of length `scc_size`, with `Y[i]` the
/// cyclic inside-weight aggregate at the `i`-th Symbol in the SCC.
///
/// **References**:
/// - Esparza, J., Kiefer, S., Luttenberger, M. (2007). "An Extension
///   of Newton's Method to ω-Continuous Semirings." DLT 2007. The
///   canonical reference for this technique.
/// - Lehmann, D. J. (1977). "Algebraic Structures for Transitive
///   Closure." TCS 4(1). The per-iteration linear solver.
/// - Goodman, J. (1999). "Semiring Parsing." Comp. Ling. 25(4). The
///   foundational framework.
#[allow(dead_code)]
pub fn solve_scc_weights_newton<W: StarSemiringRef>(
    scc_size: usize,
    packings: &[PackingFactored<W>],
    max_iters: usize,
) -> Vec<W> {
    // b vector: exit-packing contributions (no in-SCC children).
    let mut b = vec![W::zero_ref(); scc_size];
    for p in packings {
        if p.in_scc_children.is_empty() {
            b[p.target_i] = b[p.target_i].plus_ref(&p.outside_product);
        }
    }

    // LINEAR FAST-PATH: every packing has in_scc_children.len() ≤ 1.
    // Differential is constant in Y → first Newton iteration = exact
    // closed form via single-shot Lehmann.
    let is_linear = packings.iter().all(|p| p.in_scc_children.len() <= 1);
    if is_linear {
        // Build A matrix (constant; no dependence on Y).
        let mut a = vec![vec![W::zero_ref(); scc_size]; scc_size];
        for p in packings {
            if let Some(&j) = p.in_scc_children.first() {
                a[p.target_i][j] = a[p.target_i][j].plus_ref(&p.outside_product);
            }
        }
        let a_star = matrix_star_ref(&a);
        return (0..scc_size)
            .map(|i| {
                let mut acc = W::zero_ref();
                for j in 0..scc_size {
                    acc = acc.plus_ref(&a_star[i][j].times_ref(&b[j]));
                }
                acc
            })
            .collect();
    }

    // NEWTON ITERATION for multi-call SCCs.
    let mut y = vec![W::zero_ref(); scc_size];
    for _iter in 0..max_iters {
        let df = build_differential_matrix(&y, packings, scc_size);
        let df_star = matrix_star_ref(&df);
        let f_y = evaluate_f(&y, packings, &b, scc_size);
        let y_next: Vec<W> = (0..scc_size)
            .map(|i| {
                let mut acc = W::zero_ref();
                for j in 0..scc_size {
                    acc = acc.plus_ref(&df_star[i][j].times_ref(&f_y[j]));
                }
                acc
            })
            .collect();
        if y_next == y {
            return y_next; // monotone fixpoint reached
        }
        y = y_next;
    }
    y // capped — geometric convergence; final iterate is best-effort
}

/// Phase C-bis (2026-05-17): build the formal differential matrix
/// `Df(Y)` by the multi-variable Leibniz rule.
///
/// For each [`PackingFactored`] `P` with
/// `in_scc_children = [c_1, ..., c_m]` and parent `target_i`:
///
/// For each position `k ∈ 1..=m`:
/// ```text
/// ∂f_{target_i}/∂Y_{c_k} = outside_product
///                          ⊗ Π_{l < k} Y[c_l]
///                          ⊗ Π_{l > k} Y[c_l]
/// ```
/// `Df[target_i][c_k] ⊕= that partial`.
///
/// **Why the per-position decomposition**: the Leibniz rule states
/// that the derivative of `Y_a ⊗ Y_b ⊗ Y_c` with respect to `Y_a` is
/// `Y_b ⊗ Y_c` (treating `Y_a` as the variable; all other factors
/// stay at their current iterate `Y^{(n)}`). When the same `Y_j`
/// appears at multiple positions in `in_scc_children`, this is
/// handled correctly by visiting each position separately and
/// `⊕`-ing the result into `Df[target_i][j]`.
///
/// **Complexity**: O(packings × max_arity²) per call, dominated by
/// the product computation for each Leibniz partial.
///
/// **Exit packings** (`in_scc_children.is_empty()`): contribute to
/// the `b` vector, not the differential. Skipped here.
#[allow(dead_code)]
pub(crate) fn build_differential_matrix<W: SemiringRef>(
    y: &[W],
    packings: &[PackingFactored<W>],
    n: usize,
) -> Vec<Vec<W>> {
    let mut df = vec![vec![W::zero_ref(); n]; n];
    for p in packings {
        let m = p.in_scc_children.len();
        if m == 0 {
            continue; // exit packing — contributes to b, not Df
        }
        for k in 0..m {
            // Compute Π_{l ≠ k} Y[in_scc_children[l]] ⊗ outside_product.
            let mut prod = p.outside_product.clone();
            for l in 0..m {
                if l != k {
                    prod = prod.times_ref(&y[p.in_scc_children[l]]);
                }
            }
            let j = p.in_scc_children[k];
            df[p.target_i][j] = df[p.target_i][j].plus_ref(&prod);
        }
    }
    df
}

/// Phase C-bis (2026-05-17): evaluate `f(Y)` — for each Symbol in the
/// SCC, sum over all packings the contribution `outside_product ⊗ Π
/// Y[in_scc_children]`, then add `b` (exit-packing contributions).
///
/// Used inside [`solve_scc_weights_newton`] as the function-value
/// computation at each iterate.
///
/// **Complexity**: O(packings × max_arity) per call.
#[allow(dead_code)]
pub(crate) fn evaluate_f<W: SemiringRef>(
    y: &[W],
    packings: &[PackingFactored<W>],
    b: &[W],
    _n: usize,
) -> Vec<W> {
    let mut f = b.to_vec();
    for p in packings {
        if p.in_scc_children.is_empty() {
            continue; // already in b
        }
        let mut prod = p.outside_product.clone();
        for &c in &p.in_scc_children {
            prod = prod.times_ref(&y[c]);
        }
        f[p.target_i] = f[p.target_i].plus_ref(&prod);
    }
    f
}

// ══════════════════════════════════════════════════════════════════════════════
// matrix_star — Generalized Floyd-Warshall (Sprint 6)
// ══════════════════════════════════════════════════════════════════════════════

/// Compute the star (transitive closure) of an `n×n` adjacency matrix
/// over a star semiring. Generalized Floyd-Warshall: `O(n³)`.
///
/// Entry `result[i][j]` = ⊕ over all paths from `i` to `j` of ⊗ over
/// edge weights along each path, including the identity (zero-length path).
///
/// **Semiring-specific interpretations:**
/// - `BooleanWeight`: reachability (reflexive-transitive closure)
/// - `TropicalWeight`: all-pairs shortest paths
/// - `ArcticWeight`: all-pairs longest paths
/// - `CountingWeight`: all-pairs path counts (may saturate)
/// - `EditWeight`: all-pairs minimum edit distance
///
/// The algorithm is the standard Floyd-Warshall generalization to star
/// semirings (Lehmann 1977, Byorgey 2016): for each intermediate vertex `k`,
/// relax all `(i, j)` pairs via `i→k→j` using `star(k→k)` for self-loops.
///
/// **Panics** if `adj` is not square.
pub fn matrix_star<W: StarSemiring>(adj: &[Vec<W>]) -> Vec<Vec<W>> {
    let n = adj.len();
    for row in adj {
        assert_eq!(row.len(), n, "matrix_star: adjacency matrix must be square");
    }

    // Initialize: dist[i][j] = adj[i][j], with identity on the diagonal.
    let mut dist: Vec<Vec<W>> = Vec::with_capacity(n);
    for (i, adj_row) in adj.iter().enumerate().take(n) {
        let mut row = Vec::with_capacity(n);
        for (j, cell) in adj_row.iter().enumerate().take(n) {
            if i == j {
                // Identity (zero-length path) ⊕ direct edge
                row.push(W::one().plus(cell));
            } else {
                row.push(*cell);
            }
        }
        dist.push(row);
    }

    // Floyd-Warshall with star semiring:
    // For each intermediate vertex k, relax all (i, j) pairs.
    for k in 0..n {
        let k_star = dist[k][k].star();
        for i in 0..n {
            for j in 0..n {
                // dist[i][j] ⊕= dist[i][k] ⊗ star(dist[k][k]) ⊗ dist[k][j]
                let via_k = dist[i][k].times(&k_star).times(&dist[k][j]);
                dist[i][j] = dist[i][j].plus(&via_k);
            }
        }
    }

    dist
}
