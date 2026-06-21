use super::*;

/// A production packing pre-factored for the Newton-SCC cyclic weight solver.
/// Relocated from the parser's `sppf.rs` (built by `Sppf::factor_scc_packing`)
/// so the weight algebra is self-contained and substrate-agnostic.
///
/// - `target_i`: SCC-local index of the parent Symbol `s_i`.
/// - `outside_product`: per-production `Packing.weight` ⊗ the inside-weights of
///   all children OUTSIDE the SCC (constant w.r.t. the cyclic unknowns).
/// - `in_scc_children`: SCC-local indices of in-SCC children, in source order
///   (order matters for the multi-variable Leibniz differential).
#[derive(Debug, Clone)]
pub struct PackingFactored<W: SemiringRef> {
    /// SCC-local index of the parent Symbol s_i.
    pub target_i: usize,
    /// `Packing.weight ⊗ Π_{c ∈ Packing.children, c ∉ SCC} memo[c].weight_sum`.
    pub outside_product: W,
    /// SCC-local indices of in-SCC children, in source order.
    pub in_scc_children: Vec<usize>,
}

// ══════════════════════════════════════════════════════════════════════════════
// Semiring trait
// ══════════════════════════════════════════════════════════════════════════════

/// A semiring `(K, +, *, 0, 1)` where `+` combines parallel paths and `*`
/// sequences path segments.
///
/// Properties required:
/// - `(K, +, 0)` is a commutative monoid
/// - `(K, *, 1)` is a monoid
/// - `*` distributes over `+`
/// - `0 * a = a * 0 = 0` (zero annihilates)
pub trait Semiring: Clone + Copy + fmt::Debug + PartialEq + Send + Sync + 'static {
    /// Additive identity. For tropical: `+inf` (unreachable).
    fn zero() -> Self;
    /// Multiplicative identity. For tropical: `0.0` (zero cost).
    fn one() -> Self;
    /// Semiring addition: combines parallel paths. For tropical: `min(a, b)`.
    fn plus(&self, other: &Self) -> Self;
    /// Semiring multiplication: sequences path segments. For tropical: `a + b`.
    fn times(&self, other: &Self) -> Self;
    /// Whether this is the additive identity.
    fn is_zero(&self) -> bool;
    /// Whether this is the multiplicative identity.
    fn is_one(&self) -> bool;
    /// Approximate equality for floating-point convergence checks.
    fn approx_eq(&self, other: &Self, epsilon: f64) -> bool;
    /// EP-P4 (Stage E) ESS support: the scalar PRIMARY path cost this
    /// weight carries, if one is meaningful, as an `f64` where LOWER = more
    /// likely (a tropical / `-log`-probability cost; the path likelihood
    /// mass is `exp(-cost)`). Returns `None` for weights with no scalar
    /// primary (the default — e.g. boolean / counting / free semirings),
    /// which the ESS fold treats as "no information" and skips. Used ONLY
    /// to compute the frontier effective-sample-size at a budget/EOI event
    /// (never on the hot path). Default `None`.
    #[inline]
    fn ess_primary_cost(&self) -> Option<f64> {
        None
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// Trait hierarchy extensions
// ══════════════════════════════════════════════════════════════════════════════

/// Marker trait: this semiring's `is_zero()` is O(1) and reliable.
///
/// All PraTTaIL semirings satisfy this — the trait exists as a bound for
/// algorithms that require efficient zero-weight pruning (e.g., dead-state
/// elimination, sparse matrix operations).
pub trait DetectableZero: Semiring {}

/// Marker trait: `a ⊕ a = a` for all `a` (idempotent addition).
///
/// Guarantees fixed-point convergence in iterative algorithms (e.g.,
/// shortest-path relaxation, forward-backward scoring). Non-idempotent
/// semirings like `CountingWeight` and `LogWeight` require explicit
/// convergence criteria.
pub trait IdempotentSemiring: Semiring {}

/// Marker trait: infinite sums `Σ_{i∈I} aᵢ` are well-defined.
///
/// Required for well-defined semantics of `StarSemiring::star()` and for
/// forward-backward algorithms over cyclic grammars. All idempotent
/// semirings are complete (idempotent ⊕ guarantees convergence).
pub trait CompleteSemiring: Semiring {}

/// Star semiring: Kleene closure `a* = 1 ⊕ a ⊕ a² ⊕ ...`
///
/// Enables transitive closure computation over any semiring. Key applications:
/// - **Reachability** (`BooleanWeight`): reflexive-transitive closure
/// - **All-pairs shortest paths** (`TropicalWeight`): Floyd-Warshall
/// - **Longest paths** (`ArcticWeight`): critical-path analysis
/// - **Path counting** (`CountingWeight`): total derivation count
///
/// Every complete star semiring is Conway, satisfying:
/// - Sum-star: `(a ⊕ b)* = (a* ⊗ b)* ⊗ a*`
/// - Product-star: `(a ⊗ b)* = 1 ⊕ a ⊗ (b ⊗ a)* ⊗ b`
pub trait StarSemiring: Semiring {
    /// Kleene star: `a* = 1 ⊕ a ⊕ a² ⊕ ...` (infinite sum of powers).
    fn star(&self) -> Self;

    /// Kleene plus: `a⁺ = a ⊗ a*` (star without the identity term).
    fn plus_star(&self) -> Self {
        self.times(&self.star())
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// SemiringRef — semiring trait without the Copy requirement
// ══════════════════════════════════════════════════════════════════════════════

/// Semiring trait without the `Copy` requirement.
///
/// For semirings whose carrier type requires heap allocation (e.g., `FreeWeight`
/// with an AST of symbolic expressions, or large `ParikhWeight<D>` vectors).
/// All operations take `&self` references and return owned values.
///
/// Properties required (same as [`Semiring`]):
/// - `(K, ⊕, 0)` is a commutative monoid
/// - `(K, ⊗, 1)` is a monoid
/// - `⊗` distributes over `⊕`
/// - `0 ⊗ a = a ⊗ 0 = 0` (zero annihilates)
pub trait SemiringRef: Clone + fmt::Debug + PartialEq + Send + Sync + 'static {
    /// Additive identity.
    fn zero_ref() -> Self;
    /// Multiplicative identity.
    fn one_ref() -> Self;
    /// Semiring addition: combines parallel paths.
    fn plus_ref(&self, other: &Self) -> Self;
    /// Semiring multiplication: sequences path segments.
    fn times_ref(&self, other: &Self) -> Self;
    /// Whether this is the additive identity.
    fn is_zero_ref(&self) -> bool;
    /// Whether this is the multiplicative identity.
    fn is_one_ref(&self) -> bool;
    /// EP-P4 (Stage E) ESS support — see [`Semiring::ess_primary_cost`].
    /// Default `None`; the blanket `impl<T: Semiring>` forwards to the
    /// `Semiring` method so `LexicographicWeight`'s override is visible
    /// through `SemiringRef` bounds (the walker is generic over
    /// `SemiringRef`). Never on the hot path.
    #[inline]
    fn ess_primary_cost_ref(&self) -> Option<f64> {
        None
    }
}

/// Blanket implementation: every `Semiring` (which requires `Copy`) automatically
/// satisfies `SemiringRef`.
///
/// This allows algorithms parameterized by `SemiringRef` to accept both
/// `Copy` semirings (e.g., `TropicalWeight`) and heap-allocated semirings
/// (e.g., `FreeWeight`).
impl<T: Semiring> SemiringRef for T {
    #[inline]
    fn zero_ref() -> Self {
        T::zero()
    }

    #[inline]
    fn one_ref() -> Self {
        T::one()
    }

    #[inline]
    fn plus_ref(&self, other: &Self) -> Self {
        self.plus(other)
    }

    #[inline]
    fn times_ref(&self, other: &Self) -> Self {
        self.times(other)
    }

    #[inline]
    fn is_zero_ref(&self) -> bool {
        self.is_zero()
    }

    #[inline]
    fn is_one_ref(&self) -> bool {
        self.is_one()
    }

    #[inline]
    fn ess_primary_cost_ref(&self) -> Option<f64> {
        // Forward to the Semiring override (LexicographicWeight provides a
        // real primary; all others fall to the trait default `None`).
        Semiring::ess_primary_cost(self)
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// StarSemiringRef — star semiring without the Copy requirement
// ══════════════════════════════════════════════════════════════════════════════

/// Star semiring trait without the `Copy` requirement (Phase C-bis,
/// 2026-05-17, per
/// `docs/design/plans/closed-semiring-cycle-handling.md` §8).
///
/// Mirrors [`StarSemiring`] for the heap-allocated semiring family.
/// Operations take `&self` and return owned values.
///
/// **Mathematical content** identical to [`StarSemiring`]: `a*` is the
/// Kleene closure `1 ⊕ a ⊕ a² ⊕ ...` — the closed-form solution to the
/// recurrence `Y = aY ⊕ 1`.
///
/// **Used by**: `matrix_star_ref` (Lehmann's algorithm) and
/// `solve_scc_weights_newton` (Newton's method per
/// [Esparza-Kiefer-Luttenberger 2007]). The non-`Copy` variant lets
/// closed-semiring cycle handling work uniformly across both `Copy`
/// semirings (TropicalWeight, BooleanWeight, etc.) and heap-allocated
/// ones (FreeWeight, ParikhWeight<D>).
///
/// [Esparza-Kiefer-Luttenberger 2007]:
/// https://link.springer.com/chapter/10.1007/978-3-540-73208-2_17
pub trait StarSemiringRef: SemiringRef {
    /// Kleene star: `a* = 1 ⊕ a ⊕ a² ⊕ ...`
    ///
    /// For probability-like semirings (`LogWeight`, etc.) where
    /// `1 - a` may diverge, implementations return [`Self::zero_ref`]
    /// to signal divergence (the additive-identity acts as the
    /// "diverged sentinel" under monotone semantics).
    fn star_ref(&self) -> Self;

    /// Kleene plus: `a⁺ = a ⊗ a*` — star without the identity term.
    fn plus_star_ref(&self) -> Self {
        self.times_ref(&self.star_ref())
    }
}

/// Blanket implementation: every `StarSemiring` (which requires `Copy`)
/// automatically satisfies `StarSemiringRef`.
impl<T: StarSemiring> StarSemiringRef for T {
    #[inline]
    fn star_ref(&self) -> Self {
        self.star()
    }

    #[inline]
    fn plus_star_ref(&self) -> Self {
        self.plus_star()
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// TropicalDeltaWeight — per-Phase F.13 H12 Stage 1.5.3 (2026-05-21)
// ══════════════════════════════════════════════════════════════════════════════

/// Phase F.13 H12 Stage 1.5.3 (2026-05-21): semiring extension that
/// supports recovering a multiplicative delta `delta(pre, post)` such
/// that `pre ⊗ delta = post` on the PRIMARY (tropical) component.
///
/// Required by `dispatch_cohort` revive to compute per-packing cohort
/// cursor weight: `cohort.pre ⊗ delta(worker.pre, worker.post)` =
/// `cohort.pre ⊗ (sum of Fork branch weights along worker's path)`.
///
/// Implemented for [`LexicographicWeight`] via tropical primary
/// subtraction (`f64::-`). Default implementation panics in debug
/// (forces explicit override) and returns `post` in release
/// (defensive but degenerate).
///
/// **Soundness for LexicographicWeight**: under left-projection
/// semantics of [`Semiring::times`], `cohort.pre ⊗ delta` produces a
/// weight whose primary is `cohort.pre.primary + delta.primary` and
/// whose tiebreak is `cohort.pre.tiebreak` (when cohort.pre is
/// non-identity, which is invariant for production cohort sites —
/// every cross-cat dispatch traverses at least one non-identity
/// `BP_TIER_*`-weighted ForkBranch arm).
///
/// **Mathematical content**: in tropical (min, +) arithmetic, the
/// `times` operator is `+`, which is invertible. Therefore for any
/// `(pre, post)`, the unique delta satisfying `pre ⊗ delta = post`
/// (on the tropical primary component alone) is `post.primary -
/// pre.primary`. The tiebreak fields of `delta` are algebraically
/// irrelevant under cohort.pre's left-projection; we preserve
/// `post.tiebreak` to document intent.
pub trait TropicalDeltaWeight: SemiringRef {
    /// Compute the multiplicative delta on the primary component:
    /// `delta(pre, post)` such that `pre ⊗ delta = post` (modulo
    /// tiebreak fields).
    ///
    /// Default panics in debug (forces explicit override); returns
    /// `post` in release as a degenerate fallback.
    fn tropical_primary_delta(pre: &Self, post: &Self) -> Self {
        let _ = pre;
        debug_assert!(
            false,
            "TropicalDeltaWeight default impl invoked — override required \
             for weight types used by the cohort cache (production: \
             LexicographicWeight)"
        );
        post.clone()
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// LexProvenance — per-Phase F.13 Stage 2.0 (2026-05-22)
// ══════════════════════════════════════════════════════════════════════════════

/// Phase F.13 Stage 2.0 (2026-05-22): expose a cursor's lex-Fork
/// branch provenance for inclusion in `ConfigKey`. This completes
/// the GLL/Tomita descriptor with lex-disambiguation identity:
/// two cursors with distinct lex-Fork branch stamps represent
/// distinct parses under different lex-disambiguation choices and
/// must NOT merge.
///
/// `LexicographicWeight` carries explicit fields (`lex_alt_idx`,
/// `src_idx`, `rule_idx`) populated at lex-Fork emit sites via
/// `from_cost_with_lex`. `LexicographicWeight::times` left-projects,
/// so these stamps stay constant along a cursor's path after the
/// first non-identity multiplication.
///
/// Default impls return 0 for weight types without inherent lex
/// provenance (e.g., `BooleanWeight`, `TropicalWeight`); they merge
/// as before (all cursors share identical provenance, no
/// discrimination).
pub trait LexProvenance: SemiringRef {
    /// Lex-Fork branch index stamped at emit time (alt_idx=0 for
    /// primary, alt_idx≥1 for secondaries).
    fn lex_alt_idx(&self) -> u16 {
        0
    }
    /// Source category index of the rule the lex-Fork branch
    /// dispatched to.
    fn lex_src_idx(&self) -> u16 {
        0
    }
    /// Rule index within the source category.
    fn lex_rule_idx(&self) -> u16 {
        0
    }
}
