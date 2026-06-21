use super::*;

// ══════════════════════════════════════════════════════════════════════════════
// ArcticWeight (Max-Plus Semiring)
// ══════════════════════════════════════════════════════════════════════════════

/// Arctic (max-plus) semiring `(ℝ ∪ {-∞}, max, +, -∞, 0)`.
///
/// The dual of `TropicalWeight`: finds the **longest/heaviest** path rather
/// than the shortest. Where tropical computes minimum-cost, arctic computes
/// maximum-benefit.
///
/// - `plus = max`: selects the highest-benefit alternative
/// - `times = +`: accumulates benefits along a path
/// - `zero = -∞`: no benefit (identity for max)
/// - `one = 0.0`: zero benefit (identity for addition)
///
/// **Applications:**
/// - `cost_benefit.rs`: "speedup" dimension (higher = better) in
///   `ProductWeight<ArcticWeight, TropicalWeight>`
/// - `lint.rs`: worst-case error propagation depth (longest path through
///   inter-category graph)
/// - `decision_tree.rs`: critical-path analysis (highest parsing cost)
#[derive(Clone, Copy)]
pub struct ArcticWeight(pub f64);

impl ArcticWeight {
    /// Create a new arctic weight.
    #[inline]
    pub const fn new(value: f64) -> Self {
        ArcticWeight(value)
    }

    /// Get the underlying `f64` value.
    #[inline]
    pub const fn value(self) -> f64 {
        self.0
    }

    /// Negative infinity (unreachable / zero element).
    #[inline]
    pub const fn neg_infinity() -> Self {
        ArcticWeight(f64::NEG_INFINITY)
    }

    /// Whether this weight is negative-infinite (unreachable).
    #[inline]
    pub fn is_neg_infinite(self) -> bool {
        self.0.is_infinite() && self.0.is_sign_negative()
    }
}

impl Semiring for ArcticWeight {
    #[inline]
    fn zero() -> Self {
        ArcticWeight(f64::NEG_INFINITY)
    }

    #[inline]
    fn one() -> Self {
        ArcticWeight(0.0)
    }

    #[inline]
    fn plus(&self, other: &Self) -> Self {
        ArcticWeight(self.0.max(other.0))
    }

    #[inline]
    fn times(&self, other: &Self) -> Self {
        ArcticWeight(self.0 + other.0)
    }

    #[inline]
    fn is_zero(&self) -> bool {
        self.0.is_infinite() && self.0.is_sign_negative()
    }

    #[inline]
    fn is_one(&self) -> bool {
        self.0 == 0.0
    }

    fn approx_eq(&self, other: &Self, epsilon: f64) -> bool {
        if self.is_zero() && other.is_zero() {
            true
        } else if self.is_zero() || other.is_zero() {
            false
        } else {
            (self.0 - other.0).abs() <= epsilon
        }
    }
}

impl fmt::Debug for ArcticWeight {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.is_zero() {
            write!(f, "ArcticWeight(-inf)")
        } else {
            write!(f, "ArcticWeight({:.1})", self.0)
        }
    }
}

impl fmt::Display for ArcticWeight {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.is_zero() {
            write!(f, "-inf")
        } else {
            write!(f, "{:.1}", self.0)
        }
    }
}

impl PartialEq for ArcticWeight {
    fn eq(&self, other: &Self) -> bool {
        self.0.total_cmp(&other.0) == Ordering::Equal
    }
}

impl Eq for ArcticWeight {}

impl PartialOrd for ArcticWeight {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

/// Higher value = better. Ordering is *reversed* from tropical so that
/// generic shortest-path algorithms select the heaviest (best) alternative.
impl Ord for ArcticWeight {
    fn cmp(&self, other: &Self) -> Ordering {
        // Reverse: higher value = "lower" (better)
        other.0.total_cmp(&self.0)
    }
}

impl std::hash::Hash for ArcticWeight {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.0.to_bits().hash(state);
    }
}

impl Default for ArcticWeight {
    fn default() -> Self {
        Self::one()
    }
}

impl DetectableZero for ArcticWeight {}

impl IdempotentSemiring for ArcticWeight {}

impl CompleteSemiring for ArcticWeight {}

impl StarSemiring for ArcticWeight {
    /// `star(a) = 0.0` (one) if `a <= 0`, else diverges (returns zero).
    ///
    /// Symmetric to tropical: `max(0, a, 2a, ...)` converges to `0` when
    /// `a <= 0` (non-positive benefits cannot grow unboundedly).
    #[inline]
    fn star(&self) -> Self {
        if self.0 <= 0.0 {
            Self::one()
        } else {
            Self::zero() // diverges for positive values
        }
    }
}
