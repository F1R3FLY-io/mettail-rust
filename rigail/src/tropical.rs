use super::*;

// ══════════════════════════════════════════════════════════════════════════════
// TropicalWeight
// ══════════════════════════════════════════════════════════════════════════════

/// Tropical semiring weight: `(R+ union {+inf}, min, +, +inf, 0.0)`.
///
/// - `plus = min`: selects the best (lowest-cost) alternative
/// - `times = +`: accumulates costs along a path
/// - `zero = +inf`: unreachable (identity for min)
/// - `one = 0.0`: zero cost (identity for addition)
///
/// Lower weight = higher priority. Maps directly to PraTTaIL's existing
/// `TokenKind::priority()` system via `weight = MAX_PRIORITY - priority`.
///
/// Implements total ordering via `f64::total_cmp` (NaN-safe).
#[derive(Clone, Copy)]
pub struct TropicalWeight(pub f64);

impl TropicalWeight {
    /// Create a new tropical weight.
    #[inline]
    pub const fn new(value: f64) -> Self {
        TropicalWeight(value)
    }

    /// Get the underlying `f64` value.
    #[inline]
    pub const fn value(self) -> f64 {
        self.0
    }

    /// Positive infinity (unreachable / zero element).
    #[inline]
    pub const fn infinity() -> Self {
        TropicalWeight(f64::INFINITY)
    }

    /// Whether this weight is infinite (unreachable).
    #[inline]
    pub fn is_infinite(self) -> bool {
        self.0.is_infinite()
    }

    /// Convert a `TokenKind::priority()` value to a tropical weight.
    ///
    /// Higher priority (larger u8) maps to lower weight (better).
    /// Uses `MAX_PRIORITY - priority` where `MAX_PRIORITY = 10`.
    #[inline]
    pub fn from_priority(priority: u8) -> Self {
        TropicalWeight((10.0_f64) - priority as f64)
    }
}

impl Semiring for TropicalWeight {
    #[inline]
    fn zero() -> Self {
        TropicalWeight::infinity()
    }

    #[inline]
    fn one() -> Self {
        TropicalWeight(0.0)
    }

    #[inline]
    fn plus(&self, other: &Self) -> Self {
        TropicalWeight(self.0.min(other.0))
    }

    #[inline]
    fn times(&self, other: &Self) -> Self {
        TropicalWeight(self.0 + other.0)
    }

    #[inline]
    fn is_zero(&self) -> bool {
        self.0.is_infinite() && self.0.is_sign_positive()
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

impl fmt::Debug for TropicalWeight {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.is_zero() {
            write!(f, "TropicalWeight(inf)")
        } else {
            write!(f, "TropicalWeight({:.1})", self.0)
        }
    }
}

impl fmt::Display for TropicalWeight {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.is_zero() {
            write!(f, "inf")
        } else {
            write!(f, "{:.1}", self.0)
        }
    }
}

impl PartialEq for TropicalWeight {
    fn eq(&self, other: &Self) -> bool {
        self.0.total_cmp(&other.0) == Ordering::Equal
    }
}

impl Eq for TropicalWeight {}

impl PartialOrd for TropicalWeight {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for TropicalWeight {
    fn cmp(&self, other: &Self) -> Ordering {
        self.0.total_cmp(&other.0)
    }
}

impl std::hash::Hash for TropicalWeight {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.0.to_bits().hash(state);
    }
}

impl Default for TropicalWeight {
    fn default() -> Self {
        Self::one()
    }
}

impl DetectableZero for TropicalWeight {}

impl IdempotentSemiring for TropicalWeight {}

impl CompleteSemiring for TropicalWeight {}

impl StarSemiring for TropicalWeight {
    /// `star(a) = 0.0` (one) if `a >= 0`, else diverges (returns zero).
    ///
    /// For non-negative weights (PraTTaIL's invariant): repeating a
    /// non-negative-cost path zero times gives cost 0 (the identity).
    /// The infinite sum `min(0, a, 2a, ...)` converges to `0` when `a >= 0`.
    #[inline]
    fn star(&self) -> Self {
        if self.0 >= 0.0 {
            Self::one() // 0.0 — repeating zero times is free
        } else {
            Self::zero() // -∞ diverges; return unreachable
        }
    }
}
