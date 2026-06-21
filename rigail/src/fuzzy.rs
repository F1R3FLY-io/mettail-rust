use super::*;

// ══════════════════════════════════════════════════════════════════════════════
// FuzzyWeight (Possibilistic Semiring)
// ══════════════════════════════════════════════════════════════════════════════

/// Fuzzy/possibilistic semiring `([0,1], max, min, 0, 1)`.
///
/// Confidence/possibility-degree reasoning. Unlike probability (which sums
/// to 1), fuzzy weights express independent "degree of possibility" in `[0, 1]`.
///
/// `times = min` means the plausibility of a multi-step operation is limited
/// by its least plausible step (bottleneck semantics in possibility space).
///
/// - `plus = max`: selects the most possible alternative
/// - `times = min`: bottleneck — multi-step possibility = weakest link
/// - `zero = 0.0`: impossible (identity for max)
/// - `one = 1.0`: fully possible (identity for min)
///
/// **Applications:**
/// - `prediction.rs`: dispatch confidence independent of probability
/// - `recovery.rs`: fuzzy "plausibility" of a recovery strategy
/// - `lint.rs`: true-positive likelihood of a diagnostic
#[derive(Clone, Copy)]
pub struct FuzzyWeight(pub f64);

impl FuzzyWeight {
    /// Create a fuzzy weight from a possibility degree in `[0, 1]`.
    #[inline]
    pub fn new(degree: f64) -> Self {
        debug_assert!(
            (0.0..=1.0).contains(&degree),
            "FuzzyWeight: degree must be in [0, 1], got {degree}"
        );
        FuzzyWeight(degree)
    }

    /// Get the possibility degree.
    #[inline]
    pub const fn degree(self) -> f64 {
        self.0
    }
}

impl Semiring for FuzzyWeight {
    #[inline]
    fn zero() -> Self {
        FuzzyWeight(0.0)
    }

    #[inline]
    fn one() -> Self {
        FuzzyWeight(1.0)
    }

    #[inline]
    fn plus(&self, other: &Self) -> Self {
        FuzzyWeight(self.0.max(other.0))
    }

    #[inline]
    fn times(&self, other: &Self) -> Self {
        FuzzyWeight(self.0.min(other.0))
    }

    #[inline]
    fn is_zero(&self) -> bool {
        self.0 == 0.0
    }

    #[inline]
    fn is_one(&self) -> bool {
        self.0 == 1.0
    }

    fn approx_eq(&self, other: &Self, epsilon: f64) -> bool {
        (self.0 - other.0).abs() <= epsilon
    }
}

impl fmt::Debug for FuzzyWeight {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "FuzzyWeight({:.4})", self.0)
    }
}

impl fmt::Display for FuzzyWeight {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{:.4}", self.0)
    }
}

impl PartialEq for FuzzyWeight {
    fn eq(&self, other: &Self) -> bool {
        self.0.total_cmp(&other.0) == Ordering::Equal
    }
}

impl Eq for FuzzyWeight {}

impl PartialOrd for FuzzyWeight {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

/// Higher degree = better. Reversed ordering so generic shortest-path
/// algorithms select the most possible alternative.
impl Ord for FuzzyWeight {
    fn cmp(&self, other: &Self) -> Ordering {
        other.0.total_cmp(&self.0)
    }
}

impl std::hash::Hash for FuzzyWeight {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.0.to_bits().hash(state);
    }
}

impl Default for FuzzyWeight {
    fn default() -> Self {
        Self::one()
    }
}

impl DetectableZero for FuzzyWeight {}

impl IdempotentSemiring for FuzzyWeight {}

impl CompleteSemiring for FuzzyWeight {}

impl StarSemiring for FuzzyWeight {
    /// `star(a) = 1.0`. Max possibility is always 1 (the empty path has
    /// full possibility): `max(1, a, min(a,a), ...) = 1.0` for any `a`.
    #[inline]
    fn star(&self) -> Self {
        FuzzyWeight(1.0)
    }
}
