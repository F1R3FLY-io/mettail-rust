use super::*;

// NbestWeight is NOT idempotent (merge can produce different lengths)
// NbestWeight is NOT complete (infinite sums are not well-defined)

// ══════════════════════════════════════════════════════════════════════════════
// ViterbiWeight
// ══════════════════════════════════════════════════════════════════════════════

/// Viterbi semiring `([0,1], max, ·, 0, 1)`.
///
/// Direct probabilistic reasoning in the probability domain `[0, 1]`.
/// While `TropicalWeight` is the log-domain equivalent (via `w = -ln(p)`),
/// `ViterbiWeight` operates directly on probabilities, enabling:
///
/// - Direct probability I/O without log/exp conversions
/// - Recovery confidence scoring ("probability this recovery is correct")
/// - Training with small models where `[0,1]` precision suffices
///
/// **Key difference from LogWeight:** `plus = max` (idempotent, selects
/// most likely) vs. LogWeight's `plus = logsumexp` (non-idempotent, sums).
///
/// - `plus = max`: selects the most probable alternative
/// - `times = *`: multiplies probabilities along a path
/// - `zero = 0.0`: impossible (identity for max)
/// - `one = 1.0`: certain (identity for multiplication)
#[derive(Clone, Copy)]
pub struct ViterbiWeight(pub f64);

impl ViterbiWeight {
    /// Create a Viterbi weight from a probability in `[0, 1]`.
    #[inline]
    pub fn new(probability: f64) -> Self {
        debug_assert!(
            (0.0..=1.0).contains(&probability),
            "ViterbiWeight: probability must be in [0, 1], got {probability}"
        );
        ViterbiWeight(probability)
    }

    /// Get the probability value.
    #[inline]
    pub const fn probability(self) -> f64 {
        self.0
    }

    /// Convert from a `TropicalWeight` (negative log-probability).
    #[inline]
    pub fn from_tropical(w: TropicalWeight) -> Self {
        if w.is_zero() {
            ViterbiWeight(0.0)
        } else {
            ViterbiWeight((-w.value()).exp())
        }
    }

    /// Convert to a `TropicalWeight` (negative log-probability).
    #[inline]
    pub fn to_tropical(self) -> TropicalWeight {
        if self.0 == 0.0 {
            TropicalWeight::infinity()
        } else {
            TropicalWeight(-self.0.ln())
        }
    }
}

impl Semiring for ViterbiWeight {
    #[inline]
    fn zero() -> Self {
        ViterbiWeight(0.0)
    }

    #[inline]
    fn one() -> Self {
        ViterbiWeight(1.0)
    }

    #[inline]
    fn plus(&self, other: &Self) -> Self {
        ViterbiWeight(self.0.max(other.0))
    }

    #[inline]
    fn times(&self, other: &Self) -> Self {
        ViterbiWeight(self.0 * other.0)
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

impl fmt::Debug for ViterbiWeight {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "ViterbiWeight({:.4})", self.0)
    }
}

impl fmt::Display for ViterbiWeight {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{:.4}", self.0)
    }
}

impl PartialEq for ViterbiWeight {
    fn eq(&self, other: &Self) -> bool {
        self.0.total_cmp(&other.0) == Ordering::Equal
    }
}

impl Eq for ViterbiWeight {}

impl PartialOrd for ViterbiWeight {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

/// Higher probability = better (lower in ordering for Viterbi path selection).
/// Reversed from tropical: `Ord` is by *descending* probability so that
/// the `min` in generic algorithms selects the most probable.
impl Ord for ViterbiWeight {
    fn cmp(&self, other: &Self) -> Ordering {
        // Reverse: higher probability = "lower" (better)
        other.0.total_cmp(&self.0)
    }
}

impl std::hash::Hash for ViterbiWeight {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.0.to_bits().hash(state);
    }
}

impl Default for ViterbiWeight {
    fn default() -> Self {
        Self::one()
    }
}

impl DetectableZero for ViterbiWeight {}

impl IdempotentSemiring for ViterbiWeight {}

impl CompleteSemiring for ViterbiWeight {}

impl StarSemiring for ViterbiWeight {
    /// `star(a) = 1.0`. The most probable repeated application is "do nothing"
    /// (probability 1.0), since `max(1.0, p, p², ...) = 1.0` for any `p ∈ [0,1]`.
    #[inline]
    fn star(&self) -> Self {
        ViterbiWeight(1.0)
    }
}
