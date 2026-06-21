use super::*;

// ══════════════════════════════════════════════════════════════════════════════
// TruncationWeight (Bounded Ambiguity Semiring)
// ══════════════════════════════════════════════════════════════════════════════

/// Truncation semiring `({0, ..., K}, max, min(a + b, K))`.
///
/// Bounded ambiguity counting with saturation. Tracks the *maximum* count
/// from any alternative (idempotent `plus = max`) and saturates at `K`.
///
/// - `plus = max`: take the highest count from any alternative
/// - `times = min(a + b, K)`: accumulate counts with saturation
/// - `zero = 0`: no paths (identity for max)
/// - `one = 0`: adding zero doesn't increase count (identity for truncated +)
///
/// **Note:** Unlike CountingWeight (which has `plus = +`, `times = ×`),
/// TruncationWeight has idempotent `plus = max` and additive `times`.
/// This means it tracks the worst-case ambiguity level rather than summing.
///
/// **Applications:**
/// - `prediction.rs`: tiered ambiguity severity (1 = deterministic,
///   2 = binary choice, 3+ = complex, K+ = severe)
/// - More informative than `BooleanWeight` (binary), more compact than
///   `CountingWeight` (64-bit)
///
/// Common values: `K = 4` (four-tier severity), `K = 8` (fine-grained).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct TruncationWeight<const K: u32>(pub u32);

impl<const K: u32> TruncationWeight<K> {
    /// Create a truncation weight, clamping to `[0, K]`.
    #[inline]
    pub const fn new(value: u32) -> Self {
        if value > K {
            TruncationWeight(K)
        } else {
            TruncationWeight(value)
        }
    }

    /// Get the count value.
    #[inline]
    pub const fn count(self) -> u32 {
        self.0
    }

    /// Whether this weight is at the saturation threshold.
    #[inline]
    pub const fn is_saturated(self) -> bool {
        self.0 >= K
    }
}

impl<const K: u32> Semiring for TruncationWeight<K> {
    #[inline]
    fn zero() -> Self {
        TruncationWeight(0)
    }

    #[inline]
    fn one() -> Self {
        TruncationWeight(0)
    }

    #[inline]
    fn plus(&self, other: &Self) -> Self {
        TruncationWeight(self.0.max(other.0))
    }

    #[inline]
    fn times(&self, other: &Self) -> Self {
        TruncationWeight(self.0.saturating_add(other.0).min(K))
    }

    #[inline]
    fn is_zero(&self) -> bool {
        self.0 == 0
    }

    #[inline]
    fn is_one(&self) -> bool {
        self.0 == 0
    }

    fn approx_eq(&self, other: &Self, _epsilon: f64) -> bool {
        self.0 == other.0
    }
}

impl<const K: u32> PartialOrd for TruncationWeight<K> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl<const K: u32> Ord for TruncationWeight<K> {
    fn cmp(&self, other: &Self) -> Ordering {
        self.0.cmp(&other.0)
    }
}

impl<const K: u32> fmt::Display for TruncationWeight<K> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.0 >= K {
            write!(f, "{}+", K)
        } else {
            write!(f, "{}", self.0)
        }
    }
}

impl<const K: u32> Default for TruncationWeight<K> {
    fn default() -> Self {
        Self::one()
    }
}

impl<const K: u32> DetectableZero for TruncationWeight<K> {}

impl<const K: u32> IdempotentSemiring for TruncationWeight<K> {}

impl<const K: u32> CompleteSemiring for TruncationWeight<K> {}
