use super::*;

// ══════════════════════════════════════════════════════════════════════════════
// ComplexityWeight (Bottleneck Semiring)
// ══════════════════════════════════════════════════════════════════════════════

/// Bottleneck semiring for parsing complexity measurement.
///
/// **Semiring:** `(ℕ ∪ {∞}, min, max, ∞, 0)`
///
/// - `plus` = min (take least-complex alternative)
/// - `times` = max (bottleneck: path complexity = most complex segment)
/// - `zero` = ∞ (u32::MAX — identity for min)
/// - `one` = 0 (identity for max)
///
/// **Applications:**
/// - Lookahead budget allocation (only extend WFST where complexity warrants)
/// - Backtrack depth bounding (NFA try-all max depth ∝ ComplexityWeight)
/// - Selective application of multi-token lookahead (B1)
///
/// **Interpretation:** The value represents the estimated lookahead depth
/// or parsing effort required for a dispatch path. Lower values indicate
/// simpler, more deterministic paths.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash)]
pub struct ComplexityWeight(u32);

impl ComplexityWeight {
    /// Create a ComplexityWeight from a raw complexity value.
    #[inline]
    pub const fn new(value: u32) -> Self {
        ComplexityWeight(value)
    }

    /// Return the complexity value.
    #[inline]
    pub const fn value(&self) -> u32 {
        self.0
    }

    /// Complexity for a deterministic (unambiguous) dispatch point.
    #[inline]
    pub const fn deterministic() -> Self {
        ComplexityWeight(0)
    }

    /// Complexity for a dispatch point requiring single-token lookahead.
    #[inline]
    pub const fn single_lookahead() -> Self {
        ComplexityWeight(1)
    }

    /// Complexity for a dispatch point requiring multi-token lookahead.
    #[inline]
    pub const fn multi_lookahead(depth: u32) -> Self {
        ComplexityWeight(depth)
    }

    /// Infinite complexity (unreachable path).
    #[inline]
    pub const fn infinite() -> Self {
        ComplexityWeight(u32::MAX)
    }
}

impl Semiring for ComplexityWeight {
    /// Zero = ∞ (identity for min — no reachable path).
    #[inline]
    fn zero() -> Self {
        ComplexityWeight(u32::MAX)
    }

    /// One = 0 (identity for max — zero complexity).
    #[inline]
    fn one() -> Self {
        ComplexityWeight(0)
    }

    /// Plus = min: take the least-complex alternative.
    #[inline]
    fn plus(&self, other: &Self) -> Self {
        ComplexityWeight(self.0.min(other.0))
    }

    /// Times = max: bottleneck complexity is the worst segment.
    #[inline]
    fn times(&self, other: &Self) -> Self {
        ComplexityWeight(self.0.max(other.0))
    }

    #[inline]
    fn is_zero(&self) -> bool {
        self.0 == u32::MAX
    }

    #[inline]
    fn is_one(&self) -> bool {
        self.0 == 0
    }

    fn approx_eq(&self, other: &Self, _epsilon: f64) -> bool {
        self.0 == other.0
    }
}

impl PartialOrd for ComplexityWeight {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

/// Natural ordering: lower complexity = lower (better).
impl Ord for ComplexityWeight {
    fn cmp(&self, other: &Self) -> Ordering {
        self.0.cmp(&other.0)
    }
}

impl fmt::Display for ComplexityWeight {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.0 == u32::MAX {
            write!(f, "∞")
        } else {
            write!(f, "{}", self.0)
        }
    }
}

impl Default for ComplexityWeight {
    fn default() -> Self {
        Self::one()
    }
}

impl DetectableZero for ComplexityWeight {}

impl IdempotentSemiring for ComplexityWeight {}

impl CompleteSemiring for ComplexityWeight {}

impl StarSemiring for ComplexityWeight {
    /// `star(a) = ComplexityWeight(0)` (one). Minimum bottleneck = none
    /// (the empty path has zero complexity).
    #[inline]
    fn star(&self) -> Self {
        Self::one()
    }
}
