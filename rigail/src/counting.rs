use super::*;

// ══════════════════════════════════════════════════════════════════════════════
// CountingWeight
// ══════════════════════════════════════════════════════════════════════════════

/// Counting semiring `(ℕ, +, ×, 0, 1)`.
///
/// Counts the number of distinct paths/derivations through the automaton.
///
/// - `plus = addition`: sums path counts from parallel alternatives
/// - `times = multiplication`: multiplies segment counts along a path
/// - `zero = 0`: no paths (identity for addition)
/// - `one = 1`: one path (identity for multiplication)
///
/// **Application**: Compose with `TropicalWeight` via `ProductWeight` to get
/// `(best_weight, derivation_count)`. Tokens with `count > 1` are ambiguous.
/// Used for ambiguity detection and confidence metrics at codegen time.
///
/// Uses saturating arithmetic to avoid overflow on pathological grammars.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct CountingWeight(pub u64);

impl CountingWeight {
    /// Create a counting weight with the given path count.
    #[inline]
    pub const fn new(count: u64) -> Self {
        CountingWeight(count)
    }

    /// Get the path count.
    #[inline]
    pub const fn count(self) -> u64 {
        self.0
    }
}

impl Semiring for CountingWeight {
    #[inline]
    fn zero() -> Self {
        CountingWeight(0)
    }

    #[inline]
    fn one() -> Self {
        CountingWeight(1)
    }

    #[inline]
    fn plus(&self, other: &Self) -> Self {
        CountingWeight(self.0.saturating_add(other.0))
    }

    #[inline]
    fn times(&self, other: &Self) -> Self {
        CountingWeight(self.0.saturating_mul(other.0))
    }

    #[inline]
    fn is_zero(&self) -> bool {
        self.0 == 0
    }

    #[inline]
    fn is_one(&self) -> bool {
        self.0 == 1
    }

    fn approx_eq(&self, other: &Self, _epsilon: f64) -> bool {
        self.0 == other.0
    }
}

impl fmt::Display for CountingWeight {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

impl Default for CountingWeight {
    fn default() -> Self {
        Self::one()
    }
}

impl DetectableZero for CountingWeight {}

// CountingWeight is NOT idempotent: plus(3, 3) = 6 ≠ 3
// CountingWeight is NOT complete: infinite sums diverge in general

impl StarSemiring for CountingWeight {
    /// `star(0) = 1` (one path: the empty path).
    /// `star(a) = u64::MAX` (saturated) for `a > 0` — infinite paths.
    #[inline]
    fn star(&self) -> Self {
        if self.0 == 0 {
            Self::one()
        } else {
            CountingWeight(u64::MAX) // infinite paths → saturate
        }
    }
}
