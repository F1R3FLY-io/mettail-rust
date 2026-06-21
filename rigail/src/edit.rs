use super::*;

// ══════════════════════════════════════════════════════════════════════════════
// EditWeight
// ══════════════════════════════════════════════════════════════════════════════

/// Edit-distance semiring `(ℕ ∪ {∞}, min, +, ∞, 0)`.
///
/// Counts minimum token-level edits needed for error recovery. Isomorphic to
/// tropical over ℕ but semantically distinct — values represent edit operations
/// rather than arbitrary costs.
///
/// - `plus = min`: selects the repair strategy with fewest edits
/// - `times = +`: accumulates edit counts along a repair path
/// - `zero = ∞ (u32::MAX)`: impossible repair (identity for min)
/// - `one = 0`: no edits needed (identity for addition)
///
/// **Application**: Replace fixed `f64` costs in `recovery.rs`. Compose with
/// `ProductWeight<TropicalWeight, EditWeight>` to find the parse that is both
/// highest-priority AND minimum-edit. The existing `find_best_recovery()`
/// becomes a Viterbi shortest-path over the product semiring.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct EditWeight(pub u32);

impl EditWeight {
    /// Infinite edit distance (unreachable / zero element).
    pub const INFINITY: EditWeight = EditWeight(u32::MAX);

    /// Create an edit weight with the given distance.
    #[inline]
    pub const fn new(distance: u32) -> Self {
        EditWeight(distance)
    }

    /// Get the edit distance value.
    #[inline]
    pub const fn distance(self) -> u32 {
        self.0
    }

    /// Cost of skipping one input token.
    #[inline]
    pub const fn skip() -> Self {
        EditWeight(1)
    }

    /// Cost of deleting an unexpected token.
    #[inline]
    pub const fn delete() -> Self {
        EditWeight(1)
    }

    /// Cost of inserting a missing token.
    #[inline]
    pub const fn insert() -> Self {
        EditWeight(2)
    }

    /// Cost of substituting a wrong token.
    #[inline]
    pub const fn substitute() -> Self {
        EditWeight(2)
    }
}

impl Semiring for EditWeight {
    #[inline]
    fn zero() -> Self {
        Self::INFINITY
    }

    #[inline]
    fn one() -> Self {
        EditWeight(0)
    }

    #[inline]
    fn plus(&self, other: &Self) -> Self {
        EditWeight(self.0.min(other.0))
    }

    #[inline]
    fn times(&self, other: &Self) -> Self {
        EditWeight(self.0.saturating_add(other.0))
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

impl PartialOrd for EditWeight {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for EditWeight {
    fn cmp(&self, other: &Self) -> Ordering {
        self.0.cmp(&other.0)
    }
}

impl fmt::Display for EditWeight {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.is_zero() {
            write!(f, "∞")
        } else {
            write!(f, "{}", self.0)
        }
    }
}

impl Default for EditWeight {
    fn default() -> Self {
        Self::one()
    }
}

impl DetectableZero for EditWeight {}

impl IdempotentSemiring for EditWeight {}

impl CompleteSemiring for EditWeight {}

impl StarSemiring for EditWeight {
    /// `star(a) = EditWeight(0)` (one). Zero edits achievable by doing nothing
    /// (the empty path always has zero edit cost).
    #[inline]
    fn star(&self) -> Self {
        Self::one()
    }
}
