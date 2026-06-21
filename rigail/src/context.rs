use super::*;

// ══════════════════════════════════════════════════════════════════════════════
// ContextWeight (Set Semiring)
// ══════════════════════════════════════════════════════════════════════════════

/// Set semiring over rule labels using a 128-bit bitset.
///
/// **Semiring:** `(𝒫(Labels), ∪, ∩, ∅, U)`
///
/// - `plus` = union (any contributing rule from either path)
/// - `times` = intersection (rules common to both sequential segments)
/// - `zero` = ∅ (no rules reachable)
/// - `one` = U (all rules reachable — universal set)
///
/// **Applications:**
/// - Follow-set tightening (more precise sync token selection)
/// - Ambiguity diagnosis ("rules PInput and POutput both match `Ident`")
/// - Per-token NFA spillover decisions (only where |ContextWeight| > 1)
///
/// **Capacity:** Up to 128 distinct rule labels (sufficient for most grammars).
/// The bitset representation is `Copy` and requires no allocation.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash)]
pub struct ContextWeight(u128);

impl ContextWeight {
    /// Create a ContextWeight from a raw bitset.
    #[inline]
    pub const fn new(bits: u128) -> Self {
        ContextWeight(bits)
    }

    /// Create a ContextWeight with a single rule label set.
    #[inline]
    pub const fn singleton(label_id: u8) -> Self {
        assert!(label_id < 128, "label_id must be < 128");
        ContextWeight(1u128 << label_id)
    }

    /// Return the raw bitset.
    #[inline]
    pub const fn bits(&self) -> u128 {
        self.0
    }

    /// Count the number of set bits (contributing rules).
    #[inline]
    pub const fn count(&self) -> u32 {
        self.0.count_ones()
    }

    /// Check if a specific label ID is in the set.
    #[inline]
    pub const fn contains(&self, label_id: u8) -> bool {
        (self.0 >> label_id) & 1 == 1
    }

    /// Insert a label ID into the set.
    #[inline]
    pub const fn insert(self, label_id: u8) -> Self {
        ContextWeight(self.0 | (1u128 << label_id))
    }
}

impl Semiring for ContextWeight {
    /// Zero = ∅ (empty set — no rules reachable).
    #[inline]
    fn zero() -> Self {
        ContextWeight(0)
    }

    /// One = U (universal set — all 128 bits set).
    #[inline]
    fn one() -> Self {
        ContextWeight(u128::MAX)
    }

    /// Plus = union: any rule from either alternative is contributing.
    #[inline]
    fn plus(&self, other: &Self) -> Self {
        ContextWeight(self.0 | other.0)
    }

    /// Times = intersection: only rules common to both segments contribute.
    #[inline]
    fn times(&self, other: &Self) -> Self {
        ContextWeight(self.0 & other.0)
    }

    #[inline]
    fn is_zero(&self) -> bool {
        self.0 == 0
    }

    #[inline]
    fn is_one(&self) -> bool {
        self.0 == u128::MAX
    }

    fn approx_eq(&self, other: &Self, _epsilon: f64) -> bool {
        self.0 == other.0
    }
}

impl PartialOrd for ContextWeight {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

/// Ordered by set size (fewer labels = lower weight), then by raw bits for
/// deterministic tiebreaking.
impl Ord for ContextWeight {
    fn cmp(&self, other: &Self) -> Ordering {
        self.0
            .count_ones()
            .cmp(&other.0.count_ones())
            .then_with(|| self.0.cmp(&other.0))
    }
}

impl fmt::Display for ContextWeight {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.is_zero() {
            write!(f, "∅")
        } else if self.is_one() {
            write!(f, "U")
        } else {
            write!(f, "{{{}b|{}}}", self.0.count_ones(), self.0)
        }
    }
}

impl Default for ContextWeight {
    fn default() -> Self {
        Self::one()
    }
}

impl DetectableZero for ContextWeight {}

impl IdempotentSemiring for ContextWeight {}

impl CompleteSemiring for ContextWeight {}

impl StarSemiring for ContextWeight {
    /// `star(a) = U` (universal set). The reflexive-transitive closure of any
    /// context set includes the universal context.
    #[inline]
    fn star(&self) -> Self {
        Self::one() // U — all rules reachable
    }
}
