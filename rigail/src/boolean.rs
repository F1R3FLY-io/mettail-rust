use super::*;

// ══════════════════════════════════════════════════════════════════════════════
// BooleanWeight
// ══════════════════════════════════════════════════════════════════════════════

/// Boolean semiring `({false, true}, ∨, ∧, false, true)`.
///
/// Tests reachability / language emptiness.
///
/// - `plus = ∨` (disjunction): any reachable path makes the state reachable
/// - `times = ∧` (conjunction): both segments must be reachable
/// - `zero = false`: unreachable (identity for ∨)
/// - `one = true`: reachable (identity for ∧)
///
/// **Application**: Dead-rule detection at codegen time. For each grammar rule,
/// project the prediction WFST onto the boolean semiring. Rules where
/// `predict(token).weight == BooleanWeight(false)` for all tokens are
/// unreachable and can be flagged with a compile-time warning.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct BooleanWeight(pub bool);

impl BooleanWeight {
    /// Create a boolean weight.
    #[inline]
    pub const fn new(reachable: bool) -> Self {
        BooleanWeight(reachable)
    }

    /// Whether this weight represents a reachable state.
    #[inline]
    pub const fn is_reachable(self) -> bool {
        self.0
    }
}

impl Semiring for BooleanWeight {
    #[inline]
    fn zero() -> Self {
        BooleanWeight(false)
    }

    #[inline]
    fn one() -> Self {
        BooleanWeight(true)
    }

    #[inline]
    fn plus(&self, other: &Self) -> Self {
        BooleanWeight(self.0 || other.0)
    }

    #[inline]
    fn times(&self, other: &Self) -> Self {
        BooleanWeight(self.0 && other.0)
    }

    #[inline]
    fn is_zero(&self) -> bool {
        !self.0
    }

    #[inline]
    fn is_one(&self) -> bool {
        self.0
    }

    fn approx_eq(&self, other: &Self, _epsilon: f64) -> bool {
        self.0 == other.0
    }
}

impl fmt::Display for BooleanWeight {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", if self.0 { "⊤" } else { "⊥" })
    }
}

impl Default for BooleanWeight {
    fn default() -> Self {
        Self::one()
    }
}

impl DetectableZero for BooleanWeight {}

impl IdempotentSemiring for BooleanWeight {}

impl CompleteSemiring for BooleanWeight {}

impl StarSemiring for BooleanWeight {
    /// `star(a) = true` for all `a`. Reflexive-transitive closure is always
    /// reachable (the empty path exists).
    #[inline]
    fn star(&self) -> Self {
        BooleanWeight(true)
    }
}
