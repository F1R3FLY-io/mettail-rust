//! Consensus-safe lexicographic tropical weights.

use crate::{CompleteSemiring, DetectableZero, IdempotentSemiring, Semiring, StarSemiring};

/// Exact min-plus semiring over four deterministic ranking components.
///
/// Unlike `LexicographicWeight`, this type contains no floating-point values.
/// `plus` selects the lexicographically least rank and `times` accumulates
/// components. Parse forests still retain every packing; this semiring orders
/// alternatives and does not authorize beam pruning.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct ExactLexicographicWeight {
    pub recovery: u64,
    pub ambiguity: u64,
    pub preference: u64,
    pub declaration: u64,
}

impl ExactLexicographicWeight {
    pub const INFINITY: u64 = u64::MAX;

    pub const fn from_rank(
        recovery: u64,
        ambiguity: u64,
        preference: u64,
        declaration: u64,
    ) -> Self {
        Self {
            recovery,
            ambiguity,
            preference,
            declaration,
        }
    }

    fn add_component(left: u64, right: u64) -> u64 {
        if left == Self::INFINITY || right == Self::INFINITY {
            Self::INFINITY
        } else {
            left.checked_add(right).unwrap_or(Self::INFINITY)
        }
    }
}

impl Semiring for ExactLexicographicWeight {
    fn zero() -> Self {
        Self::from_rank(Self::INFINITY, Self::INFINITY, Self::INFINITY, Self::INFINITY)
    }

    fn one() -> Self {
        Self::from_rank(0, 0, 0, 0)
    }

    fn plus(&self, other: &Self) -> Self {
        (*self).min(*other)
    }

    fn times(&self, other: &Self) -> Self {
        if self.is_zero() || other.is_zero() {
            return Self::zero();
        }
        Self::from_rank(
            Self::add_component(self.recovery, other.recovery),
            Self::add_component(self.ambiguity, other.ambiguity),
            Self::add_component(self.preference, other.preference),
            Self::add_component(self.declaration, other.declaration),
        )
    }

    fn is_zero(&self) -> bool {
        *self == Self::zero()
    }

    fn is_one(&self) -> bool {
        *self == Self::one()
    }

    fn approx_eq(&self, other: &Self, _epsilon: f64) -> bool {
        self == other
    }
}

impl DetectableZero for ExactLexicographicWeight {}
impl IdempotentSemiring for ExactLexicographicWeight {}
impl CompleteSemiring for ExactLexicographicWeight {}

impl StarSemiring for ExactLexicographicWeight {
    fn star(&self) -> Self {
        Self::one()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn operations_are_exact_and_lexicographic() {
        let preferred = ExactLexicographicWeight::from_rank(0, 1, 2, 9);
        let recovered = ExactLexicographicWeight::from_rank(1, 0, 0, 0);
        assert_eq!(preferred.plus(&recovered), preferred);
        assert_eq!(
            preferred.times(&ExactLexicographicWeight::from_rank(0, 2, 3, 4)),
            ExactLexicographicWeight::from_rank(0, 3, 5, 13)
        );
    }

    #[test]
    fn semiring_identities_hold_without_epsilon() {
        let value = ExactLexicographicWeight::from_rank(3, 4, 5, 6);
        assert_eq!(value.plus(&ExactLexicographicWeight::zero()), value);
        assert_eq!(value.times(&ExactLexicographicWeight::one()), value);
        assert_eq!(ExactLexicographicWeight::one().times(&value), value);
        assert_eq!(
            value.times(&ExactLexicographicWeight::zero()),
            ExactLexicographicWeight::zero()
        );
    }

    #[test]
    fn component_overflow_becomes_infinity_without_wrapping() {
        let high = ExactLexicographicWeight::from_rank(0, u64::MAX - 1, 0, 0);
        let delta = ExactLexicographicWeight::from_rank(0, 2, 0, 0);
        assert_eq!(high.times(&delta), ExactLexicographicWeight::from_rank(0, u64::MAX, 0, 0));
        assert!(!high.times(&delta).is_zero());
    }
}
