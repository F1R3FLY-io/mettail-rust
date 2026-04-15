//! Parikh weight semiring: `[u64; D]` component-wise counter vectors.
//!
//! The Parikh image of a word records the number of occurrences of each
//! letter. The Parikh weight semiring generalizes this to D-dimensional
//! counter vectors, useful for tracking resource consumption, transition
//! counts, or symbol frequencies along automaton paths.
//!
//! ## Semiring structure
//!
//! - `⊕` = component-wise max (join in the lattice of counter vectors)
//! - `⊗` = component-wise addition (accumulate counts along a path)
//! - `0` = `[0; D]` (identity for max)
//! - `1` = `[0; D]` (identity for addition)
//!
//! Note: `0 = 1 = [0; D]` is a degenerate case. This semiring is idempotent
//! (`max(a, a) = a`) and the zero element also happens to be the one element.
//! This is valid because `max(0, a) = a` (zero is identity for plus) and
//! `a + 0 = a` (zero is identity for times).
//!
//! ## Applications
//!
//! - **Parikh automata**: track letter counts for semilinear set projection
//! - **Resource analysis**: count channel sends/receives per dimension
//! - **Boundedness checking**: `max` aggregation detects maximum resource usage

use std::fmt;

use mettail_prattail::automata::semiring::Semiring;

/// Parikh weight: a `D`-dimensional vector of `u64` counters.
///
/// The const generic `D` determines the dimensionality at compile time,
/// enabling stack allocation for common cases (D <= 16) and avoiding
/// heap allocation overhead.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct ParikhWeight<const D: usize> {
    /// Component values. `counters[i]` tracks the count for dimension `i`.
    pub counters: [u64; D],
}

impl<const D: usize> ParikhWeight<D> {
    /// Create a Parikh weight from a counter array.
    #[inline]
    pub const fn new(counters: [u64; D]) -> Self {
        ParikhWeight { counters }
    }

    /// Create a unit vector: 1 in dimension `dim`, 0 elsewhere.
    ///
    /// Panics if `dim >= D`.
    #[inline]
    pub fn unit(dim: usize) -> Self {
        assert!(dim < D, "ParikhWeight::unit: dim {} >= D {}", dim, D);
        let mut counters = [0u64; D];
        counters[dim] = 1;
        ParikhWeight { counters }
    }

    /// Create a scaled unit vector: `count` in dimension `dim`, 0 elsewhere.
    ///
    /// Panics if `dim >= D`.
    #[inline]
    pub fn scaled_unit(dim: usize, count: u64) -> Self {
        assert!(dim < D, "ParikhWeight::scaled_unit: dim {} >= D {}", dim, D);
        let mut counters = [0u64; D];
        counters[dim] = count;
        ParikhWeight { counters }
    }

    /// Get the counter value for a specific dimension.
    #[inline]
    pub fn get(&self, dim: usize) -> u64 {
        self.counters[dim]
    }

    /// Sum of all counters (L1 norm).
    #[inline]
    pub fn total(&self) -> u64 {
        let mut sum = 0u64;
        let mut i = 0;
        while i < D {
            sum = sum.saturating_add(self.counters[i]);
            i += 1;
        }
        sum
    }

    /// Maximum counter value (L-infinity norm).
    #[inline]
    pub fn max_component(&self) -> u64 {
        let mut max_val = 0u64;
        let mut i = 0;
        while i < D {
            if self.counters[i] > max_val {
                max_val = self.counters[i];
            }
            i += 1;
        }
        max_val
    }

    /// Check component-wise `<=` (partial order).
    #[inline]
    pub fn leq(&self, other: &Self) -> bool {
        let mut i = 0;
        while i < D {
            if self.counters[i] > other.counters[i] {
                return false;
            }
            i += 1;
        }
        true
    }
}

impl<const D: usize> Semiring for ParikhWeight<D> {
    /// Zero = `[0; D]`: identity for component-wise max.
    #[inline]
    fn zero() -> Self {
        ParikhWeight { counters: [0u64; D] }
    }

    /// One = `[0; D]`: identity for component-wise addition.
    #[inline]
    fn one() -> Self {
        ParikhWeight { counters: [0u64; D] }
    }

    /// Plus = component-wise max.
    #[inline]
    fn plus(&self, other: &Self) -> Self {
        let mut result = [0u64; D];
        let mut i = 0;
        while i < D {
            result[i] = self.counters[i].max(other.counters[i]);
            i += 1;
        }
        ParikhWeight { counters: result }
    }

    /// Times = component-wise addition (saturating).
    #[inline]
    fn times(&self, other: &Self) -> Self {
        let mut result = [0u64; D];
        let mut i = 0;
        while i < D {
            result[i] = self.counters[i].saturating_add(other.counters[i]);
            i += 1;
        }
        ParikhWeight { counters: result }
    }

    /// Zero check: all components are 0.
    #[inline]
    fn is_zero(&self) -> bool {
        let mut i = 0;
        while i < D {
            if self.counters[i] != 0 {
                return false;
            }
            i += 1;
        }
        true
    }

    /// One check: all components are 0 (same as zero for this semiring).
    #[inline]
    fn is_one(&self) -> bool {
        self.is_zero()
    }

    fn approx_eq(&self, other: &Self, _epsilon: f64) -> bool {
        self.counters == other.counters
    }
}

impl<const D: usize> PartialOrd for ParikhWeight<D> {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

/// Lexicographic ordering on counter vectors.
impl<const D: usize> Ord for ParikhWeight<D> {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.counters.cmp(&other.counters)
    }
}

impl<const D: usize> fmt::Display for ParikhWeight<D> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "[")?;
        for (i, c) in self.counters.iter().enumerate() {
            if i > 0 {
                write!(f, ", ")?;
            }
            write!(f, "{}", c)?;
        }
        write!(f, "]")
    }
}

impl<const D: usize> Default for ParikhWeight<D> {
    fn default() -> Self {
        Self::one()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    type P3 = ParikhWeight<3>;

    #[test]
    fn test_zero_identity_for_plus() {
        let a = P3::new([1, 2, 3]);
        let sum = a.plus(&P3::zero());
        assert_eq!(sum, a, "zero is identity for plus (max)");
    }

    #[test]
    fn test_one_identity_for_times() {
        let a = P3::new([1, 2, 3]);
        let prod = a.times(&P3::one());
        assert_eq!(prod, a, "one is identity for times (add)");
    }

    #[test]
    fn test_plus_is_componentwise_max() {
        let a = P3::new([1, 5, 2]);
        let b = P3::new([3, 2, 4]);
        let sum = a.plus(&b);
        assert_eq!(sum, P3::new([3, 5, 4]));
    }

    #[test]
    fn test_times_is_componentwise_add() {
        let a = P3::new([1, 2, 3]);
        let b = P3::new([4, 5, 6]);
        let prod = a.times(&b);
        assert_eq!(prod, P3::new([5, 7, 9]));
    }

    #[test]
    fn test_unit_vector() {
        let u = P3::unit(1);
        assert_eq!(u, P3::new([0, 1, 0]));
    }

    #[test]
    fn test_idempotent() {
        let a = P3::new([3, 7, 1]);
        let sum = a.plus(&a);
        assert_eq!(sum, a, "plus is idempotent: max(a, a) = a");
    }

    #[test]
    fn test_leq() {
        let a = P3::new([1, 2, 3]);
        let b = P3::new([2, 3, 4]);
        assert!(a.leq(&b));
        assert!(!b.leq(&a));
        assert!(a.leq(&a));
    }

    #[test]
    fn test_total_and_max_component() {
        let a = P3::new([1, 5, 3]);
        assert_eq!(a.total(), 9);
        assert_eq!(a.max_component(), 5);
    }

    #[test]
    fn test_times_saturates() {
        let a = P3::new([u64::MAX, 0, 0]);
        let b = P3::new([1, 0, 0]);
        let prod = a.times(&b);
        assert_eq!(prod.counters[0], u64::MAX, "saturating add");
    }
}
