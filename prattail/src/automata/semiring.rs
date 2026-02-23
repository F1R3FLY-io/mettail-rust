//! Semiring types for weighted automata.
//!
//! Provides the `Semiring` trait and `TropicalWeight` implementation, adapted
//! from the `lling-llang` WFST library. Only the minimal subset needed for
//! PraTTaIL's weighted lexer pipeline is included here (~100 LOC) rather than
//! depending on the full 95K LOC `lling-llang` crate, preserving the 55s
//! proc-macro build time.
//!
//! ## Tropical Semiring
//!
//! The tropical semiring `(R+ union {+inf}, min, +, +inf, 0.0)` maps naturally
//! to lexer token priority: lower weight = higher priority. The `plus` operation
//! (min) selects the best alternative; `times` (addition) accumulates costs
//! along a path.
//!
//! ## Derived from lling-llang
//!
//! Source: `lling-llang/src/semiring/tropical.rs`
//! License: MIT OR Apache-2.0

use std::cmp::Ordering;
use std::fmt;

// ══════════════════════════════════════════════════════════════════════════════
// Semiring trait
// ══════════════════════════════════════════════════════════════════════════════

/// A semiring `(K, +, *, 0, 1)` where `+` combines parallel paths and `*`
/// sequences path segments.
///
/// Properties required:
/// - `(K, +, 0)` is a commutative monoid
/// - `(K, *, 1)` is a monoid
/// - `*` distributes over `+`
/// - `0 * a = a * 0 = 0` (zero annihilates)
pub trait Semiring: Clone + Copy + fmt::Debug + PartialEq + Send + Sync + 'static {
    /// Additive identity. For tropical: `+inf` (unreachable).
    fn zero() -> Self;
    /// Multiplicative identity. For tropical: `0.0` (zero cost).
    fn one() -> Self;
    /// Semiring addition: combines parallel paths. For tropical: `min(a, b)`.
    fn plus(&self, other: &Self) -> Self;
    /// Semiring multiplication: sequences path segments. For tropical: `a + b`.
    fn times(&self, other: &Self) -> Self;
    /// Whether this is the additive identity.
    fn is_zero(&self) -> bool;
    /// Whether this is the multiplicative identity.
    fn is_one(&self) -> bool;
    /// Approximate equality for floating-point convergence checks.
    fn approx_eq(&self, other: &Self, epsilon: f64) -> bool;
}

// ══════════════════════════════════════════════════════════════════════════════
// TropicalWeight
// ══════════════════════════════════════════════════════════════════════════════

/// Tropical semiring weight: `(R+ union {+inf}, min, +, +inf, 0.0)`.
///
/// - `plus = min`: selects the best (lowest-cost) alternative
/// - `times = +`: accumulates costs along a path
/// - `zero = +inf`: unreachable (identity for min)
/// - `one = 0.0`: zero cost (identity for addition)
///
/// Lower weight = higher priority. Maps directly to PraTTaIL's existing
/// `TokenKind::priority()` system via `weight = MAX_PRIORITY - priority`.
///
/// Implements total ordering via `f64::total_cmp` (NaN-safe).
#[derive(Clone, Copy)]
pub struct TropicalWeight(pub f64);

impl TropicalWeight {
    /// Create a new tropical weight.
    #[inline]
    pub const fn new(value: f64) -> Self {
        TropicalWeight(value)
    }

    /// Get the underlying `f64` value.
    #[inline]
    pub const fn value(self) -> f64 {
        self.0
    }

    /// Positive infinity (unreachable / zero element).
    #[inline]
    pub const fn infinity() -> Self {
        TropicalWeight(f64::INFINITY)
    }

    /// Whether this weight is infinite (unreachable).
    #[inline]
    pub fn is_infinite(self) -> bool {
        self.0.is_infinite()
    }

    /// Convert a `TokenKind::priority()` value to a tropical weight.
    ///
    /// Higher priority (larger u8) maps to lower weight (better).
    /// Uses `MAX_PRIORITY - priority` where `MAX_PRIORITY = 10`.
    #[inline]
    pub fn from_priority(priority: u8) -> Self {
        TropicalWeight((10.0_f64) - priority as f64)
    }
}

impl Semiring for TropicalWeight {
    #[inline]
    fn zero() -> Self {
        TropicalWeight::infinity()
    }

    #[inline]
    fn one() -> Self {
        TropicalWeight(0.0)
    }

    #[inline]
    fn plus(&self, other: &Self) -> Self {
        TropicalWeight(self.0.min(other.0))
    }

    #[inline]
    fn times(&self, other: &Self) -> Self {
        TropicalWeight(self.0 + other.0)
    }

    #[inline]
    fn is_zero(&self) -> bool {
        self.0.is_infinite() && self.0.is_sign_positive()
    }

    #[inline]
    fn is_one(&self) -> bool {
        self.0 == 0.0
    }

    fn approx_eq(&self, other: &Self, epsilon: f64) -> bool {
        if self.is_zero() && other.is_zero() {
            true
        } else if self.is_zero() || other.is_zero() {
            false
        } else {
            (self.0 - other.0).abs() <= epsilon
        }
    }
}

impl fmt::Debug for TropicalWeight {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.is_zero() {
            write!(f, "TropicalWeight(inf)")
        } else {
            write!(f, "TropicalWeight({:.1})", self.0)
        }
    }
}

impl fmt::Display for TropicalWeight {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.is_zero() {
            write!(f, "inf")
        } else {
            write!(f, "{:.1}", self.0)
        }
    }
}

impl PartialEq for TropicalWeight {
    fn eq(&self, other: &Self) -> bool {
        self.0.total_cmp(&other.0) == Ordering::Equal
    }
}

impl Eq for TropicalWeight {}

impl PartialOrd for TropicalWeight {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for TropicalWeight {
    fn cmp(&self, other: &Self) -> Ordering {
        self.0.total_cmp(&other.0)
    }
}

impl std::hash::Hash for TropicalWeight {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.0.to_bits().hash(state);
    }
}

impl Default for TropicalWeight {
    fn default() -> Self {
        Self::one()
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// LogWeight (feature = "wfst-log")
// ══════════════════════════════════════════════════════════════════════════════

/// Log semiring weight: `(R+ union {+inf}, log-sum-exp, +, +inf, 0.0)`.
///
/// Represents negative log probabilities: `w = -ln(p)`.
///
/// - `plus = log-sum-exp`: combines probabilities: `-ln(exp(-a) + exp(-b))`
/// - `times = +`: multiplies probabilities: `-ln(p * q) = -ln(p) + -ln(q)`
/// - `zero = +inf`: probability 0 (identity for log-sum-exp)
/// - `one = 0.0`: probability 1 (identity for multiplication)
///
/// Unlike `TropicalWeight`, `LogWeight` is **not idempotent**: `plus(a, a) != a`
/// because `exp(-a) + exp(-a) = 2*exp(-a)`, so `-ln(2*exp(-a)) = a - ln(2) != a`.
///
/// This is the semiring used for forward-backward scoring, N-best extraction,
/// and weight training.
///
/// ## Numerical Stability
///
/// The `log_sum_exp` helper uses the standard trick: factor out the smaller
/// value to avoid overflow/underflow. For very large differences (`|a-b| > 20`),
/// the smaller term contributes < `exp(-20) ≈ 2e-9` and is safely dropped.
#[cfg(feature = "wfst-log")]
#[derive(Clone, Copy)]
pub struct LogWeight(pub f64);

#[cfg(feature = "wfst-log")]
impl LogWeight {
    /// Create a new log weight from a raw negative-log value.
    #[inline]
    pub const fn new(value: f64) -> Self {
        LogWeight(value)
    }

    /// Get the underlying `f64` value.
    #[inline]
    pub const fn value(self) -> f64 {
        self.0
    }

    /// Create a log weight from a probability `p` in `(0, 1]`.
    ///
    /// `w = -ln(p)`. Panics if `p <= 0`.
    #[inline]
    pub fn from_probability(p: f64) -> Self {
        assert!(p > 0.0, "LogWeight::from_probability: p must be > 0, got {p}");
        LogWeight(-p.ln())
    }

    /// Convert back to a probability: `p = exp(-w)`.
    #[inline]
    pub fn to_probability(self) -> f64 {
        (-self.0).exp()
    }

    /// Numerically stable log-sum-exp: `-ln(exp(-a) + exp(-b))`.
    ///
    /// Uses the identity: `logsumexp(a, b) = min(a, b) - ln(1 + exp(-|a-b|))`.
    /// For `|a-b| > 20`, the correction term is negligible and is dropped.
    #[inline]
    fn log_sum_exp(a: f64, b: f64) -> f64 {
        if a == f64::INFINITY {
            return b;
        }
        if b == f64::INFINITY {
            return a;
        }
        let min_val = a.min(b);
        let diff = (a - b).abs();
        if diff > 20.0 {
            min_val // fast path: correction < 2e-9
        } else {
            min_val - (1.0 + (-diff).exp()).ln()
        }
    }

    /// Positive infinity (probability 0 / zero element).
    #[inline]
    pub const fn infinity() -> Self {
        LogWeight(f64::INFINITY)
    }

    /// Whether this weight is infinite (probability 0).
    #[inline]
    pub fn is_infinite(self) -> bool {
        self.0.is_infinite() && self.0.is_sign_positive()
    }
}

#[cfg(feature = "wfst-log")]
impl Semiring for LogWeight {
    #[inline]
    fn zero() -> Self {
        LogWeight(f64::INFINITY) // p = 0
    }

    #[inline]
    fn one() -> Self {
        LogWeight(0.0) // p = 1
    }

    #[inline]
    fn plus(&self, other: &Self) -> Self {
        LogWeight(Self::log_sum_exp(self.0, other.0))
    }

    #[inline]
    fn times(&self, other: &Self) -> Self {
        LogWeight(self.0 + other.0)
    }

    #[inline]
    fn is_zero(&self) -> bool {
        self.0.is_infinite() && self.0.is_sign_positive()
    }

    #[inline]
    fn is_one(&self) -> bool {
        self.0 == 0.0
    }

    fn approx_eq(&self, other: &Self, epsilon: f64) -> bool {
        if self.is_zero() && other.is_zero() {
            true
        } else if self.is_zero() || other.is_zero() {
            false
        } else {
            (self.0 - other.0).abs() <= epsilon
        }
    }
}

#[cfg(feature = "wfst-log")]
impl fmt::Debug for LogWeight {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.is_zero() {
            write!(f, "LogWeight(inf)")
        } else {
            write!(f, "LogWeight({:.4})", self.0)
        }
    }
}

#[cfg(feature = "wfst-log")]
impl fmt::Display for LogWeight {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.is_zero() {
            write!(f, "inf")
        } else {
            write!(f, "{:.4}", self.0)
        }
    }
}

#[cfg(feature = "wfst-log")]
impl PartialEq for LogWeight {
    fn eq(&self, other: &Self) -> bool {
        self.0.total_cmp(&other.0) == Ordering::Equal
    }
}

#[cfg(feature = "wfst-log")]
impl Eq for LogWeight {}

#[cfg(feature = "wfst-log")]
impl PartialOrd for LogWeight {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

#[cfg(feature = "wfst-log")]
impl Ord for LogWeight {
    fn cmp(&self, other: &Self) -> Ordering {
        self.0.total_cmp(&other.0)
    }
}

#[cfg(feature = "wfst-log")]
impl std::hash::Hash for LogWeight {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.0.to_bits().hash(state);
    }
}

#[cfg(feature = "wfst-log")]
impl Default for LogWeight {
    fn default() -> Self {
        Self::one()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_tropical_zero_is_infinity() {
        let z = TropicalWeight::zero();
        assert!(z.is_zero());
        assert!(z.is_infinite());
        assert_eq!(z.value(), f64::INFINITY);
    }

    #[test]
    fn test_tropical_one_is_zero_cost() {
        let one = TropicalWeight::one();
        assert!(one.is_one());
        assert!(!one.is_zero());
        assert_eq!(one.value(), 0.0);
    }

    #[test]
    fn test_tropical_plus_is_min() {
        let a = TropicalWeight::new(3.0);
        let b = TropicalWeight::new(7.0);
        assert_eq!(a.plus(&b), TropicalWeight::new(3.0));
        assert_eq!(b.plus(&a), TropicalWeight::new(3.0));
    }

    #[test]
    fn test_tropical_times_is_add() {
        let a = TropicalWeight::new(3.0);
        let b = TropicalWeight::new(7.0);
        assert_eq!(a.times(&b), TropicalWeight::new(10.0));
    }

    #[test]
    fn test_tropical_zero_annihilates() {
        let a = TropicalWeight::new(5.0);
        let z = TropicalWeight::zero();
        // 0 * a = a * 0 = 0 (inf + 5.0 = inf)
        assert!(z.times(&a).is_zero());
        assert!(a.times(&z).is_zero());
    }

    #[test]
    fn test_tropical_one_is_identity() {
        let a = TropicalWeight::new(5.0);
        let one = TropicalWeight::one();
        // 1 * a = a * 1 = a (0.0 + 5.0 = 5.0)
        assert_eq!(one.times(&a), a);
        assert_eq!(a.times(&one), a);
    }

    #[test]
    fn test_tropical_zero_is_plus_identity() {
        let a = TropicalWeight::new(5.0);
        let z = TropicalWeight::zero();
        // 0 + a = a + 0 = a (min(inf, 5.0) = 5.0)
        assert_eq!(z.plus(&a), a);
        assert_eq!(a.plus(&z), a);
    }

    #[test]
    fn test_tropical_plus_idempotent() {
        let a = TropicalWeight::new(5.0);
        assert_eq!(a.plus(&a), a);
    }

    #[test]
    fn test_tropical_from_priority() {
        // Higher priority (10) → lower weight (0.0)
        let fixed = TropicalWeight::from_priority(10);
        assert_eq!(fixed, TropicalWeight::new(0.0));

        // Lower priority (1) → higher weight (9.0)
        let ident = TropicalWeight::from_priority(1);
        assert_eq!(ident, TropicalWeight::new(9.0));

        // Fixed beats Ident: min(0.0, 9.0) = 0.0
        assert_eq!(fixed.plus(&ident), fixed);
    }

    #[test]
    fn test_tropical_ordering() {
        let a = TropicalWeight::new(1.0);
        let b = TropicalWeight::new(5.0);
        let z = TropicalWeight::zero();
        assert!(a < b);
        assert!(b < z);
        assert!(a < z);
    }

    #[test]
    fn test_tropical_approx_eq() {
        let a = TropicalWeight::new(1.0);
        let b = TropicalWeight::new(1.0 + 1e-12);
        assert!(a.approx_eq(&b, 1e-10));
        assert!(!a.approx_eq(&b, 1e-15));
    }

    #[test]
    fn test_tropical_hash_consistency() {
        use std::collections::HashSet;
        let mut set = HashSet::new();
        set.insert(TropicalWeight::new(3.0));
        assert!(set.contains(&TropicalWeight::new(3.0)));
        assert!(!set.contains(&TropicalWeight::new(4.0)));
    }

    // ═══════════════════════════════════════════════════════════════════════
    // LogWeight tests (feature = "wfst-log")
    // ═══════════════════════════════════════════════════════════════════════

    #[cfg(feature = "wfst-log")]
    mod log_weight_tests {
        use super::super::*;

        #[test]
        fn test_log_weight_semiring_laws() {
            let a = LogWeight::new(2.0);
            let b = LogWeight::new(3.0);
            let z = LogWeight::zero();
            let one = LogWeight::one();

            // Zero identity: 0 + a = a
            assert!(z.plus(&a).approx_eq(&a, 1e-10));
            assert!(a.plus(&z).approx_eq(&a, 1e-10));

            // One identity: 1 * a = a
            assert!(one.times(&a).approx_eq(&a, 1e-10));
            assert!(a.times(&one).approx_eq(&a, 1e-10));

            // Zero annihilates: 0 * a = 0
            assert!(z.times(&a).is_zero());
            assert!(a.times(&z).is_zero());

            // Commutativity of plus
            assert!(a.plus(&b).approx_eq(&b.plus(&a), 1e-10));

            // Times is commutative for log: a + b = b + a
            assert!(a.times(&b).approx_eq(&b.times(&a), 1e-10));
        }

        #[test]
        fn test_log_weight_probability_roundtrip() {
            let probs = [0.1, 0.25, 0.5, 0.75, 0.9, 1.0];
            for &p in &probs {
                let w = LogWeight::from_probability(p);
                let p_back = w.to_probability();
                assert!((p - p_back).abs() < 1e-12, "roundtrip failed for p={}: got {}", p, p_back);
            }
        }

        #[test]
        fn test_log_weight_non_idempotent() {
            // Key difference from tropical: plus(a, a) != a
            // Because exp(-a) + exp(-a) = 2*exp(-a), so -ln(2*exp(-a)) = a - ln(2)
            let a = LogWeight::new(2.0);
            let result = a.plus(&a);
            let expected = 2.0 - 2.0_f64.ln(); // a - ln(2)
            assert!(
                (result.value() - expected).abs() < 1e-10,
                "plus(a,a) should be a - ln(2), got {} vs {}",
                result.value(),
                expected
            );
            assert_ne!(result, a, "LogWeight must NOT be idempotent");
        }

        #[test]
        fn test_log_weight_numerical_stability() {
            // Very large values: should not produce NaN or unexpected Inf
            let large = LogWeight::new(1000.0);
            let small = LogWeight::new(1.0);

            // log_sum_exp(1000, 1) ≈ 1.0 (the 1000 term is negligible)
            let result = large.plus(&small);
            assert!(
                (result.value() - 1.0).abs() < 1e-6,
                "large + small should ≈ small, got {}",
                result.value()
            );
            assert!(!result.value().is_nan());
            assert!(!result.value().is_infinite());

            // Very small value (near zero weight = high probability)
            let tiny = LogWeight::new(1e-15);
            let normal = LogWeight::new(5.0);
            let r = tiny.plus(&normal);
            assert!(!r.value().is_nan());
            assert!(r.value() < tiny.value()); // result should be less than the smaller input
        }

        #[test]
        fn test_log_sum_exp_large_diff() {
            // When diff > 20, log_sum_exp returns the smaller value (fast path)
            let a = LogWeight::new(1.0);
            let b = LogWeight::new(30.0); // diff = 29 > 20
            let result = a.plus(&b);
            // Should be very close to 1.0 (fast path returns min directly)
            assert!(
                (result.value() - 1.0).abs() < 1e-6,
                "large diff should use fast path, got {}",
                result.value()
            );
        }

        #[test]
        fn test_log_weight_times_is_addition() {
            let a = LogWeight::new(2.0);
            let b = LogWeight::new(3.0);
            assert_eq!(a.times(&b), LogWeight::new(5.0));
        }

        #[test]
        fn test_log_weight_ordering() {
            let a = LogWeight::new(1.0);
            let b = LogWeight::new(5.0);
            let z = LogWeight::zero();
            assert!(a < b);
            assert!(b < z);
        }

        #[test]
        fn test_log_weight_display() {
            let w = LogWeight::new(1.5);
            assert_eq!(format!("{}", w), "1.5000");

            let z = LogWeight::zero();
            assert_eq!(format!("{}", z), "inf");
        }
    }
}
