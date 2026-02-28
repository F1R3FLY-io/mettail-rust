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

// ══════════════════════════════════════════════════════════════════════════════
// ProductWeight
// ══════════════════════════════════════════════════════════════════════════════

/// Product semiring `(S₁ × S₂)` — computes two metrics simultaneously.
///
/// - `plus`: component-wise plus (selects best in each dimension independently)
/// - `times`: component-wise times (accumulates in each dimension)
/// - `zero`: `(S₁::zero(), S₂::zero())`
/// - `one`: `(S₁::one(), S₂::one())`
///
/// **Applications**:
/// - `ProductWeight<TropicalWeight, CountingWeight>`: best parse + "was it
///   unique?" → **confidence metric** for dispatch decisions
/// - `ProductWeight<TropicalWeight, EditWeight>`: best parse + minimum repair
///   distance → **optimal error recovery**
///
/// Note: The product semiring applies `plus`/`times` component-wise. For
/// lexicographic ordering (where the second component only breaks ties in
/// the first), a separate `LexicographicWeight` would be needed.
#[derive(Clone, Copy, Debug, PartialEq)]
pub struct ProductWeight<S1: Semiring, S2: Semiring> {
    /// First component weight.
    pub left: S1,
    /// Second component weight.
    pub right: S2,
}

impl<S1: Semiring, S2: Semiring> ProductWeight<S1, S2> {
    /// Create a product weight from two components.
    #[inline]
    pub const fn new(left: S1, right: S2) -> Self {
        ProductWeight { left, right }
    }
}

impl<S1: Semiring + Eq + std::hash::Hash, S2: Semiring + Eq + std::hash::Hash> Semiring
    for ProductWeight<S1, S2>
{
    #[inline]
    fn zero() -> Self {
        ProductWeight {
            left: S1::zero(),
            right: S2::zero(),
        }
    }

    #[inline]
    fn one() -> Self {
        ProductWeight {
            left: S1::one(),
            right: S2::one(),
        }
    }

    #[inline]
    fn plus(&self, other: &Self) -> Self {
        ProductWeight {
            left: self.left.plus(&other.left),
            right: self.right.plus(&other.right),
        }
    }

    #[inline]
    fn times(&self, other: &Self) -> Self {
        ProductWeight {
            left: self.left.times(&other.left),
            right: self.right.times(&other.right),
        }
    }

    #[inline]
    fn is_zero(&self) -> bool {
        self.left.is_zero() || self.right.is_zero()
    }

    #[inline]
    fn is_one(&self) -> bool {
        self.left.is_one() && self.right.is_one()
    }

    fn approx_eq(&self, other: &Self, epsilon: f64) -> bool {
        self.left.approx_eq(&other.left, epsilon) && self.right.approx_eq(&other.right, epsilon)
    }
}

impl<S1: Semiring + Eq, S2: Semiring + Eq> Eq for ProductWeight<S1, S2> {}

impl<S1: Semiring + Ord, S2: Semiring + Ord> PartialOrd for ProductWeight<S1, S2> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

/// Lexicographic ordering: compare left component first, then right.
///
/// This means `ProductWeight<TropicalWeight, EditWeight>` will prefer
/// the parse with the best tropical weight; ties are broken by edit distance.
impl<S1: Semiring + Ord, S2: Semiring + Ord> Ord for ProductWeight<S1, S2> {
    fn cmp(&self, other: &Self) -> Ordering {
        self.left.cmp(&other.left).then_with(|| self.right.cmp(&other.right))
    }
}

impl<S1: Semiring + Eq + std::hash::Hash, S2: Semiring + Eq + std::hash::Hash> std::hash::Hash
    for ProductWeight<S1, S2>
{
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.left.hash(state);
        self.right.hash(state);
    }
}

impl<S1: Semiring + fmt::Display, S2: Semiring + fmt::Display> fmt::Display
    for ProductWeight<S1, S2>
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "({}, {})", self.left, self.right)
    }
}

impl<S1: Semiring, S2: Semiring> Default for ProductWeight<S1, S2> {
    fn default() -> Self {
        ProductWeight {
            left: S1::one(),
            right: S2::one(),
        }
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
    // CountingWeight tests
    // ═══════════════════════════════════════════════════════════════════════

    #[test]
    fn test_counting_semiring_laws() {
        let a = CountingWeight::new(3);
        let b = CountingWeight::new(5);
        let z = CountingWeight::zero();
        let one = CountingWeight::one();

        // Zero identity: 0 + a = a
        assert_eq!(z.plus(&a), a);
        assert_eq!(a.plus(&z), a);

        // One identity: 1 * a = a
        assert_eq!(one.times(&a), a);
        assert_eq!(a.times(&one), a);

        // Zero annihilates: 0 * a = 0
        assert!(z.times(&a).is_zero());
        assert!(a.times(&z).is_zero());

        // Plus is commutative: a + b = b + a
        assert_eq!(a.plus(&b), b.plus(&a));

        // Times is commutative: a * b = b * a
        assert_eq!(a.times(&b), b.times(&a));
    }

    #[test]
    fn test_counting_plus_is_add() {
        let a = CountingWeight::new(3);
        let b = CountingWeight::new(5);
        assert_eq!(a.plus(&b), CountingWeight::new(8));
    }

    #[test]
    fn test_counting_times_is_mul() {
        let a = CountingWeight::new(3);
        let b = CountingWeight::new(5);
        assert_eq!(a.times(&b), CountingWeight::new(15));
    }

    #[test]
    fn test_counting_saturating() {
        let big = CountingWeight::new(u64::MAX);
        let two = CountingWeight::new(2);
        // Saturating add
        assert_eq!(big.plus(&two), CountingWeight::new(u64::MAX));
        // Saturating mul
        assert_eq!(big.times(&two), CountingWeight::new(u64::MAX));
    }

    #[test]
    fn test_counting_not_idempotent() {
        let a = CountingWeight::new(3);
        // plus(3, 3) = 6 ≠ 3, not idempotent
        assert_ne!(a.plus(&a), a);
        assert_eq!(a.plus(&a), CountingWeight::new(6));
    }

    #[test]
    fn test_counting_distributivity() {
        // a * (b + c) = a*b + a*c
        let a = CountingWeight::new(2);
        let b = CountingWeight::new(3);
        let c = CountingWeight::new(4);
        let lhs = a.times(&b.plus(&c));
        let rhs = a.times(&b).plus(&a.times(&c));
        assert_eq!(lhs, rhs);
    }

    // ═══════════════════════════════════════════════════════════════════════
    // BooleanWeight tests
    // ═══════════════════════════════════════════════════════════════════════

    #[test]
    fn test_boolean_semiring_laws() {
        let t = BooleanWeight::new(true);
        let f = BooleanWeight::new(false);
        let z = BooleanWeight::zero();
        let one = BooleanWeight::one();

        // Zero = false, One = true
        assert_eq!(z, f);
        assert_eq!(one, t);

        // Zero identity: false ∨ a = a
        assert_eq!(z.plus(&t), t);
        assert_eq!(z.plus(&f), f);

        // One identity: true ∧ a = a
        assert_eq!(one.times(&t), t);
        assert_eq!(one.times(&f), f);

        // Zero annihilates: false ∧ a = false
        assert_eq!(z.times(&t), z);
        assert_eq!(z.times(&f), z);
    }

    #[test]
    fn test_boolean_plus_is_or() {
        let t = BooleanWeight::new(true);
        let f = BooleanWeight::new(false);
        assert_eq!(t.plus(&t), t);
        assert_eq!(t.plus(&f), t);
        assert_eq!(f.plus(&t), t);
        assert_eq!(f.plus(&f), f);
    }

    #[test]
    fn test_boolean_times_is_and() {
        let t = BooleanWeight::new(true);
        let f = BooleanWeight::new(false);
        assert_eq!(t.times(&t), t);
        assert_eq!(t.times(&f), f);
        assert_eq!(f.times(&t), f);
        assert_eq!(f.times(&f), f);
    }

    #[test]
    fn test_boolean_idempotent() {
        let t = BooleanWeight::new(true);
        let f = BooleanWeight::new(false);
        // Plus is idempotent: a ∨ a = a
        assert_eq!(t.plus(&t), t);
        assert_eq!(f.plus(&f), f);
    }

    #[test]
    fn test_boolean_reachability() {
        let reachable = BooleanWeight::new(true);
        let unreachable = BooleanWeight::new(false);
        assert!(reachable.is_reachable());
        assert!(!unreachable.is_reachable());
    }

    // ═══════════════════════════════════════════════════════════════════════
    // EditWeight tests
    // ═══════════════════════════════════════════════════════════════════════

    #[test]
    fn test_edit_semiring_laws() {
        let a = EditWeight::new(3);
        let b = EditWeight::new(5);
        let z = EditWeight::zero();
        let one = EditWeight::one();

        // Zero identity: min(∞, a) = a
        assert_eq!(z.plus(&a), a);
        assert_eq!(a.plus(&z), a);

        // One identity: 0 + a = a
        assert_eq!(one.times(&a), a);
        assert_eq!(a.times(&one), a);

        // Zero annihilates: ∞ + a = ∞ (saturating)
        assert!(z.times(&a).is_zero());
        assert!(a.times(&z).is_zero());

        // Commutativity
        assert_eq!(a.plus(&b), b.plus(&a));
        assert_eq!(a.times(&b), b.times(&a));
    }

    #[test]
    fn test_edit_plus_is_min() {
        let a = EditWeight::new(3);
        let b = EditWeight::new(5);
        assert_eq!(a.plus(&b), EditWeight::new(3));
        assert_eq!(b.plus(&a), EditWeight::new(3));
    }

    #[test]
    fn test_edit_times_is_add() {
        let a = EditWeight::new(3);
        let b = EditWeight::new(5);
        assert_eq!(a.times(&b), EditWeight::new(8));
    }

    #[test]
    fn test_edit_idempotent() {
        let a = EditWeight::new(3);
        // min(3, 3) = 3, idempotent
        assert_eq!(a.plus(&a), a);
    }

    #[test]
    fn test_edit_operation_costs() {
        assert_eq!(EditWeight::skip().distance(), 1);
        assert_eq!(EditWeight::delete().distance(), 1);
        assert_eq!(EditWeight::insert().distance(), 2);
        assert_eq!(EditWeight::substitute().distance(), 2);
    }

    #[test]
    fn test_edit_infinity() {
        assert_eq!(EditWeight::INFINITY, EditWeight::zero());
        assert!(EditWeight::INFINITY.is_zero());
        assert_eq!(EditWeight::INFINITY.distance(), u32::MAX);
    }

    #[test]
    fn test_edit_saturating() {
        let big = EditWeight::new(u32::MAX - 1);
        let two = EditWeight::new(2);
        assert_eq!(big.times(&two), EditWeight::new(u32::MAX));
    }

    #[test]
    fn test_edit_ordering() {
        let a = EditWeight::new(1);
        let b = EditWeight::new(5);
        let z = EditWeight::zero();
        assert!(a < b);
        assert!(b < z);
    }

    // ═══════════════════════════════════════════════════════════════════════
    // ProductWeight tests
    // ═══════════════════════════════════════════════════════════════════════

    #[test]
    fn test_product_semiring_laws() {
        type PW = ProductWeight<TropicalWeight, CountingWeight>;
        let a = PW::new(TropicalWeight::new(2.0), CountingWeight::new(3));
        let b = PW::new(TropicalWeight::new(5.0), CountingWeight::new(2));
        let z = PW::zero();
        let one = PW::one();

        // Zero identity
        assert_eq!(z.plus(&a), a);
        assert_eq!(a.plus(&z), a);

        // One identity
        assert_eq!(one.times(&a), a);
        assert_eq!(a.times(&one), a);

        // Zero annihilates
        assert!(z.times(&a).is_zero());
        assert!(a.times(&z).is_zero());

        // Commutativity of plus
        assert_eq!(a.plus(&b), b.plus(&a));
    }

    #[test]
    fn test_product_tropical_counting() {
        type PW = ProductWeight<TropicalWeight, CountingWeight>;

        let a = PW::new(TropicalWeight::new(2.0), CountingWeight::new(3));
        let b = PW::new(TropicalWeight::new(5.0), CountingWeight::new(2));

        // Plus: component-wise (min, add)
        let sum = a.plus(&b);
        assert_eq!(sum.left, TropicalWeight::new(2.0)); // min(2, 5) = 2
        assert_eq!(sum.right, CountingWeight::new(5)); // 3 + 2 = 5

        // Times: component-wise (add, mul)
        let prod = a.times(&b);
        assert_eq!(prod.left, TropicalWeight::new(7.0)); // 2 + 5 = 7
        assert_eq!(prod.right, CountingWeight::new(6)); // 3 * 2 = 6
    }

    #[test]
    fn test_product_tropical_edit() {
        type PW = ProductWeight<TropicalWeight, EditWeight>;

        let a = PW::new(TropicalWeight::new(1.0), EditWeight::new(2));
        let b = PW::new(TropicalWeight::new(3.0), EditWeight::new(1));

        // Plus: component-wise (min, min)
        let sum = a.plus(&b);
        assert_eq!(sum.left, TropicalWeight::new(1.0)); // min(1, 3) = 1
        assert_eq!(sum.right, EditWeight::new(1)); // min(2, 1) = 1

        // Times: component-wise (add, add)
        let prod = a.times(&b);
        assert_eq!(prod.left, TropicalWeight::new(4.0)); // 1 + 3 = 4
        assert_eq!(prod.right, EditWeight::new(3)); // 2 + 1 = 3
    }

    #[test]
    fn test_product_is_zero() {
        type PW = ProductWeight<TropicalWeight, CountingWeight>;
        // is_zero if either component is zero
        let z_left = PW::new(TropicalWeight::zero(), CountingWeight::new(5));
        assert!(z_left.is_zero());

        let z_right = PW::new(TropicalWeight::new(1.0), CountingWeight::zero());
        assert!(z_right.is_zero());

        let neither = PW::new(TropicalWeight::new(1.0), CountingWeight::new(1));
        assert!(!neither.is_zero());
    }

    #[test]
    fn test_product_is_one() {
        type PW = ProductWeight<TropicalWeight, CountingWeight>;
        let one = PW::one();
        assert!(one.is_one());
        assert_eq!(one.left, TropicalWeight::one());
        assert_eq!(one.right, CountingWeight::one());
    }

    #[test]
    fn test_product_default() {
        type PW = ProductWeight<TropicalWeight, CountingWeight>;
        let d = PW::default();
        assert!(d.is_one());
    }

    #[test]
    fn test_product_approx_eq() {
        type PW = ProductWeight<TropicalWeight, CountingWeight>;
        let a = PW::new(TropicalWeight::new(1.0), CountingWeight::new(3));
        let b = PW::new(TropicalWeight::new(1.0 + 1e-12), CountingWeight::new(3));
        assert!(a.approx_eq(&b, 1e-10));
        assert!(!a.approx_eq(&b, 1e-15));
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
