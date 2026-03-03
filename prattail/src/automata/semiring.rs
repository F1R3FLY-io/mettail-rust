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

// ══════════════════════════════════════════════════════════════════════════════
// EntropyWeight (Expectation Semiring, feature = "wfst-log")
// ══════════════════════════════════════════════════════════════════════════════

/// Expectation semiring for computing parse distribution entropy.
///
/// Based on Li & Eisner (2009), "First- and Second-Order Expectation Semirings".
///
/// **Semiring:** `(ℝ × ℝ, ⊕, ⊗, (∞, 0), (0, 0))`
///
/// The carrier set is pairs `(w, e)` where:
/// - `w` = total weight in negative log-probability space (like LogWeight)
/// - `e` = expected value accumulated under the distribution
///
/// **Operations:**
/// - `⊕ (plus)`: Combine parallel paths. For weights, `log-sum-exp(w₁, w₂)`.
///   For expectations, weighted mixture: `(p₁·e₁ + p₂·e₂) / (p₁ + p₂)` where
///   `pᵢ = exp(-wᵢ)`, computed in log-space for numerical stability.
/// - `⊗ (times)`: Sequence path segments. Weights add: `w₁ + w₂`.
///   Expectations add: `e₁ + e₂`.
/// - `0̄ = (∞, 0.0)`: No paths (zero probability, zero expectation).
/// - `1̄ = (0.0, 0.0)`: Single path with probability 1, zero expectation.
///
/// **Shannon Entropy Computation:**
/// To compute Shannon entropy H = -Σ pᵢ ln(pᵢ), set each arc's expectation
/// component `e` to the arc's negative log-probability `w`. Then after
/// forward-backward, the total expectation at the final state gives H.
///
/// **Applications:**
/// - Adaptive beam width (wider beam at high-entropy dispatch points)
/// - Grammar design feedback ("category Proc has 2.3 bits entropy at `Ident`")
/// - Training convergence criterion (stop when total entropy stabilizes)
///
/// Feature-gated behind `wfst-log`.
#[cfg(feature = "wfst-log")]
#[derive(Clone, Copy)]
pub struct EntropyWeight {
    /// Total weight in negative log-probability space.
    pub weight: f64,
    /// Accumulated expected value (entropy contribution).
    pub expectation: f64,
}

#[cfg(feature = "wfst-log")]
impl EntropyWeight {
    /// Create an EntropyWeight from weight and expectation components.
    #[inline]
    pub const fn new(weight: f64, expectation: f64) -> Self {
        EntropyWeight { weight, expectation }
    }

    /// Create an EntropyWeight for a single arc with the given weight.
    ///
    /// For Shannon entropy computation, set expectation = weight (the arc's
    /// negative log-probability). This way, after forward-backward, the total
    /// expectation gives H = -Σ pᵢ ln(pᵢ).
    #[inline]
    pub const fn from_arc_weight(weight: f64) -> Self {
        EntropyWeight {
            weight,
            expectation: weight,
        }
    }

    /// Get the weight component.
    #[inline]
    pub const fn weight(&self) -> f64 {
        self.weight
    }

    /// Get the expectation component.
    #[inline]
    pub const fn expectation(&self) -> f64 {
        self.expectation
    }

    /// Compute entropy in bits (divide by ln(2)).
    #[inline]
    pub fn entropy_bits(&self) -> f64 {
        self.expectation / std::f64::consts::LN_2
    }

    /// Numerically stable log-sum-exp: `-ln(exp(-a) + exp(-b))`.
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
            min_val
        } else {
            min_val - (1.0 + (-diff).exp()).ln()
        }
    }
}

#[cfg(feature = "wfst-log")]
impl Semiring for EntropyWeight {
    /// Zero = (∞, 0.0): no paths, zero expectation.
    #[inline]
    fn zero() -> Self {
        EntropyWeight {
            weight: f64::INFINITY,
            expectation: 0.0,
        }
    }

    /// One = (0.0, 0.0): single zero-cost path, zero expectation.
    #[inline]
    fn one() -> Self {
        EntropyWeight {
            weight: 0.0,
            expectation: 0.0,
        }
    }

    /// Plus = combine parallel paths.
    ///
    /// Weight: `log-sum-exp(w₁, w₂)` — combines probabilities.
    /// Expectation: weighted mixture `(p₁·e₁ + p₂·e₂) / (p₁ + p₂)`.
    ///
    /// In log space: if `w₁ ≤ w₂`, then
    ///   `new_e = e₁ + softplus(w₁ - w₂) * (e₂ - e₁) / (1 + exp(w₁ - w₂))`
    /// but more stably computed as:
    ///   `new_e = (p₁·e₁ + p₂·e₂) / (p₁ + p₂)`
    /// where `pᵢ = exp(-wᵢ)`.
    fn plus(&self, other: &Self) -> Self {
        if self.weight == f64::INFINITY {
            return *other;
        }
        if other.weight == f64::INFINITY {
            return *self;
        }

        let new_weight = Self::log_sum_exp(self.weight, other.weight);

        // Compute the weighted mixture of expectations:
        //   new_e = (p_self · e_self + p_other · e_other) / (p_self + p_other)
        // where pᵢ = exp(-wᵢ).
        //
        // For numerical stability, factor out exp(-w_min) from numerator
        // and denominator, where w_min = min(w_self, w_other):
        //   p_self / p_max = exp(-(w_self - w_min))
        //   p_other / p_max = exp(-(w_other - w_min))
        //   new_e = (r_self · e_self + r_other · e_other) / (r_self + r_other)
        //
        // This is symmetric and always commutative.
        let w_min = self.weight.min(other.weight);

        let diff_self = self.weight - w_min; // ≥ 0
        let diff_other = other.weight - w_min; // ≥ 0

        if diff_self > 20.0 {
            // other dominates (self has negligible probability)
            EntropyWeight {
                weight: new_weight,
                expectation: other.expectation,
            }
        } else if diff_other > 20.0 {
            // self dominates (other has negligible probability)
            EntropyWeight {
                weight: new_weight,
                expectation: self.expectation,
            }
        } else {
            let r_self = (-diff_self).exp(); // relative probability of self
            let r_other = (-diff_other).exp(); // relative probability of other
            let denom = r_self + r_other;
            let new_expectation =
                (r_self * self.expectation + r_other * other.expectation) / denom;

            EntropyWeight {
                weight: new_weight,
                expectation: new_expectation,
            }
        }
    }

    /// Times = sequence path segments.
    /// Weight: `w₁ + w₂` (multiply probabilities in log space).
    /// Expectation: `e₁ + e₂` (additive over path segments).
    #[inline]
    fn times(&self, other: &Self) -> Self {
        EntropyWeight {
            weight: self.weight + other.weight,
            expectation: self.expectation + other.expectation,
        }
    }

    #[inline]
    fn is_zero(&self) -> bool {
        self.weight.is_infinite() && self.weight.is_sign_positive()
    }

    #[inline]
    fn is_one(&self) -> bool {
        self.weight == 0.0 && self.expectation == 0.0
    }

    fn approx_eq(&self, other: &Self, epsilon: f64) -> bool {
        if self.is_zero() && other.is_zero() {
            true
        } else if self.is_zero() || other.is_zero() {
            false
        } else {
            (self.weight - other.weight).abs() <= epsilon
                && (self.expectation - other.expectation).abs() <= epsilon
        }
    }
}

#[cfg(feature = "wfst-log")]
impl fmt::Debug for EntropyWeight {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.is_zero() {
            write!(f, "EntropyWeight(inf, 0)")
        } else {
            write!(
                f,
                "EntropyWeight({:.4}, {:.4})",
                self.weight, self.expectation
            )
        }
    }
}

#[cfg(feature = "wfst-log")]
impl fmt::Display for EntropyWeight {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.is_zero() {
            write!(f, "(inf, 0)")
        } else {
            write!(f, "({:.4}, {:.4})", self.weight, self.expectation)
        }
    }
}

#[cfg(feature = "wfst-log")]
impl PartialEq for EntropyWeight {
    fn eq(&self, other: &Self) -> bool {
        self.weight.total_cmp(&other.weight) == Ordering::Equal
            && self.expectation.total_cmp(&other.expectation) == Ordering::Equal
    }
}

#[cfg(feature = "wfst-log")]
impl Eq for EntropyWeight {}

#[cfg(feature = "wfst-log")]
impl PartialOrd for EntropyWeight {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

/// Ordered by weight first (lower = more probable), then expectation.
#[cfg(feature = "wfst-log")]
impl Ord for EntropyWeight {
    fn cmp(&self, other: &Self) -> Ordering {
        self.weight
            .total_cmp(&other.weight)
            .then_with(|| self.expectation.total_cmp(&other.expectation))
    }
}

#[cfg(feature = "wfst-log")]
impl std::hash::Hash for EntropyWeight {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.weight.to_bits().hash(state);
        self.expectation.to_bits().hash(state);
    }
}

#[cfg(feature = "wfst-log")]
impl Default for EntropyWeight {
    fn default() -> Self {
        Self::one()
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// NbestWeight (Viterbi-N-Best Semiring)
// ══════════════════════════════════════════════════════════════════════════════

/// A single entry in the N-best list: (path_id, weight).
///
/// `path_id` identifies which derivation this entry represents.
/// `weight` is the TropicalWeight cost. Lower = better.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct NbestEntry {
    /// Identifier for the derivation path.
    pub path_id: u32,
    /// Cost of this path (tropical weight).
    pub weight: TropicalWeight,
}

impl NbestEntry {
    /// Create a new N-best entry.
    #[inline]
    pub const fn new(path_id: u32, weight: TropicalWeight) -> Self {
        NbestEntry { path_id, weight }
    }
}

/// Viterbi-N-Best semiring with a fixed-size bounded array.
///
/// **Semiring:** `(Sorted[N], merge_nbest, concat_nbest, [], [(0, 0.0)])`
///
/// Tracks the N best alternative parses simultaneously. Each entry is a
/// `(path_id, TropicalWeight)` pair sorted by weight (lowest = best).
///
/// - `⊕ (plus)` = merge two sorted arrays, keep top N by weight
/// - `⊗ (times)` = cross-product of entries (add weights, combine path IDs),
///   keep top N
/// - `0̄` = empty array (no paths)
/// - `1̄` = single entry `(0, 0.0)` (one zero-cost path)
///
/// **Applications:**
/// - Lazy disambiguation: try best; if fails, fall back to 2nd-best
/// - Confidence scoring: large gap between #1 and #2 → commit immediately
/// - Parse forest construction: N-best paths form compact forest
///
/// The const generic `N` controls how many alternatives are tracked.
/// Common values: `N = 4` (parse forest), `N = 2` (confidence gap).
///
/// **Copy compliance:** Uses `[Option<NbestEntry>; N]` with fixed-size array,
/// satisfying the `Copy` bound on `Semiring`. The `Option` wrapper allows
/// sparse arrays (fewer than N entries).
#[derive(Clone, Copy, Debug)]
pub struct NbestWeight<const N: usize> {
    /// Sorted entries: `entries[0]` is best (lowest weight).
    /// `None` values are at the end (the array is packed).
    entries: [Option<NbestEntry>; N],
    /// Number of valid entries (count of `Some` values).
    len: usize,
}

impl<const N: usize> NbestWeight<N> {
    /// Create an empty N-best weight (zero element).
    #[inline]
    pub const fn empty() -> Self {
        NbestWeight {
            entries: [None; N],
            len: 0,
        }
    }

    /// Create an N-best weight with a single entry.
    pub fn singleton(path_id: u32, weight: TropicalWeight) -> Self {
        let mut entries = [None; N];
        entries[0] = Some(NbestEntry::new(path_id, weight));
        NbestWeight { entries, len: 1 }
    }

    /// Create from a slice of entries (sorts and truncates to N).
    pub fn from_entries(mut input: Vec<NbestEntry>) -> Self {
        input.sort_by(|a, b| a.weight.cmp(&b.weight));
        input.dedup_by(|a, b| a.path_id == b.path_id);
        let mut entries = [None; N];
        let len = input.len().min(N);
        for (i, entry) in input.into_iter().take(N).enumerate() {
            entries[i] = Some(entry);
        }
        NbestWeight { entries, len }
    }

    /// Number of valid entries.
    #[inline]
    pub const fn len(&self) -> usize {
        self.len
    }

    /// Whether this is empty (zero element).
    #[inline]
    pub const fn is_empty(&self) -> bool {
        self.len == 0
    }

    /// Get the i-th best entry (0-indexed).
    #[inline]
    pub const fn get(&self, index: usize) -> Option<&NbestEntry> {
        if index < self.len {
            self.entries[index].as_ref()
        } else {
            None
        }
    }

    /// Get the best (lowest-weight) entry.
    #[inline]
    pub const fn best(&self) -> Option<&NbestEntry> {
        self.get(0)
    }

    /// Get the weight gap between the best and second-best entries.
    ///
    /// A large gap indicates high confidence in the best parse.
    /// Returns `f64::INFINITY` if fewer than 2 entries.
    pub fn confidence_gap(&self) -> f64 {
        match (self.get(0), self.get(1)) {
            (Some(best), Some(second)) => second.weight.value() - best.weight.value(),
            _ => f64::INFINITY,
        }
    }

    /// Iterate over valid entries.
    pub fn iter(&self) -> impl Iterator<Item = &NbestEntry> {
        self.entries[..self.len].iter().filter_map(|e| e.as_ref())
    }

    /// Merge two sorted N-best lists, keeping the top N by weight.
    /// Deduplicates by path_id (keeps the lower-weight occurrence).
    fn merge_nbest(&self, other: &Self) -> Self {
        let mut merged: [Option<NbestEntry>; N] = [None; N];
        let mut count = 0;
        let mut i = 0;
        let mut j = 0;

        // Two-pointer merge of sorted arrays
        while count < N && (i < self.len || j < other.len) {
            let take_self = if i >= self.len {
                false
            } else if j >= other.len {
                true
            } else {
                let a = self.entries[i].as_ref().expect("valid entry at i");
                let b = other.entries[j].as_ref().expect("valid entry at j");
                a.weight <= b.weight
            };

            let entry = if take_self {
                let e = self.entries[i].expect("valid entry at i");
                i += 1;
                e
            } else {
                let e = other.entries[j].expect("valid entry at j");
                j += 1;
                e
            };

            // Dedup: skip if this path_id is already in merged
            let is_dup = merged[..count]
                .iter()
                .any(|m| m.map_or(false, |m| m.path_id == entry.path_id));
            if !is_dup {
                merged[count] = Some(entry);
                count += 1;
            }
        }

        NbestWeight {
            entries: merged,
            len: count,
        }
    }

    /// Cross-product of two N-best lists: combine each pair (add weights,
    /// combine path IDs via XOR hash), keep top N results.
    fn concat_nbest(&self, other: &Self) -> Self {
        if self.is_empty() || other.is_empty() {
            return Self::empty();
        }

        // Collect all cross-product entries
        // Capacity: at most self.len * other.len, capped at N
        let mut candidates: Vec<NbestEntry> = Vec::with_capacity(self.len * other.len);
        for a in self.iter() {
            for b in other.iter() {
                let combined_weight = a.weight.times(&b.weight);
                // Combine path IDs: use a hash-like combination
                // Wrapping multiply + XOR gives good distribution
                let combined_id = a.path_id.wrapping_mul(31).wrapping_add(b.path_id);
                candidates.push(NbestEntry::new(combined_id, combined_weight));
            }
        }

        Self::from_entries(candidates)
    }
}

impl<const N: usize> Semiring for NbestWeight<N> {
    /// Zero = empty array (no paths).
    #[inline]
    fn zero() -> Self {
        Self::empty()
    }

    /// One = single entry (path 0, weight 0.0).
    #[inline]
    fn one() -> Self {
        Self::singleton(0, TropicalWeight::one())
    }

    /// Plus = merge two N-best lists, keep top N.
    #[inline]
    fn plus(&self, other: &Self) -> Self {
        self.merge_nbest(other)
    }

    /// Times = cross-product, keep top N.
    #[inline]
    fn times(&self, other: &Self) -> Self {
        self.concat_nbest(other)
    }

    #[inline]
    fn is_zero(&self) -> bool {
        self.is_empty()
    }

    #[inline]
    fn is_one(&self) -> bool {
        self.len == 1
            && self.entries[0].map_or(false, |e| e.path_id == 0 && e.weight.is_one())
    }

    fn approx_eq(&self, other: &Self, epsilon: f64) -> bool {
        if self.len != other.len {
            return false;
        }
        for i in 0..self.len {
            match (self.entries[i], other.entries[i]) {
                (Some(a), Some(b)) => {
                    if a.path_id != b.path_id || !a.weight.approx_eq(&b.weight, epsilon) {
                        return false;
                    }
                }
                (None, None) => {}
                _ => return false,
            }
        }
        true
    }
}

impl<const N: usize> PartialEq for NbestWeight<N> {
    fn eq(&self, other: &Self) -> bool {
        if self.len != other.len {
            return false;
        }
        for i in 0..self.len {
            if self.entries[i] != other.entries[i] {
                return false;
            }
        }
        true
    }
}

impl<const N: usize> Eq for NbestWeight<N> {}

impl<const N: usize> PartialOrd for NbestWeight<N> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

/// Ordered by the best (first) entry's weight. Empty (zero) is worst.
impl<const N: usize> Ord for NbestWeight<N> {
    fn cmp(&self, other: &Self) -> Ordering {
        match (self.best(), other.best()) {
            (None, None) => Ordering::Equal,
            (None, Some(_)) => Ordering::Greater, // empty = worst
            (Some(_), None) => Ordering::Less,
            (Some(a), Some(b)) => a
                .weight
                .cmp(&b.weight)
                .then_with(|| self.len.cmp(&other.len)),
        }
    }
}

impl<const N: usize> std::hash::Hash for NbestWeight<N> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.len.hash(state);
        for i in 0..self.len {
            self.entries[i].hash(state);
        }
    }
}

impl<const N: usize> fmt::Display for NbestWeight<N> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "[")?;
        for i in 0..self.len {
            if i > 0 {
                write!(f, ", ")?;
            }
            if let Some(e) = &self.entries[i] {
                write!(f, "({}:{:.1})", e.path_id, e.weight.value())?;
            }
        }
        write!(f, "]")
    }
}

impl<const N: usize> Default for NbestWeight<N> {
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
    // ContextWeight tests
    // ═══════════════════════════════════════════════════════════════════════

    #[test]
    fn test_context_weight_semiring_laws() {
        let a = ContextWeight::new(0b1010);
        let b = ContextWeight::new(0b1100);
        let z = ContextWeight::zero();
        let one = ContextWeight::one();

        // Zero identity: ∅ ∪ a = a
        assert_eq!(z.plus(&a), a);
        assert_eq!(a.plus(&z), a);

        // One identity: U ∩ a = a
        assert_eq!(one.times(&a), a);
        assert_eq!(a.times(&one), a);

        // Zero annihilates: ∅ ∩ a = ∅
        assert!(z.times(&a).is_zero());
        assert!(a.times(&z).is_zero());

        // Commutativity of plus (union)
        assert_eq!(a.plus(&b), b.plus(&a));

        // Commutativity of times (intersection)
        assert_eq!(a.times(&b), b.times(&a));
    }

    #[test]
    fn test_context_weight_union_intersection() {
        let a = ContextWeight::new(0b1010); // rules 1, 3
        let b = ContextWeight::new(0b1100); // rules 2, 3

        // Union: rules 1, 2, 3
        assert_eq!(a.plus(&b), ContextWeight::new(0b1110));

        // Intersection: rule 3 only
        assert_eq!(a.times(&b), ContextWeight::new(0b1000));
    }

    #[test]
    fn test_context_weight_singleton_and_contains() {
        let s = ContextWeight::singleton(5);
        assert!(s.contains(5));
        assert!(!s.contains(4));
        assert!(!s.contains(6));
        assert_eq!(s.count(), 1);

        let s2 = s.insert(10);
        assert!(s2.contains(5));
        assert!(s2.contains(10));
        assert_eq!(s2.count(), 2);
    }

    #[test]
    fn test_context_weight_idempotent_plus() {
        // Set semiring plus (union) is idempotent: a ∪ a = a
        let a = ContextWeight::new(0b1010);
        assert_eq!(a.plus(&a), a);
    }

    #[test]
    fn test_context_weight_distributivity() {
        // a ∩ (b ∪ c) = (a ∩ b) ∪ (a ∩ c)
        let a = ContextWeight::new(0b1111);
        let b = ContextWeight::new(0b1010);
        let c = ContextWeight::new(0b0101);

        let lhs = a.times(&b.plus(&c));
        let rhs = a.times(&b).plus(&a.times(&c));
        assert_eq!(lhs, rhs);
    }

    #[test]
    fn test_context_weight_ordering() {
        // Fewer labels = lower (better)
        let empty = ContextWeight::zero();
        let one_bit = ContextWeight::singleton(0);
        let two_bits = ContextWeight::new(0b11);
        let all = ContextWeight::one();

        assert!(empty < one_bit);
        assert!(one_bit < two_bits);
        assert!(two_bits < all);
    }

    #[test]
    fn test_context_weight_display() {
        assert_eq!(format!("{}", ContextWeight::zero()), "∅");
        assert_eq!(format!("{}", ContextWeight::one()), "U");
        let s = ContextWeight::new(0b1010);
        assert_eq!(format!("{}", s), "{2b|10}");
    }

    // ═══════════════════════════════════════════════════════════════════════
    // ComplexityWeight tests
    // ═══════════════════════════════════════════════════════════════════════

    #[test]
    fn test_complexity_weight_semiring_laws() {
        let a = ComplexityWeight::new(3);
        let b = ComplexityWeight::new(7);
        let z = ComplexityWeight::zero();
        let one = ComplexityWeight::one();

        // Zero identity: ∞ min a = a
        assert_eq!(z.plus(&a), a);
        assert_eq!(a.plus(&z), a);

        // One identity: 0 max a = a
        assert_eq!(one.times(&a), a);
        assert_eq!(a.times(&one), a);

        // Zero annihilates: check that ∞ max a = ∞
        // (In bottleneck semiring, zero is ∞ which is the max of everything)
        assert!(z.times(&a).is_zero());
        assert!(a.times(&z).is_zero());

        // Commutativity of plus (min)
        assert_eq!(a.plus(&b), b.plus(&a));

        // Commutativity of times (max)
        assert_eq!(a.times(&b), b.times(&a));
    }

    #[test]
    fn test_complexity_weight_min_max() {
        let a = ComplexityWeight::new(3);
        let b = ComplexityWeight::new(7);

        // Plus = min: least-complex alternative
        assert_eq!(a.plus(&b), ComplexityWeight::new(3));

        // Times = max: bottleneck complexity
        assert_eq!(a.times(&b), ComplexityWeight::new(7));
    }

    #[test]
    fn test_complexity_weight_idempotent_plus() {
        // min(a, a) = a — idempotent
        let a = ComplexityWeight::new(5);
        assert_eq!(a.plus(&a), a);
    }

    #[test]
    fn test_complexity_weight_constructors() {
        assert_eq!(ComplexityWeight::deterministic().value(), 0);
        assert_eq!(ComplexityWeight::single_lookahead().value(), 1);
        assert_eq!(ComplexityWeight::multi_lookahead(3).value(), 3);
        assert_eq!(ComplexityWeight::infinite().value(), u32::MAX);

        assert!(ComplexityWeight::infinite().is_zero()); // ∞ is the zero
        assert!(ComplexityWeight::deterministic().is_one()); // 0 is the one
    }

    #[test]
    fn test_complexity_weight_distributivity() {
        // max(a, min(b, c)) = min(max(a, b), max(a, c))
        let a = ComplexityWeight::new(3);
        let b = ComplexityWeight::new(5);
        let c = ComplexityWeight::new(7);

        let lhs = a.times(&b.plus(&c));
        let rhs = a.times(&b).plus(&a.times(&c));
        assert_eq!(lhs, rhs);
    }

    #[test]
    fn test_complexity_weight_ordering() {
        let a = ComplexityWeight::new(2);
        let b = ComplexityWeight::new(5);
        let z = ComplexityWeight::zero(); // ∞

        assert!(a < b);
        assert!(b < z);
    }

    #[test]
    fn test_complexity_weight_display() {
        assert_eq!(format!("{}", ComplexityWeight::new(3)), "3");
        assert_eq!(format!("{}", ComplexityWeight::zero()), "∞");
        assert_eq!(format!("{}", ComplexityWeight::one()), "0");
    }

    #[test]
    fn test_complexity_weight_product_with_tropical() {
        // ProductWeight<TropicalWeight, ComplexityWeight> should work
        type TPC = ProductWeight<TropicalWeight, ComplexityWeight>;
        let a = TPC::new(TropicalWeight::new(1.0), ComplexityWeight::new(3));
        let b = TPC::new(TropicalWeight::new(2.0), ComplexityWeight::new(5));

        // Plus: (min(1,2), min(3,5)) = (1, 3)
        let sum = a.plus(&b);
        assert_eq!(sum.left.value(), 1.0);
        assert_eq!(sum.right.value(), 3);

        // Times: (1+2, max(3,5)) = (3, 5)
        let prod = a.times(&b);
        assert_eq!(prod.left.value(), 3.0);
        assert_eq!(prod.right.value(), 5);
    }

    #[test]
    fn test_context_weight_product_with_tropical() {
        // ProductWeight<TropicalWeight, ContextWeight> should work
        type TPC = ProductWeight<TropicalWeight, ContextWeight>;
        let a = TPC::new(TropicalWeight::new(1.0), ContextWeight::new(0b1010));
        let b = TPC::new(TropicalWeight::new(2.0), ContextWeight::new(0b1100));

        // Plus: (min(1,2), 0b1010 | 0b1100) = (1, 0b1110)
        let sum = a.plus(&b);
        assert_eq!(sum.left.value(), 1.0);
        assert_eq!(sum.right.bits(), 0b1110);

        // Times: (1+2, 0b1010 & 0b1100) = (3, 0b1000)
        let prod = a.times(&b);
        assert_eq!(prod.left.value(), 3.0);
        assert_eq!(prod.right.bits(), 0b1000);
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

        // ═══════════════════════════════════════════════════════════════════
        // EntropyWeight tests
        // ═══════════════════════════════════════════════════════════════════

        #[test]
        fn test_entropy_weight_semiring_laws() {
            let a = EntropyWeight::new(2.0, 1.5);
            let b = EntropyWeight::new(3.0, 2.0);
            let z = EntropyWeight::zero();
            let one = EntropyWeight::one();

            // Zero identity: 0 ⊕ a = a
            assert!(z.plus(&a).approx_eq(&a, 1e-10));
            assert!(a.plus(&z).approx_eq(&a, 1e-10));

            // One identity: 1 ⊗ a = a
            assert!(one.times(&a).approx_eq(&a, 1e-10));
            assert!(a.times(&one).approx_eq(&a, 1e-10));

            // Zero annihilates: 0 ⊗ a = 0
            assert!(z.times(&a).is_zero());
            assert!(a.times(&z).is_zero());
        }

        #[test]
        fn test_entropy_weight_times_is_addition() {
            let a = EntropyWeight::new(2.0, 1.5);
            let b = EntropyWeight::new(3.0, 2.0);
            let prod = a.times(&b);
            assert!((prod.weight - 5.0).abs() < 1e-10);
            assert!((prod.expectation - 3.5).abs() < 1e-10);
        }

        #[test]
        fn test_entropy_weight_plus_equal_weights() {
            // Two paths with equal weight: expectations average
            let a = EntropyWeight::new(1.0, 2.0);
            let b = EntropyWeight::new(1.0, 4.0);
            let sum = a.plus(&b);
            // weight: log_sum_exp(1, 1) = 1 - ln(2) ≈ 0.3069
            let expected_w = 1.0 - 2.0_f64.ln();
            assert!(
                (sum.weight - expected_w).abs() < 1e-10,
                "weight: got {}, expected {}",
                sum.weight,
                expected_w
            );
            // expectation: (p1*2 + p2*4) / (p1+p2), p1=p2, so average = 3.0
            assert!(
                (sum.expectation - 3.0).abs() < 1e-10,
                "expectation: got {}, expected 3.0",
                sum.expectation
            );
        }

        #[test]
        fn test_entropy_weight_plus_unequal_weights() {
            // One path with much higher probability dominates
            let dominant = EntropyWeight::new(0.1, 5.0); // high prob
            let minor = EntropyWeight::new(10.0, 100.0); // low prob
            let sum = dominant.plus(&minor);
            // The dominant path's expectation should dominate
            assert!(
                (sum.expectation - 5.0).abs() < 0.1,
                "dominant expectation should win, got {}",
                sum.expectation
            );
        }

        #[test]
        fn test_entropy_weight_plus_commutativity() {
            let a = EntropyWeight::new(1.0, 3.0);
            let b = EntropyWeight::new(2.0, 5.0);
            let ab = a.plus(&b);
            let ba = b.plus(&a);
            assert!(ab.approx_eq(&ba, 1e-10), "plus not commutative: {:?} vs {:?}", ab, ba);
        }

        #[test]
        fn test_entropy_weight_from_arc_weight() {
            let e = EntropyWeight::from_arc_weight(2.5);
            assert_eq!(e.weight, 2.5);
            assert_eq!(e.expectation, 2.5);
        }

        #[test]
        fn test_entropy_weight_entropy_bits() {
            // If expectation = ln(4) nats, then bits = ln(4)/ln(2) = 2.0
            let e = EntropyWeight::new(0.0, 4.0_f64.ln());
            assert!(
                (e.entropy_bits() - 2.0).abs() < 1e-10,
                "entropy bits: got {}, expected 2.0",
                e.entropy_bits()
            );
        }

        #[test]
        fn test_entropy_weight_plus_large_diff() {
            // Very large weight difference: dominant path takes over
            let a = EntropyWeight::new(0.1, 1.0);
            let b = EntropyWeight::new(100.0, 999.0);
            let result = a.plus(&b);
            // a dominates (much lower weight = much higher prob)
            assert!(
                (result.expectation - 1.0).abs() < 1e-6,
                "large diff: got {}, expected ~1.0",
                result.expectation
            );
        }

        #[test]
        fn test_entropy_weight_distributivity_approx() {
            // a ⊗ (b ⊕ c) ≈ (a ⊗ b) ⊕ (a ⊗ c)
            // Note: for the expectation semiring, distributivity holds exactly
            let a = EntropyWeight::new(1.0, 0.5);
            let b = EntropyWeight::new(2.0, 1.0);
            let c = EntropyWeight::new(3.0, 1.5);

            let lhs = a.times(&b.plus(&c));
            let rhs = a.times(&b).plus(&a.times(&c));
            assert!(
                lhs.approx_eq(&rhs, 1e-8),
                "distributivity failed: {:?} vs {:?}",
                lhs,
                rhs
            );
        }

        #[test]
        fn test_entropy_weight_ordering() {
            let a = EntropyWeight::new(1.0, 0.5);
            let b = EntropyWeight::new(5.0, 0.5);
            let z = EntropyWeight::zero();
            assert!(a < b); // lower weight = better
            assert!(b < z); // zero (inf) = worst
        }

        #[test]
        fn test_entropy_weight_display() {
            let e = EntropyWeight::new(1.5, 2.3);
            assert_eq!(format!("{}", e), "(1.5000, 2.3000)");
            let z = EntropyWeight::zero();
            assert_eq!(format!("{}", z), "(inf, 0)");
        }

        #[test]
        fn test_entropy_weight_hash() {
            use std::collections::HashSet;
            let mut set = HashSet::new();
            set.insert(EntropyWeight::new(1.0, 2.0));
            assert!(set.contains(&EntropyWeight::new(1.0, 2.0)));
            assert!(!set.contains(&EntropyWeight::new(1.0, 3.0)));
        }

        #[test]
        fn test_entropy_weight_product_with_tropical() {
            // ProductWeight<TropicalWeight, EntropyWeight>
            type TPE = ProductWeight<TropicalWeight, EntropyWeight>;
            let a = TPE::new(TropicalWeight::new(1.0), EntropyWeight::new(2.0, 0.5));
            let b = TPE::new(TropicalWeight::new(3.0), EntropyWeight::new(1.0, 1.0));

            // Plus: (min(1,3), entropy_plus)
            let sum = a.plus(&b);
            assert_eq!(sum.left, TropicalWeight::new(1.0));

            // Times: (1+3, (2+1, 0.5+1.0)) = (4, (3, 1.5))
            let prod = a.times(&b);
            assert_eq!(prod.left, TropicalWeight::new(4.0));
            assert!((prod.right.weight - 3.0).abs() < 1e-10);
            assert!((prod.right.expectation - 1.5).abs() < 1e-10);
        }
    }

    // ═══════════════════════════════════════════════════════════════════════
    // NbestWeight tests
    // ═══════════════════════════════════════════════════════════════════════

    #[test]
    fn test_nbest_semiring_laws() {
        type NB = NbestWeight<4>;
        let a = NB::singleton(1, TropicalWeight::new(2.0));
        let b = NB::singleton(2, TropicalWeight::new(5.0));
        let z = NB::zero();
        let one = NB::one();

        // Zero identity: 0 ⊕ a = a
        assert_eq!(z.plus(&a), a);
        assert_eq!(a.plus(&z), a);

        // Plus commutativity (same result regardless of order)
        let ab = a.plus(&b);
        let ba = b.plus(&a);
        assert_eq!(ab.len(), ba.len());

        // One identity: 1 ⊗ a should produce a valid result
        let prod = one.times(&a);
        assert_eq!(prod.len(), 1);
        assert_eq!(prod.best().expect("has best").weight, TropicalWeight::new(2.0));

        // Zero annihilates: 0 ⊗ a = 0
        assert!(z.times(&a).is_zero());
        assert!(a.times(&z).is_zero());
    }

    #[test]
    fn test_nbest_merge_keeps_top_n() {
        type NB = NbestWeight<3>;
        let mut a = NB::singleton(1, TropicalWeight::new(1.0));
        a = a.plus(&NB::singleton(2, TropicalWeight::new(2.0)));
        a = a.plus(&NB::singleton(3, TropicalWeight::new(3.0)));
        assert_eq!(a.len(), 3);

        // Adding a 4th should keep only top 3
        let b = NB::singleton(4, TropicalWeight::new(0.5));
        let merged = a.plus(&b);
        assert_eq!(merged.len(), 3);
        // Best should be path 4 (weight 0.5)
        assert_eq!(merged.best().expect("has best").path_id, 4);
        assert_eq!(
            merged.best().expect("has best").weight,
            TropicalWeight::new(0.5)
        );
    }

    #[test]
    fn test_nbest_merge_deduplicates() {
        type NB = NbestWeight<4>;
        let a = NB::singleton(1, TropicalWeight::new(2.0));
        let b = NB::singleton(1, TropicalWeight::new(5.0)); // same path_id, worse weight

        let merged = a.plus(&b);
        assert_eq!(merged.len(), 1);
        // Should keep the better (lower) weight
        assert_eq!(
            merged.best().expect("has best").weight,
            TropicalWeight::new(2.0)
        );
    }

    #[test]
    fn test_nbest_cross_product() {
        type NB = NbestWeight<4>;
        let a = NB::singleton(1, TropicalWeight::new(1.0));
        let b = NB::singleton(2, TropicalWeight::new(3.0));

        let prod = a.times(&b);
        assert_eq!(prod.len(), 1);
        assert_eq!(
            prod.best().expect("has best").weight,
            TropicalWeight::new(4.0)
        ); // 1 + 3 = 4
    }

    #[test]
    fn test_nbest_cross_product_multi() {
        type NB = NbestWeight<4>;
        let mut a = NB::singleton(1, TropicalWeight::new(1.0));
        a = a.plus(&NB::singleton(2, TropicalWeight::new(2.0)));

        let mut b = NB::singleton(10, TropicalWeight::new(0.5));
        b = b.plus(&NB::singleton(20, TropicalWeight::new(1.5)));

        let prod = a.times(&b);
        // 2x2 cross product = up to 4 entries
        assert!(prod.len() <= 4);
        assert!(prod.len() >= 2);
        // Best should be path combining (1, 10) with weight 1.0 + 0.5 = 1.5
        assert_eq!(
            prod.best().expect("has best").weight,
            TropicalWeight::new(1.5)
        );
    }

    #[test]
    fn test_nbest_empty_operations() {
        type NB = NbestWeight<4>;
        let z = NB::zero();
        assert!(z.is_zero());
        assert!(z.is_empty());
        assert_eq!(z.len(), 0);
        assert!(z.best().is_none());
    }

    #[test]
    fn test_nbest_one() {
        type NB = NbestWeight<4>;
        let one = NB::one();
        assert!(one.is_one());
        assert_eq!(one.len(), 1);
        assert_eq!(one.best().expect("has best").path_id, 0);
        assert_eq!(
            one.best().expect("has best").weight,
            TropicalWeight::one()
        );
    }

    #[test]
    fn test_nbest_confidence_gap() {
        type NB = NbestWeight<4>;
        let mut w = NB::singleton(1, TropicalWeight::new(1.0));
        w = w.plus(&NB::singleton(2, TropicalWeight::new(5.0)));
        // Gap = 5.0 - 1.0 = 4.0
        assert!((w.confidence_gap() - 4.0).abs() < 1e-10);

        // Single entry: gap = infinity
        let single = NB::singleton(1, TropicalWeight::new(1.0));
        assert!(single.confidence_gap().is_infinite());

        // Empty: gap = infinity
        let empty = NB::zero();
        assert!(empty.confidence_gap().is_infinite());
    }

    #[test]
    fn test_nbest_ordering() {
        type NB = NbestWeight<4>;
        let a = NB::singleton(1, TropicalWeight::new(1.0)); // best weight 1.0
        let b = NB::singleton(2, TropicalWeight::new(5.0)); // best weight 5.0
        let z = NB::zero(); // empty = worst

        assert!(a < b); // lower best weight = better
        assert!(b < z); // anything better than empty
    }

    #[test]
    fn test_nbest_display() {
        type NB = NbestWeight<4>;
        let z = NB::zero();
        assert_eq!(format!("{}", z), "[]");

        let one = NB::one();
        assert_eq!(format!("{}", one), "[(0:0.0)]");

        let mut w = NB::singleton(1, TropicalWeight::new(2.5));
        w = w.plus(&NB::singleton(3, TropicalWeight::new(4.0)));
        assert_eq!(format!("{}", w), "[(1:2.5), (3:4.0)]");
    }

    #[test]
    fn test_nbest_hash() {
        use std::collections::HashSet;
        type NB = NbestWeight<4>;
        let mut set = HashSet::new();
        set.insert(NB::singleton(1, TropicalWeight::new(2.0)));
        assert!(set.contains(&NB::singleton(1, TropicalWeight::new(2.0))));
        assert!(!set.contains(&NB::singleton(2, TropicalWeight::new(2.0))));
    }

    #[test]
    fn test_nbest_from_entries() {
        type NB = NbestWeight<3>;
        let entries = vec![
            NbestEntry::new(3, TropicalWeight::new(5.0)),
            NbestEntry::new(1, TropicalWeight::new(1.0)),
            NbestEntry::new(2, TropicalWeight::new(3.0)),
            NbestEntry::new(4, TropicalWeight::new(0.5)),
        ];
        let w = NB::from_entries(entries);
        assert_eq!(w.len(), 3); // truncated to N=3
        assert_eq!(w.best().expect("has best").path_id, 4); // lowest weight
        assert_eq!(w.get(1).expect("has 2nd").path_id, 1);
        assert_eq!(w.get(2).expect("has 3rd").path_id, 2);
    }

    #[test]
    fn test_nbest_iter() {
        type NB = NbestWeight<4>;
        let mut w = NB::singleton(1, TropicalWeight::new(1.0));
        w = w.plus(&NB::singleton(2, TropicalWeight::new(3.0)));
        w = w.plus(&NB::singleton(3, TropicalWeight::new(5.0)));

        let ids: Vec<u32> = w.iter().map(|e| e.path_id).collect();
        assert_eq!(ids.len(), 3);
        assert_eq!(ids[0], 1); // best first
    }

    #[test]
    fn test_nbest_n2_confidence() {
        // N=2 specialization for confidence gap use case
        type NB2 = NbestWeight<2>;
        let mut w = NB2::singleton(1, TropicalWeight::new(0.5));
        w = w.plus(&NB2::singleton(2, TropicalWeight::new(3.0)));
        w = w.plus(&NB2::singleton(3, TropicalWeight::new(1.0)));

        // Should keep paths 1 (0.5) and 3 (1.0)
        assert_eq!(w.len(), 2);
        assert_eq!(w.best().expect("has best").path_id, 1);
        assert!((w.confidence_gap() - 0.5).abs() < 1e-10);
    }

    #[test]
    fn test_nbest_approx_eq() {
        type NB = NbestWeight<4>;
        let a = NB::singleton(1, TropicalWeight::new(1.0));
        let b = NB::singleton(1, TropicalWeight::new(1.0 + 1e-12));
        assert!(a.approx_eq(&b, 1e-10));
        assert!(!a.approx_eq(&b, 1e-15));
    }
}
