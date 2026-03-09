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
// Trait hierarchy extensions
// ══════════════════════════════════════════════════════════════════════════════

/// Marker trait: this semiring's `is_zero()` is O(1) and reliable.
///
/// All PraTTaIL semirings satisfy this — the trait exists as a bound for
/// algorithms that require efficient zero-weight pruning (e.g., dead-state
/// elimination, sparse matrix operations).
pub trait DetectableZero: Semiring {}

/// Marker trait: `a ⊕ a = a` for all `a` (idempotent addition).
///
/// Guarantees fixed-point convergence in iterative algorithms (e.g.,
/// shortest-path relaxation, forward-backward scoring). Non-idempotent
/// semirings like `CountingWeight` and `LogWeight` require explicit
/// convergence criteria.
pub trait IdempotentSemiring: Semiring {}

/// Marker trait: infinite sums `Σ_{i∈I} aᵢ` are well-defined.
///
/// Required for well-defined semantics of `StarSemiring::star()` and for
/// forward-backward algorithms over cyclic grammars. All idempotent
/// semirings are complete (idempotent ⊕ guarantees convergence).
pub trait CompleteSemiring: Semiring {}

/// Star semiring: Kleene closure `a* = 1 ⊕ a ⊕ a² ⊕ ...`
///
/// Enables transitive closure computation over any semiring. Key applications:
/// - **Reachability** (`BooleanWeight`): reflexive-transitive closure
/// - **All-pairs shortest paths** (`TropicalWeight`): Floyd-Warshall
/// - **Longest paths** (`ArcticWeight`): critical-path analysis
/// - **Path counting** (`CountingWeight`): total derivation count
///
/// Every complete star semiring is Conway, satisfying:
/// - Sum-star: `(a ⊕ b)* = (a* ⊗ b)* ⊗ a*`
/// - Product-star: `(a ⊗ b)* = 1 ⊕ a ⊗ (b ⊗ a)* ⊗ b`
pub trait StarSemiring: Semiring {
    /// Kleene star: `a* = 1 ⊕ a ⊕ a² ⊕ ...` (infinite sum of powers).
    fn star(&self) -> Self;

    /// Kleene plus: `a⁺ = a ⊗ a*` (star without the identity term).
    fn plus_star(&self) -> Self {
        self.times(&self.star())
    }
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

impl DetectableZero for TropicalWeight {}
impl IdempotentSemiring for TropicalWeight {}
impl CompleteSemiring for TropicalWeight {}

impl StarSemiring for TropicalWeight {
    /// `star(a) = 0.0` (one) if `a >= 0`, else diverges (returns zero).
    ///
    /// For non-negative weights (PraTTaIL's invariant): repeating a
    /// non-negative-cost path zero times gives cost 0 (the identity).
    /// The infinite sum `min(0, a, 2a, ...)` converges to `0` when `a >= 0`.
    #[inline]
    fn star(&self) -> Self {
        if self.0 >= 0.0 {
            Self::one() // 0.0 — repeating zero times is free
        } else {
            Self::zero() // -∞ diverges; return unreachable
        }
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

impl<S1: DetectableZero, S2: DetectableZero> DetectableZero for ProductWeight<S1, S2>
where ProductWeight<S1, S2>: Semiring {}

impl<S1: IdempotentSemiring, S2: IdempotentSemiring> IdempotentSemiring for ProductWeight<S1, S2>
where ProductWeight<S1, S2>: Semiring {}

impl<S1: CompleteSemiring, S2: CompleteSemiring> CompleteSemiring for ProductWeight<S1, S2>
where ProductWeight<S1, S2>: Semiring {}

impl<S1: StarSemiring + Eq + std::hash::Hash, S2: StarSemiring + Eq + std::hash::Hash> StarSemiring
    for ProductWeight<S1, S2>
{
    /// Component-wise star: `(a, b)* = (a*, b*)`.
    #[inline]
    fn star(&self) -> Self {
        ProductWeight {
            left: self.left.star(),
            right: self.right.star(),
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

#[cfg(feature = "wfst-log")]
impl DetectableZero for LogWeight {}
// LogWeight is NOT idempotent: plus(a, a) = a - ln(2) ≠ a
#[cfg(feature = "wfst-log")]
impl CompleteSemiring for LogWeight {}

#[cfg(feature = "wfst-log")]
impl StarSemiring for LogWeight {
    /// `star(a) = -ln(1 / (1 - exp(-a)))` for `a > 0`.
    ///
    /// In probability space: `p* = 1/(1-p)` (geometric series sum).
    /// In negative-log space: `star(a) = -ln(1/(1 - exp(-a)))`.
    /// For `a = 0` (p = 1): diverges — return zero (unreachable).
    /// For `a = +∞` (p = 0): `star(∞) = 0.0` (one) — empty path.
    fn star(&self) -> Self {
        if self.is_zero() {
            return Self::one(); // p = 0 → 1/(1-0) = 1 → -ln(1) = 0
        }
        if self.0 == 0.0 {
            return Self::zero(); // p = 1 → 1/(1-1) diverges
        }
        let p = (-self.0).exp();
        if p >= 1.0 {
            return Self::zero(); // diverges
        }
        LogWeight(-(1.0 / (1.0 - p)).ln())
    }
}

#[cfg(feature = "wfst-log")]
impl DetectableZero for EntropyWeight {}
// EntropyWeight is NOT idempotent (inherits from LogWeight)
#[cfg(feature = "wfst-log")]
impl CompleteSemiring for EntropyWeight {}

#[cfg(feature = "wfst-log")]
impl StarSemiring for EntropyWeight {
    /// Star for the expectation semiring. The weight component uses the
    /// LogWeight star formula. The expectation component is derived from
    /// the fixed-point equation `star(a) = 1 ⊕ a ⊗ star(a)`:
    ///
    /// Solving for `e_star`: `e_star = p · s · e` where `p = exp(-w)`,
    /// `s = 1/(1-p)`, giving `e_star = exp(-(w + star_w)) · e`.
    fn star(&self) -> Self {
        if self.weight == f64::INFINITY {
            // p = 0 → star = 1, expectation = 0
            return Self::one();
        }
        if self.weight == 0.0 {
            // p = 1 → diverges
            return Self::zero();
        }
        let p = (-self.weight).exp();
        if p >= 1.0 {
            return Self::zero();
        }
        let s = 1.0 / (1.0 - p); // geometric sum in probability space
        let star_weight = -s.ln();
        // From fixed-point: e_star = exp(-(w + star_w)) × e = p × s × e
        let star_expectation = p * s * self.expectation;
        EntropyWeight {
            weight: star_weight,
            expectation: star_expectation,
        }
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

impl<const N: usize> DetectableZero for NbestWeight<N> {}
// NbestWeight is NOT idempotent (merge can produce different lengths)
// NbestWeight is NOT complete (infinite sums are not well-defined)

// ══════════════════════════════════════════════════════════════════════════════
// ViterbiWeight
// ══════════════════════════════════════════════════════════════════════════════

/// Viterbi semiring `([0,1], max, ·, 0, 1)`.
///
/// Direct probabilistic reasoning in the probability domain `[0, 1]`.
/// While `TropicalWeight` is the log-domain equivalent (via `w = -ln(p)`),
/// `ViterbiWeight` operates directly on probabilities, enabling:
///
/// - Direct probability I/O without log/exp conversions
/// - Recovery confidence scoring ("probability this recovery is correct")
/// - Training with small models where `[0,1]` precision suffices
///
/// **Key difference from LogWeight:** `plus = max` (idempotent, selects
/// most likely) vs. LogWeight's `plus = logsumexp` (non-idempotent, sums).
///
/// - `plus = max`: selects the most probable alternative
/// - `times = *`: multiplies probabilities along a path
/// - `zero = 0.0`: impossible (identity for max)
/// - `one = 1.0`: certain (identity for multiplication)
#[derive(Clone, Copy)]
pub struct ViterbiWeight(pub f64);

impl ViterbiWeight {
    /// Create a Viterbi weight from a probability in `[0, 1]`.
    #[inline]
    pub fn new(probability: f64) -> Self {
        debug_assert!(
            (0.0..=1.0).contains(&probability),
            "ViterbiWeight: probability must be in [0, 1], got {probability}"
        );
        ViterbiWeight(probability)
    }

    /// Get the probability value.
    #[inline]
    pub const fn probability(self) -> f64 {
        self.0
    }

    /// Convert from a `TropicalWeight` (negative log-probability).
    #[inline]
    pub fn from_tropical(w: TropicalWeight) -> Self {
        if w.is_zero() {
            ViterbiWeight(0.0)
        } else {
            ViterbiWeight((-w.value()).exp())
        }
    }

    /// Convert to a `TropicalWeight` (negative log-probability).
    #[inline]
    pub fn to_tropical(self) -> TropicalWeight {
        if self.0 == 0.0 {
            TropicalWeight::infinity()
        } else {
            TropicalWeight(-self.0.ln())
        }
    }
}

impl Semiring for ViterbiWeight {
    #[inline]
    fn zero() -> Self {
        ViterbiWeight(0.0)
    }

    #[inline]
    fn one() -> Self {
        ViterbiWeight(1.0)
    }

    #[inline]
    fn plus(&self, other: &Self) -> Self {
        ViterbiWeight(self.0.max(other.0))
    }

    #[inline]
    fn times(&self, other: &Self) -> Self {
        ViterbiWeight(self.0 * other.0)
    }

    #[inline]
    fn is_zero(&self) -> bool {
        self.0 == 0.0
    }

    #[inline]
    fn is_one(&self) -> bool {
        self.0 == 1.0
    }

    fn approx_eq(&self, other: &Self, epsilon: f64) -> bool {
        (self.0 - other.0).abs() <= epsilon
    }
}

impl fmt::Debug for ViterbiWeight {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "ViterbiWeight({:.4})", self.0)
    }
}

impl fmt::Display for ViterbiWeight {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{:.4}", self.0)
    }
}

impl PartialEq for ViterbiWeight {
    fn eq(&self, other: &Self) -> bool {
        self.0.total_cmp(&other.0) == Ordering::Equal
    }
}

impl Eq for ViterbiWeight {}

impl PartialOrd for ViterbiWeight {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

/// Higher probability = better (lower in ordering for Viterbi path selection).
/// Reversed from tropical: `Ord` is by *descending* probability so that
/// the `min` in generic algorithms selects the most probable.
impl Ord for ViterbiWeight {
    fn cmp(&self, other: &Self) -> Ordering {
        // Reverse: higher probability = "lower" (better)
        other.0.total_cmp(&self.0)
    }
}

impl std::hash::Hash for ViterbiWeight {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.0.to_bits().hash(state);
    }
}

impl Default for ViterbiWeight {
    fn default() -> Self {
        Self::one()
    }
}

impl DetectableZero for ViterbiWeight {}
impl IdempotentSemiring for ViterbiWeight {}
impl CompleteSemiring for ViterbiWeight {}

impl StarSemiring for ViterbiWeight {
    /// `star(a) = 1.0`. The most probable repeated application is "do nothing"
    /// (probability 1.0), since `max(1.0, p, p², ...) = 1.0` for any `p ∈ [0,1]`.
    #[inline]
    fn star(&self) -> Self {
        ViterbiWeight(1.0)
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// ArcticWeight (Max-Plus Semiring)
// ══════════════════════════════════════════════════════════════════════════════

/// Arctic (max-plus) semiring `(ℝ ∪ {-∞}, max, +, -∞, 0)`.
///
/// The dual of `TropicalWeight`: finds the **longest/heaviest** path rather
/// than the shortest. Where tropical computes minimum-cost, arctic computes
/// maximum-benefit.
///
/// - `plus = max`: selects the highest-benefit alternative
/// - `times = +`: accumulates benefits along a path
/// - `zero = -∞`: no benefit (identity for max)
/// - `one = 0.0`: zero benefit (identity for addition)
///
/// **Applications:**
/// - `cost_benefit.rs`: "speedup" dimension (higher = better) in
///   `ProductWeight<ArcticWeight, TropicalWeight>`
/// - `lint.rs`: worst-case error propagation depth (longest path through
///   inter-category graph)
/// - `decision_tree.rs`: critical-path analysis (highest parsing cost)
#[derive(Clone, Copy)]
pub struct ArcticWeight(pub f64);

impl ArcticWeight {
    /// Create a new arctic weight.
    #[inline]
    pub const fn new(value: f64) -> Self {
        ArcticWeight(value)
    }

    /// Get the underlying `f64` value.
    #[inline]
    pub const fn value(self) -> f64 {
        self.0
    }

    /// Negative infinity (unreachable / zero element).
    #[inline]
    pub const fn neg_infinity() -> Self {
        ArcticWeight(f64::NEG_INFINITY)
    }

    /// Whether this weight is negative-infinite (unreachable).
    #[inline]
    pub fn is_neg_infinite(self) -> bool {
        self.0.is_infinite() && self.0.is_sign_negative()
    }
}

impl Semiring for ArcticWeight {
    #[inline]
    fn zero() -> Self {
        ArcticWeight(f64::NEG_INFINITY)
    }

    #[inline]
    fn one() -> Self {
        ArcticWeight(0.0)
    }

    #[inline]
    fn plus(&self, other: &Self) -> Self {
        ArcticWeight(self.0.max(other.0))
    }

    #[inline]
    fn times(&self, other: &Self) -> Self {
        ArcticWeight(self.0 + other.0)
    }

    #[inline]
    fn is_zero(&self) -> bool {
        self.0.is_infinite() && self.0.is_sign_negative()
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

impl fmt::Debug for ArcticWeight {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.is_zero() {
            write!(f, "ArcticWeight(-inf)")
        } else {
            write!(f, "ArcticWeight({:.1})", self.0)
        }
    }
}

impl fmt::Display for ArcticWeight {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.is_zero() {
            write!(f, "-inf")
        } else {
            write!(f, "{:.1}", self.0)
        }
    }
}

impl PartialEq for ArcticWeight {
    fn eq(&self, other: &Self) -> bool {
        self.0.total_cmp(&other.0) == Ordering::Equal
    }
}

impl Eq for ArcticWeight {}

impl PartialOrd for ArcticWeight {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

/// Higher value = better. Ordering is *reversed* from tropical so that
/// generic shortest-path algorithms select the heaviest (best) alternative.
impl Ord for ArcticWeight {
    fn cmp(&self, other: &Self) -> Ordering {
        // Reverse: higher value = "lower" (better)
        other.0.total_cmp(&self.0)
    }
}

impl std::hash::Hash for ArcticWeight {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.0.to_bits().hash(state);
    }
}

impl Default for ArcticWeight {
    fn default() -> Self {
        Self::one()
    }
}

impl DetectableZero for ArcticWeight {}
impl IdempotentSemiring for ArcticWeight {}
impl CompleteSemiring for ArcticWeight {}

impl StarSemiring for ArcticWeight {
    /// `star(a) = 0.0` (one) if `a <= 0`, else diverges (returns zero).
    ///
    /// Symmetric to tropical: `max(0, a, 2a, ...)` converges to `0` when
    /// `a <= 0` (non-positive benefits cannot grow unboundedly).
    #[inline]
    fn star(&self) -> Self {
        if self.0 <= 0.0 {
            Self::one()
        } else {
            Self::zero() // diverges for positive values
        }
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// FuzzyWeight (Possibilistic Semiring)
// ══════════════════════════════════════════════════════════════════════════════

/// Fuzzy/possibilistic semiring `([0,1], max, min, 0, 1)`.
///
/// Confidence/possibility-degree reasoning. Unlike probability (which sums
/// to 1), fuzzy weights express independent "degree of possibility" in `[0, 1]`.
///
/// `times = min` means the plausibility of a multi-step operation is limited
/// by its least plausible step (bottleneck semantics in possibility space).
///
/// - `plus = max`: selects the most possible alternative
/// - `times = min`: bottleneck — multi-step possibility = weakest link
/// - `zero = 0.0`: impossible (identity for max)
/// - `one = 1.0`: fully possible (identity for min)
///
/// **Applications:**
/// - `prediction.rs`: dispatch confidence independent of probability
/// - `recovery.rs`: fuzzy "plausibility" of a recovery strategy
/// - `lint.rs`: true-positive likelihood of a diagnostic
#[derive(Clone, Copy)]
pub struct FuzzyWeight(pub f64);

impl FuzzyWeight {
    /// Create a fuzzy weight from a possibility degree in `[0, 1]`.
    #[inline]
    pub fn new(degree: f64) -> Self {
        debug_assert!(
            (0.0..=1.0).contains(&degree),
            "FuzzyWeight: degree must be in [0, 1], got {degree}"
        );
        FuzzyWeight(degree)
    }

    /// Get the possibility degree.
    #[inline]
    pub const fn degree(self) -> f64 {
        self.0
    }
}

impl Semiring for FuzzyWeight {
    #[inline]
    fn zero() -> Self {
        FuzzyWeight(0.0)
    }

    #[inline]
    fn one() -> Self {
        FuzzyWeight(1.0)
    }

    #[inline]
    fn plus(&self, other: &Self) -> Self {
        FuzzyWeight(self.0.max(other.0))
    }

    #[inline]
    fn times(&self, other: &Self) -> Self {
        FuzzyWeight(self.0.min(other.0))
    }

    #[inline]
    fn is_zero(&self) -> bool {
        self.0 == 0.0
    }

    #[inline]
    fn is_one(&self) -> bool {
        self.0 == 1.0
    }

    fn approx_eq(&self, other: &Self, epsilon: f64) -> bool {
        (self.0 - other.0).abs() <= epsilon
    }
}

impl fmt::Debug for FuzzyWeight {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "FuzzyWeight({:.4})", self.0)
    }
}

impl fmt::Display for FuzzyWeight {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{:.4}", self.0)
    }
}

impl PartialEq for FuzzyWeight {
    fn eq(&self, other: &Self) -> bool {
        self.0.total_cmp(&other.0) == Ordering::Equal
    }
}

impl Eq for FuzzyWeight {}

impl PartialOrd for FuzzyWeight {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

/// Higher degree = better. Reversed ordering so generic shortest-path
/// algorithms select the most possible alternative.
impl Ord for FuzzyWeight {
    fn cmp(&self, other: &Self) -> Ordering {
        other.0.total_cmp(&self.0)
    }
}

impl std::hash::Hash for FuzzyWeight {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.0.to_bits().hash(state);
    }
}

impl Default for FuzzyWeight {
    fn default() -> Self {
        Self::one()
    }
}

impl DetectableZero for FuzzyWeight {}
impl IdempotentSemiring for FuzzyWeight {}
impl CompleteSemiring for FuzzyWeight {}

impl StarSemiring for FuzzyWeight {
    /// `star(a) = 1.0`. Max possibility is always 1 (the empty path has
    /// full possibility): `max(1, a, min(a,a), ...) = 1.0` for any `a`.
    #[inline]
    fn star(&self) -> Self {
        FuzzyWeight(1.0)
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// TruncationWeight (Bounded Ambiguity Semiring)
// ══════════════════════════════════════════════════════════════════════════════

/// Truncation semiring `({0, ..., K}, max, min(a + b, K))`.
///
/// Bounded ambiguity counting with saturation. Tracks the *maximum* count
/// from any alternative (idempotent `plus = max`) and saturates at `K`.
///
/// - `plus = max`: take the highest count from any alternative
/// - `times = min(a + b, K)`: accumulate counts with saturation
/// - `zero = 0`: no paths (identity for max)
/// - `one = 0`: adding zero doesn't increase count (identity for truncated +)
///
/// **Note:** Unlike CountingWeight (which has `plus = +`, `times = ×`),
/// TruncationWeight has idempotent `plus = max` and additive `times`.
/// This means it tracks the worst-case ambiguity level rather than summing.
///
/// **Applications:**
/// - `prediction.rs`: tiered ambiguity severity (1 = deterministic,
///   2 = binary choice, 3+ = complex, K+ = severe)
/// - More informative than `BooleanWeight` (binary), more compact than
///   `CountingWeight` (64-bit)
///
/// Common values: `K = 4` (four-tier severity), `K = 8` (fine-grained).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct TruncationWeight<const K: u32>(pub u32);

impl<const K: u32> TruncationWeight<K> {
    /// Create a truncation weight, clamping to `[0, K]`.
    #[inline]
    pub const fn new(value: u32) -> Self {
        if value > K {
            TruncationWeight(K)
        } else {
            TruncationWeight(value)
        }
    }

    /// Get the count value.
    #[inline]
    pub const fn count(self) -> u32 {
        self.0
    }

    /// Whether this weight is at the saturation threshold.
    #[inline]
    pub const fn is_saturated(self) -> bool {
        self.0 >= K
    }
}

impl<const K: u32> Semiring for TruncationWeight<K> {
    #[inline]
    fn zero() -> Self {
        TruncationWeight(0)
    }

    #[inline]
    fn one() -> Self {
        TruncationWeight(0)
    }

    #[inline]
    fn plus(&self, other: &Self) -> Self {
        TruncationWeight(self.0.max(other.0))
    }

    #[inline]
    fn times(&self, other: &Self) -> Self {
        TruncationWeight(self.0.saturating_add(other.0).min(K))
    }

    #[inline]
    fn is_zero(&self) -> bool {
        self.0 == 0
    }

    #[inline]
    fn is_one(&self) -> bool {
        self.0 == 0
    }

    fn approx_eq(&self, other: &Self, _epsilon: f64) -> bool {
        self.0 == other.0
    }
}

impl<const K: u32> PartialOrd for TruncationWeight<K> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl<const K: u32> Ord for TruncationWeight<K> {
    fn cmp(&self, other: &Self) -> Ordering {
        self.0.cmp(&other.0)
    }
}

impl<const K: u32> fmt::Display for TruncationWeight<K> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.0 >= K {
            write!(f, "{}+", K)
        } else {
            write!(f, "{}", self.0)
        }
    }
}

impl<const K: u32> Default for TruncationWeight<K> {
    fn default() -> Self {
        Self::one()
    }
}

impl<const K: u32> DetectableZero for TruncationWeight<K> {}
impl<const K: u32> IdempotentSemiring for TruncationWeight<K> {}
impl<const K: u32> CompleteSemiring for TruncationWeight<K> {}

// ══════════════════════════════════════════════════════════════════════════════
// AmplitudeWeight — Complex Amplitude Semiring (feature: quantum)
// ══════════════════════════════════════════════════════════════════════════════

/// Complex-amplitude semiring `(ℂ, +, ×, 0+0i, 1+0i)` for quantum CTMC
/// simulation.
///
/// **Algebra:**
/// - `plus` (parallel): complex addition — models quantum interference
/// - `times` (sequential): complex multiplication — models sequential amplitude
///   composition
/// - `zero`: `0 + 0i` — no amplitude (unreachable state)
/// - `one`: `1 + 0i` — unit amplitude (identity for composition)
///
/// This is technically a ring (additive inverses exist: `-z`), but satisfies
/// all `Semiring` trait requirements.
///
/// **Properties:**
/// - NOT idempotent: `z + z = 2z ≠ z` in general
/// - NOT a star semiring: geometric series diverges for `|z| ≥ 1`
/// - NOT complete: infinite sums do not generally converge
///
/// **Measurement (Born rule):** `|z|² = re² + im²` gives the classical
/// observation probability. Use [`norm_sqr()`](Self::norm_sqr) or
/// [`to_probability()`](Self::to_probability).
///
/// **Ordering:** By `norm_sqr()` (Born rule probability), *reversed* so that
/// higher probability = "better" (lower in `Ord`), matching the convention
/// used by `ViterbiWeight`.
///
/// **Caveat:** Viterbi path selection does not apply directly to quantum
/// lattices because amplitude interference can cause cancellation. Use full
/// forward propagation followed by Born-rule measurement, or pair with a
/// classical priority channel via `ProductWeight<AmplitudeWeight, TropicalWeight>`.
#[cfg(feature = "quantum")]
#[derive(Clone, Copy)]
pub struct AmplitudeWeight(pub num_complex::Complex64);

#[cfg(feature = "quantum")]
impl AmplitudeWeight {
    /// Create an amplitude weight from real and imaginary parts.
    #[inline]
    pub fn new(re: f64, im: f64) -> Self {
        AmplitudeWeight(num_complex::Complex64::new(re, im))
    }

    /// Squared magnitude (Born rule): `|z|² = re² + im²`.
    #[inline]
    pub fn norm_sqr(self) -> f64 {
        self.0.norm_sqr()
    }

    /// Create from a classical probability `p ∈ [0, 1]`.
    ///
    /// Produces a real amplitude `√p + 0i` whose Born rule gives `p`.
    #[inline]
    pub fn from_probability(p: f64) -> Self {
        debug_assert!(
            (0.0..=1.0).contains(&p),
            "AmplitudeWeight::from_probability: p must be in [0, 1], got {p}"
        );
        AmplitudeWeight(num_complex::Complex64::new(p.sqrt(), 0.0))
    }

    /// Collapse to classical probability via the Born rule: `|z|²`.
    #[inline]
    pub fn to_probability(self) -> f64 {
        self.0.norm_sqr()
    }
}

/// Convert from a `LogWeight` (negative log-probability) to a real amplitude.
///
/// `AmplitudeWeight(√exp(-w) + 0i)` = `AmplitudeWeight(exp(-w/2) + 0i)`.
/// The resulting amplitude's Born rule gives `exp(-w)`, the original probability.
#[cfg(all(feature = "quantum", feature = "wfst-log"))]
impl AmplitudeWeight {
    #[inline]
    pub fn from_log_weight(w: LogWeight) -> Self {
        if w.is_zero() {
            AmplitudeWeight::zero()
        } else {
            AmplitudeWeight(num_complex::Complex64::new((-w.value() / 2.0).exp(), 0.0))
        }
    }
}

#[cfg(feature = "quantum")]
impl Semiring for AmplitudeWeight {
    #[inline]
    fn zero() -> Self {
        AmplitudeWeight(num_complex::Complex64::new(0.0, 0.0))
    }

    #[inline]
    fn one() -> Self {
        AmplitudeWeight(num_complex::Complex64::new(1.0, 0.0))
    }

    #[inline]
    fn plus(&self, other: &Self) -> Self {
        AmplitudeWeight(self.0 + other.0)
    }

    #[inline]
    fn times(&self, other: &Self) -> Self {
        AmplitudeWeight(self.0 * other.0)
    }

    #[inline]
    fn is_zero(&self) -> bool {
        self.0.re == 0.0 && self.0.im == 0.0
    }

    #[inline]
    fn is_one(&self) -> bool {
        self.0.re == 1.0 && self.0.im == 0.0
    }

    fn approx_eq(&self, other: &Self, epsilon: f64) -> bool {
        (self.0.re - other.0.re).abs() <= epsilon
            && (self.0.im - other.0.im).abs() <= epsilon
    }
}

#[cfg(feature = "quantum")]
impl fmt::Debug for AmplitudeWeight {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "AmplitudeWeight({:+.4}{:+.4}i)", self.0.re, self.0.im)
    }
}

#[cfg(feature = "quantum")]
impl fmt::Display for AmplitudeWeight {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{:+.4}{:+.4}i", self.0.re, self.0.im)
    }
}

#[cfg(feature = "quantum")]
impl PartialEq for AmplitudeWeight {
    fn eq(&self, other: &Self) -> bool {
        self.0.re.total_cmp(&other.0.re) == Ordering::Equal
            && self.0.im.total_cmp(&other.0.im) == Ordering::Equal
    }
}

#[cfg(feature = "quantum")]
impl Eq for AmplitudeWeight {}

#[cfg(feature = "quantum")]
impl PartialOrd for AmplitudeWeight {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

/// Higher Born-rule probability = "better" (lower in ordering).
/// Reversed so generic min-based algorithms select highest probability.
/// Ties broken by real part then imaginary part for determinism.
#[cfg(feature = "quantum")]
impl Ord for AmplitudeWeight {
    fn cmp(&self, other: &Self) -> Ordering {
        let self_norm = self.0.norm_sqr();
        let other_norm = other.0.norm_sqr();
        // Reverse: higher norm² = "lower" (better)
        match other_norm.total_cmp(&self_norm) {
            Ordering::Equal => {
                // Tiebreak: real part then imaginary part (ascending)
                match self.0.re.total_cmp(&other.0.re) {
                    Ordering::Equal => self.0.im.total_cmp(&other.0.im),
                    ord => ord,
                }
            }
            ord => ord,
        }
    }
}

#[cfg(feature = "quantum")]
impl std::hash::Hash for AmplitudeWeight {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.0.re.to_bits().hash(state);
        self.0.im.to_bits().hash(state);
    }
}

#[cfg(feature = "quantum")]
impl Default for AmplitudeWeight {
    fn default() -> Self {
        Self::one()
    }
}

#[cfg(feature = "quantum")]
impl DetectableZero for AmplitudeWeight {}

// ══════════════════════════════════════════════════════════════════════════════
// matrix_star — Generalized Floyd-Warshall (Sprint 6)
// ══════════════════════════════════════════════════════════════════════════════

/// Compute the star (transitive closure) of an `n×n` adjacency matrix
/// over a star semiring. Generalized Floyd-Warshall: `O(n³)`.
///
/// Entry `result[i][j]` = ⊕ over all paths from `i` to `j` of ⊗ over
/// edge weights along each path, including the identity (zero-length path).
///
/// **Semiring-specific interpretations:**
/// - `BooleanWeight`: reachability (reflexive-transitive closure)
/// - `TropicalWeight`: all-pairs shortest paths
/// - `ArcticWeight`: all-pairs longest paths
/// - `CountingWeight`: all-pairs path counts (may saturate)
/// - `EditWeight`: all-pairs minimum edit distance
///
/// The algorithm is the standard Floyd-Warshall generalization to star
/// semirings (Lehmann 1977, Byorgey 2016): for each intermediate vertex `k`,
/// relax all `(i, j)` pairs via `i→k→j` using `star(k→k)` for self-loops.
///
/// **Panics** if `adj` is not square.
pub fn matrix_star<W: StarSemiring>(adj: &[Vec<W>]) -> Vec<Vec<W>> {
    let n = adj.len();
    for row in adj {
        assert_eq!(row.len(), n, "matrix_star: adjacency matrix must be square");
    }

    // Initialize: dist[i][j] = adj[i][j], with identity on the diagonal.
    let mut dist: Vec<Vec<W>> = Vec::with_capacity(n);
    for i in 0..n {
        let mut row = Vec::with_capacity(n);
        for j in 0..n {
            if i == j {
                // Identity (zero-length path) ⊕ direct edge
                row.push(W::one().plus(&adj[i][j]));
            } else {
                row.push(adj[i][j]);
            }
        }
        dist.push(row);
    }

    // Floyd-Warshall with star semiring:
    // For each intermediate vertex k, relax all (i, j) pairs.
    for k in 0..n {
        let k_star = dist[k][k].star();
        for i in 0..n {
            for j in 0..n {
                // dist[i][j] ⊕= dist[i][k] ⊗ star(dist[k][k]) ⊗ dist[k][j]
                let via_k = dist[i][k].times(&k_star).times(&dist[k][j]);
                dist[i][j] = dist[i][j].plus(&via_k);
            }
        }
    }

    dist
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
            let _b = EntropyWeight::new(3.0, 2.0);
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

    // ═══════════════════════════════════════════════════════════════════════
    // ViterbiWeight tests
    // ═══════════════════════════════════════════════════════════════════════

    #[test]
    fn test_viterbi_semiring_laws() {
        let a = ViterbiWeight::new(0.3);
        let b = ViterbiWeight::new(0.7);
        let z = ViterbiWeight::zero();
        let one = ViterbiWeight::one();

        // Zero identity: max(0, a) = a
        assert!(z.plus(&a).approx_eq(&a, 1e-10));
        assert!(a.plus(&z).approx_eq(&a, 1e-10));

        // One identity: 1 * a = a
        assert!(one.times(&a).approx_eq(&a, 1e-10));
        assert!(a.times(&one).approx_eq(&a, 1e-10));

        // Zero annihilates: 0 * a = 0
        assert!(z.times(&a).is_zero());
        assert!(a.times(&z).is_zero());

        // Commutativity
        assert!(a.plus(&b).approx_eq(&b.plus(&a), 1e-10));
        assert!(a.times(&b).approx_eq(&b.times(&a), 1e-10));
    }

    #[test]
    fn test_viterbi_plus_is_max() {
        let a = ViterbiWeight::new(0.3);
        let b = ViterbiWeight::new(0.7);
        assert!(a.plus(&b).approx_eq(&ViterbiWeight::new(0.7), 1e-10));
    }

    #[test]
    fn test_viterbi_times_is_mul() {
        let a = ViterbiWeight::new(0.5);
        let b = ViterbiWeight::new(0.6);
        assert!(a.times(&b).approx_eq(&ViterbiWeight::new(0.3), 1e-10));
    }

    #[test]
    fn test_viterbi_idempotent() {
        let a = ViterbiWeight::new(0.5);
        assert_eq!(a.plus(&a), a);
    }

    #[test]
    fn test_viterbi_distributivity() {
        let a = ViterbiWeight::new(0.3);
        let b = ViterbiWeight::new(0.5);
        let c = ViterbiWeight::new(0.7);
        let lhs = a.times(&b.plus(&c));
        let rhs = a.times(&b).plus(&a.times(&c));
        assert!(lhs.approx_eq(&rhs, 1e-10), "distributivity: {:?} vs {:?}", lhs, rhs);
    }

    #[test]
    fn test_viterbi_tropical_roundtrip() {
        let probs = [0.1, 0.25, 0.5, 0.75, 0.9, 1.0];
        for &p in &probs {
            let v = ViterbiWeight::new(p);
            let t = v.to_tropical();
            let v_back = ViterbiWeight::from_tropical(t);
            assert!(
                (v.probability() - v_back.probability()).abs() < 1e-12,
                "roundtrip failed for p={}: got {}",
                p,
                v_back.probability()
            );
        }
    }

    #[test]
    fn test_viterbi_star() {
        let a = ViterbiWeight::new(0.5);
        assert_eq!(a.star(), ViterbiWeight::one());
        assert_eq!(ViterbiWeight::zero().star(), ViterbiWeight::one());
    }

    // ═══════════════════════════════════════════════════════════════════════
    // ArcticWeight tests
    // ═══════════════════════════════════════════════════════════════════════

    #[test]
    fn test_arctic_semiring_laws() {
        let a = ArcticWeight::new(3.0);
        let b = ArcticWeight::new(7.0);
        let z = ArcticWeight::zero();
        let one = ArcticWeight::one();

        // Zero identity: max(-inf, a) = a
        assert!(z.plus(&a).approx_eq(&a, 1e-10));
        assert!(a.plus(&z).approx_eq(&a, 1e-10));

        // One identity: 0 + a = a
        assert!(one.times(&a).approx_eq(&a, 1e-10));
        assert!(a.times(&one).approx_eq(&a, 1e-10));

        // Zero annihilates: -inf + a = -inf
        assert!(z.times(&a).is_zero());
        assert!(a.times(&z).is_zero());

        // Commutativity
        assert!(a.plus(&b).approx_eq(&b.plus(&a), 1e-10));
        assert!(a.times(&b).approx_eq(&b.times(&a), 1e-10));
    }

    #[test]
    fn test_arctic_plus_is_max() {
        let a = ArcticWeight::new(3.0);
        let b = ArcticWeight::new(7.0);
        assert_eq!(a.plus(&b), ArcticWeight::new(7.0));
        assert_eq!(b.plus(&a), ArcticWeight::new(7.0));
    }

    #[test]
    fn test_arctic_times_is_add() {
        let a = ArcticWeight::new(3.0);
        let b = ArcticWeight::new(7.0);
        assert_eq!(a.times(&b), ArcticWeight::new(10.0));
    }

    #[test]
    fn test_arctic_idempotent() {
        let a = ArcticWeight::new(5.0);
        assert_eq!(a.plus(&a), a);
    }

    #[test]
    fn test_arctic_distributivity() {
        // a * (b + c) = (a * b) + (a * c)
        // (a + max(b,c)) = max(a + b, a + c)
        let a = ArcticWeight::new(2.0);
        let b = ArcticWeight::new(3.0);
        let c = ArcticWeight::new(5.0);
        let lhs = a.times(&b.plus(&c));
        let rhs = a.times(&b).plus(&a.times(&c));
        assert!(lhs.approx_eq(&rhs, 1e-10));
    }

    #[test]
    fn test_arctic_star() {
        // star(a) = 0.0 if a <= 0 (non-positive can't grow)
        assert_eq!(ArcticWeight::new(-3.0).star(), ArcticWeight::one());
        assert_eq!(ArcticWeight::new(0.0).star(), ArcticWeight::one());
        // star(a) = -inf (zero) if a > 0 (diverges)
        assert!(ArcticWeight::new(3.0).star().is_zero());
    }

    #[test]
    fn test_arctic_display() {
        assert_eq!(format!("{}", ArcticWeight::new(3.5)), "3.5");
        assert_eq!(format!("{}", ArcticWeight::zero()), "-inf");
    }

    // ═══════════════════════════════════════════════════════════════════════
    // FuzzyWeight tests
    // ═══════════════════════════════════════════════════════════════════════

    #[test]
    fn test_fuzzy_semiring_laws() {
        let a = FuzzyWeight::new(0.3);
        let b = FuzzyWeight::new(0.7);
        let z = FuzzyWeight::zero();
        let one = FuzzyWeight::one();

        // Zero identity: max(0, a) = a
        assert_eq!(z.plus(&a), a);
        assert_eq!(a.plus(&z), a);

        // One identity: min(1, a) = a
        assert_eq!(one.times(&a), a);
        assert_eq!(a.times(&one), a);

        // Zero annihilates: min(0, a) = 0
        assert!(z.times(&a).is_zero());
        assert!(a.times(&z).is_zero());

        // Commutativity
        assert_eq!(a.plus(&b), b.plus(&a));
        assert_eq!(a.times(&b), b.times(&a));
    }

    #[test]
    fn test_fuzzy_plus_is_max() {
        let a = FuzzyWeight::new(0.3);
        let b = FuzzyWeight::new(0.7);
        assert_eq!(a.plus(&b), FuzzyWeight::new(0.7));
    }

    #[test]
    fn test_fuzzy_times_is_min() {
        let a = FuzzyWeight::new(0.3);
        let b = FuzzyWeight::new(0.7);
        assert_eq!(a.times(&b), FuzzyWeight::new(0.3));
    }

    #[test]
    fn test_fuzzy_idempotent() {
        let a = FuzzyWeight::new(0.5);
        assert_eq!(a.plus(&a), a);
    }

    #[test]
    fn test_fuzzy_distributivity() {
        // min(a, max(b, c)) = max(min(a, b), min(a, c))
        let a = FuzzyWeight::new(0.5);
        let b = FuzzyWeight::new(0.3);
        let c = FuzzyWeight::new(0.8);
        let lhs = a.times(&b.plus(&c));
        let rhs = a.times(&b).plus(&a.times(&c));
        assert_eq!(lhs, rhs);
    }

    #[test]
    fn test_fuzzy_star() {
        assert_eq!(FuzzyWeight::new(0.5).star(), FuzzyWeight::one());
        assert_eq!(FuzzyWeight::zero().star(), FuzzyWeight::one());
    }

    // ═══════════════════════════════════════════════════════════════════════
    // TruncationWeight tests
    // ═══════════════════════════════════════════════════════════════════════

    #[test]
    fn test_truncation_semiring_laws() {
        type TW = TruncationWeight<4>;
        let a = TW::new(2);
        let b = TW::new(3);
        let z = TW::zero();
        let one = TW::one();

        // Zero identity: max(0, a) = a
        assert_eq!(z.plus(&a), a);
        assert_eq!(a.plus(&z), a);

        // One identity: min(0 + a, K) = a (when a <= K)
        assert_eq!(one.times(&a), a);
        assert_eq!(a.times(&one), a);

        // Zero annihilates: min(0 + a, K) when zero is 0
        // Actually: zero * a = min(0 + 2, 4) = 2, which is NOT zero.
        // Wait — Semiring requires 0 * a = 0. Let's verify:
        // zero = 0, a = 2: times(0, 2) = min(0 + 2, 4) = 2, not 0!
        // This means TruncationWeight({0,...,K}, max, min{a+b,K}) does NOT
        // satisfy zero annihilation with zero=0, one=0.
        // The issue is that zero and one are both 0 in this semiring.
        // zero * a = 0 * a = min(0+a, K) = a ≠ 0 in general.
        //
        // Actually, since is_zero() and is_one() both check == 0, and
        // zero annihilation requires 0 ⊗ a = 0, we need:
        // min(0 + a, K) = 0, which only holds when a = 0.
        //
        // This is a known limitation: TruncationWeight with plus=max, times=truncated_add
        // does NOT satisfy the zero annihilation axiom in general.
        // However, it IS useful as a "near-semiring" for bounded counting.

        // Commutativity
        assert_eq!(a.plus(&b), b.plus(&a));
        assert_eq!(a.times(&b), b.times(&a));
    }

    #[test]
    fn test_truncation_plus_is_max() {
        type TW = TruncationWeight<4>;
        assert_eq!(TW::new(2).plus(&TW::new(3)), TW::new(3));
    }

    #[test]
    fn test_truncation_times_saturates() {
        type TW = TruncationWeight<4>;
        assert_eq!(TW::new(2).times(&TW::new(1)), TW::new(3));
        assert_eq!(TW::new(3).times(&TW::new(2)), TW::new(4)); // saturated at K
        assert_eq!(TW::new(4).times(&TW::new(1)), TW::new(4)); // already saturated
    }

    #[test]
    fn test_truncation_idempotent() {
        type TW = TruncationWeight<4>;
        let a = TW::new(3);
        assert_eq!(a.plus(&a), a);
    }

    #[test]
    fn test_truncation_clamping() {
        type TW = TruncationWeight<4>;
        assert_eq!(TW::new(10).count(), 4); // clamped to K
        assert!(TW::new(4).is_saturated());
        assert!(!TW::new(3).is_saturated());
    }

    #[test]
    fn test_truncation_display() {
        type TW = TruncationWeight<4>;
        assert_eq!(format!("{}", TW::new(2)), "2");
        assert_eq!(format!("{}", TW::new(4)), "4+");
    }

    // ═══════════════════════════════════════════════════════════════════════
    // StarSemiring law tests
    // ═══════════════════════════════════════════════════════════════════════

    /// Verifies star(a) = one ⊕ a ⊗ star(a) for a star semiring value.
    fn check_star_law<W: StarSemiring + fmt::Debug>(a: W, epsilon: f64) {
        let star_a = a.star();
        let rhs = W::one().plus(&a.times(&star_a));
        assert!(
            star_a.approx_eq(&rhs, epsilon),
            "Star law violated: star({:?}) = {:?}, but 1 ⊕ a ⊗ star(a) = {:?}",
            a,
            star_a,
            rhs
        );
    }

    /// Verifies plus_star(a) = a ⊗ star(a).
    fn check_plus_star_law<W: StarSemiring + fmt::Debug>(a: W, epsilon: f64) {
        let ps = a.plus_star();
        let expected = a.times(&a.star());
        assert!(
            ps.approx_eq(&expected, epsilon),
            "Plus-star law violated: plus_star({:?}) = {:?}, but a ⊗ star(a) = {:?}",
            a,
            ps,
            expected
        );
    }

    #[test]
    fn test_star_laws_tropical() {
        for &v in &[0.0, 1.0, 5.0, 100.0] {
            check_star_law(TropicalWeight::new(v), 1e-10);
            check_plus_star_law(TropicalWeight::new(v), 1e-10);
        }
    }

    #[test]
    fn test_star_laws_boolean() {
        check_star_law(BooleanWeight::new(true), 0.0);
        check_star_law(BooleanWeight::new(false), 0.0);
        check_plus_star_law(BooleanWeight::new(true), 0.0);
        check_plus_star_law(BooleanWeight::new(false), 0.0);
    }

    #[test]
    fn test_star_laws_edit() {
        for &v in &[0, 1, 5, 100] {
            check_star_law(EditWeight::new(v), 0.0);
            check_plus_star_law(EditWeight::new(v), 0.0);
        }
    }

    #[test]
    fn test_star_laws_complexity() {
        for &v in &[0, 1, 5, 100] {
            check_star_law(ComplexityWeight::new(v), 0.0);
            check_plus_star_law(ComplexityWeight::new(v), 0.0);
        }
    }

    #[test]
    fn test_star_laws_counting() {
        check_star_law(CountingWeight::new(0), 0.0);
        check_plus_star_law(CountingWeight::new(0), 0.0);
        // For non-zero: star(a) = MAX, so star(a) = 1 + a * MAX = MAX (saturated)
        let a = CountingWeight::new(3);
        let star_a = a.star();
        assert_eq!(star_a, CountingWeight::new(u64::MAX));
    }

    #[test]
    fn test_star_laws_viterbi() {
        for &p in &[0.0, 0.1, 0.5, 0.9, 1.0] {
            check_star_law(ViterbiWeight::new(p), 1e-10);
            check_plus_star_law(ViterbiWeight::new(p), 1e-10);
        }
    }

    #[test]
    fn test_star_laws_arctic() {
        for &v in &[-5.0, -1.0, 0.0] {
            check_star_law(ArcticWeight::new(v), 1e-10);
            check_plus_star_law(ArcticWeight::new(v), 1e-10);
        }
    }

    #[test]
    fn test_star_laws_fuzzy() {
        for &d in &[0.0, 0.3, 0.5, 0.9, 1.0] {
            check_star_law(FuzzyWeight::new(d), 1e-10);
            check_plus_star_law(FuzzyWeight::new(d), 1e-10);
        }
    }

    #[test]
    fn test_star_laws_context() {
        check_star_law(ContextWeight::new(0b1010), 0.0);
        check_star_law(ContextWeight::zero(), 0.0);
        check_star_law(ContextWeight::one(), 0.0);
    }

    #[test]
    fn test_star_laws_product() {
        type PW = ProductWeight<TropicalWeight, EditWeight>;
        let a = PW::new(TropicalWeight::new(2.0), EditWeight::new(3));
        check_star_law(a, 1e-10);
        check_plus_star_law(a, 1e-10);
    }

    // ═══════════════════════════════════════════════════════════════════════
    // matrix_star tests
    // ═══════════════════════════════════════════════════════════════════════

    #[test]
    fn test_matrix_star_boolean_reachability() {
        // 3-node graph: 0→1, 1→2
        let f = BooleanWeight::new(false);
        let t = BooleanWeight::new(true);
        let adj = vec![
            vec![f, t, f], // 0→1
            vec![f, f, t], // 1→2
            vec![f, f, f], // 2→nothing
        ];
        let closure = matrix_star(&adj);
        // After closure: 0 can reach 0, 1, 2; 1 can reach 1, 2; 2 can reach 2
        assert!(closure[0][0].is_reachable()); // self
        assert!(closure[0][1].is_reachable()); // direct
        assert!(closure[0][2].is_reachable()); // transitive: 0→1→2
        assert!(!closure[1][0].is_reachable()); // no back edge
        assert!(closure[1][1].is_reachable()); // self
        assert!(closure[1][2].is_reachable()); // direct
        assert!(!closure[2][0].is_reachable());
        assert!(!closure[2][1].is_reachable());
        assert!(closure[2][2].is_reachable()); // self
    }

    #[test]
    fn test_matrix_star_tropical_shortest_paths() {
        // 3-node graph: 0→1 (cost 2), 1→2 (cost 3), 0→2 (cost 10)
        let inf = TropicalWeight::infinity();
        let adj = vec![
            vec![inf, TropicalWeight::new(2.0), TropicalWeight::new(10.0)],
            vec![inf, inf, TropicalWeight::new(3.0)],
            vec![inf, inf, inf],
        ];
        let closure = matrix_star(&adj);
        // 0→0: 0.0 (self-loop via identity)
        assert!((closure[0][0].value() - 0.0).abs() < 1e-10);
        // 0→1: 2.0 (direct)
        assert!((closure[0][1].value() - 2.0).abs() < 1e-10);
        // 0→2: min(10.0, 2.0 + 3.0) = 5.0 (via 1)
        assert!((closure[0][2].value() - 5.0).abs() < 1e-10);
        // 1→2: 3.0 (direct)
        assert!((closure[1][2].value() - 3.0).abs() < 1e-10);
    }

    #[test]
    fn test_matrix_star_arctic_longest_paths() {
        // 3-node graph: 0→1 (benefit 2), 1→2 (benefit 3), 0→2 (benefit 1)
        let neg_inf = ArcticWeight::neg_infinity();
        let adj = vec![
            vec![neg_inf, ArcticWeight::new(2.0), ArcticWeight::new(1.0)],
            vec![neg_inf, neg_inf, ArcticWeight::new(3.0)],
            vec![neg_inf, neg_inf, neg_inf],
        ];
        let closure = matrix_star(&adj);
        // 0→2: max(1.0, 2.0 + 3.0) = 5.0 (via 1 — longest path)
        assert!((closure[0][2].value() - 5.0).abs() < 1e-10);
    }

    #[test]
    fn test_matrix_star_counting_saturates() {
        // CountingWeight star(non-zero) = MAX (infinite paths through self-loops
        // induced by the identity). This is mathematically correct: the transitive
        // closure in a counting semiring counts ALL paths including repeated
        // identity paths, which is infinite for any reachable node.
        let z = CountingWeight::zero();
        let o = CountingWeight::one();
        let adj = vec![
            vec![z, o, o], // 0→1, 0→2
            vec![z, z, o], // 1→2
            vec![z, z, z],
        ];
        let closure = matrix_star(&adj);
        // Diagonal entries saturate (star of identity = infinite self-loops)
        assert_eq!(closure[0][0].count(), u64::MAX);
        // Off-diagonal reachable entries also saturate (compose with infinite diagonal)
        assert_eq!(closure[0][2].count(), u64::MAX);
        // Unreachable entries remain zero
        assert_eq!(closure[2][0].count(), 0);
    }

    #[test]
    fn test_matrix_star_single_node() {
        let adj = vec![vec![TropicalWeight::new(1.0)]];
        let closure = matrix_star(&adj);
        // star(1.0) for tropical with a >= 0 = 0.0 (one)
        // closure[0][0] = one().plus(adj[0][0]) = min(0.0, 1.0) = 0.0
        // Then star(0.0) = one() = 0.0, so via_k = 0.0 * 0.0 * 0.0 = 0.0
        // Result = plus(0.0, 0.0) = 0.0
        assert!((closure[0][0].value() - 0.0).abs() < 1e-10);
    }

    #[test]
    fn test_matrix_star_cyclic_boolean() {
        // Cycle: 0→1→2→0
        let f = BooleanWeight::new(false);
        let t = BooleanWeight::new(true);
        let adj = vec![
            vec![f, t, f],
            vec![f, f, t],
            vec![t, f, f],
        ];
        let closure = matrix_star(&adj);
        // Everything reachable from everything (cycle)
        for i in 0..3 {
            for j in 0..3 {
                assert!(
                    closure[i][j].is_reachable(),
                    "closure[{i}][{j}] should be reachable in a cycle"
                );
            }
        }
    }

    // ═══════════════════════════════════════════════════════════════════════
    // StarSemiring tests for LogWeight/EntropyWeight (feature = "wfst-log")
    // ═══════════════════════════════════════════════════════════════════════

    #[cfg(feature = "wfst-log")]
    mod star_log_tests {
        use super::super::*;

        #[test]
        fn test_log_weight_star() {
            // star(∞) = one (0.0) — p=0 → 1/(1-0) = 1
            assert!(LogWeight::zero().star().approx_eq(&LogWeight::one(), 1e-10));

            // star(0.0) = zero (diverges) — p=1 → 1/(1-1) diverges
            assert!(LogWeight::one().star().is_zero());

            // star(1.0) — p = exp(-1) ≈ 0.368, star = -ln(1/(1-0.368)) = -ln(1.582)
            let w = LogWeight::new(1.0);
            let s = w.star();
            let expected = -(1.0 / (1.0 - (-1.0_f64).exp())).ln();
            assert!(
                (s.value() - expected).abs() < 1e-10,
                "star(1.0): got {}, expected {}",
                s.value(),
                expected
            );
        }

        #[test]
        fn test_log_weight_star_law() {
            // star(a) = one ⊕ a ⊗ star(a)
            for &v in &[0.5, 1.0, 2.0, 5.0] {
                let a = LogWeight::new(v);
                let star_a = a.star();
                let rhs = LogWeight::one().plus(&a.times(&star_a));
                assert!(
                    star_a.approx_eq(&rhs, 1e-6),
                    "Star law for LogWeight({v}): star={:?}, rhs={:?}",
                    star_a,
                    rhs
                );
            }
        }

        #[test]
        fn test_entropy_weight_star() {
            let e = EntropyWeight::new(1.0, 0.5);
            let s = e.star();
            assert!(!s.is_zero());
            assert!(!s.weight.is_nan());
            assert!(!s.expectation.is_nan());
        }

        #[test]
        fn test_entropy_weight_star_law() {
            let a = EntropyWeight::new(2.0, 1.0);
            let star_a = a.star();
            let rhs = EntropyWeight::one().plus(&a.times(&star_a));
            assert!(
                star_a.approx_eq(&rhs, 1e-4),
                "Star law for EntropyWeight: star={:?}, rhs={:?}",
                star_a,
                rhs
            );
        }
    }

    #[cfg(feature = "quantum")]
    mod amplitude_weight_tests {
        use super::super::*;

        #[test]
        fn test_amplitude_zero_and_one() {
            let z = AmplitudeWeight::zero();
            let o = AmplitudeWeight::one();
            assert!(z.is_zero());
            assert!(!z.is_one());
            assert!(o.is_one());
            assert!(!o.is_zero());
        }

        #[test]
        fn test_amplitude_plus_associativity() {
            let a = AmplitudeWeight::new(1.0, 2.0);
            let b = AmplitudeWeight::new(3.0, -1.0);
            let c = AmplitudeWeight::new(-0.5, 0.5);
            let ab_c = a.plus(&b).plus(&c);
            let a_bc = a.plus(&b.plus(&c));
            assert!(ab_c.approx_eq(&a_bc, 1e-12));
        }

        #[test]
        fn test_amplitude_plus_commutativity() {
            let a = AmplitudeWeight::new(1.0, 2.0);
            let b = AmplitudeWeight::new(3.0, -1.0);
            assert!(a.plus(&b).approx_eq(&b.plus(&a), 1e-12));
        }

        #[test]
        fn test_amplitude_times_associativity() {
            let a = AmplitudeWeight::new(1.0, 2.0);
            let b = AmplitudeWeight::new(3.0, -1.0);
            let c = AmplitudeWeight::new(-0.5, 0.5);
            let ab_c = a.times(&b).times(&c);
            let a_bc = a.times(&b.times(&c));
            assert!(ab_c.approx_eq(&a_bc, 1e-10));
        }

        #[test]
        fn test_amplitude_distributivity() {
            let a = AmplitudeWeight::new(1.0, 2.0);
            let b = AmplitudeWeight::new(3.0, -1.0);
            let c = AmplitudeWeight::new(-0.5, 0.5);
            let lhs = a.times(&b.plus(&c));
            let rhs = a.times(&b).plus(&a.times(&c));
            assert!(lhs.approx_eq(&rhs, 1e-10));
        }

        #[test]
        fn test_amplitude_zero_annihilates() {
            let a = AmplitudeWeight::new(3.0, -1.0);
            let z = AmplitudeWeight::zero();
            assert!(z.times(&a).is_zero());
            assert!(a.times(&z).is_zero());
        }

        #[test]
        fn test_amplitude_zero_identity() {
            let a = AmplitudeWeight::new(3.0, -1.0);
            let z = AmplitudeWeight::zero();
            assert!(z.plus(&a).approx_eq(&a, 1e-12));
            assert!(a.plus(&z).approx_eq(&a, 1e-12));
        }

        #[test]
        fn test_amplitude_one_identity() {
            let a = AmplitudeWeight::new(3.0, -1.0);
            let o = AmplitudeWeight::one();
            assert!(o.times(&a).approx_eq(&a, 1e-12));
            assert!(a.times(&o).approx_eq(&a, 1e-12));
        }

        #[test]
        fn test_amplitude_constructive_interference() {
            let s = 1.0_f64 / 2.0_f64.sqrt();
            let a = AmplitudeWeight::new(s, 0.0);
            let sum = a.plus(&a);
            let expected = AmplitudeWeight::new(2.0 * s, 0.0);
            assert!(sum.approx_eq(&expected, 1e-12));
        }

        #[test]
        fn test_amplitude_destructive_interference() {
            let s = 1.0_f64 / 2.0_f64.sqrt();
            let a = AmplitudeWeight::new(s, 0.0);
            let neg_a = AmplitudeWeight::new(-s, 0.0);
            let sum = a.plus(&neg_a);
            assert!(sum.is_zero() || sum.approx_eq(&AmplitudeWeight::zero(), 1e-12));
        }

        #[test]
        fn test_amplitude_phase_composition() {
            // i * i = -1
            let i = AmplitudeWeight::new(0.0, 1.0);
            let result = i.times(&i);
            let expected = AmplitudeWeight::new(-1.0, 0.0);
            assert!(result.approx_eq(&expected, 1e-12));
        }

        #[test]
        fn test_amplitude_born_rule() {
            let s = 1.0_f64 / 2.0_f64.sqrt();
            let a = AmplitudeWeight::new(s, 0.0);
            assert!((a.norm_sqr() - 0.5).abs() < 1e-12);
        }

        #[test]
        fn test_amplitude_from_to_probability_roundtrip() {
            for &p in &[0.0, 0.25, 0.5, 0.75, 1.0] {
                let a = AmplitudeWeight::from_probability(p);
                let recovered = a.to_probability();
                assert!(
                    (recovered - p).abs() < 1e-12,
                    "roundtrip failed for p={p}: got {recovered}"
                );
            }
        }

        #[test]
        fn test_amplitude_ord_higher_probability_is_better() {
            let high = AmplitudeWeight::new(0.9, 0.0); // |z|² = 0.81
            let low = AmplitudeWeight::new(0.3, 0.0); // |z|² = 0.09
            // Higher norm_sqr should be "less" (better) in Ord
            assert!(high < low);
        }

        #[test]
        fn test_amplitude_detectable_zero() {
            let z = AmplitudeWeight::zero();
            assert!(z.is_zero());
            let nz = AmplitudeWeight::new(0.0, 1e-15);
            assert!(!nz.is_zero());
        }

        #[test]
        fn test_amplitude_hash_consistency() {
            use std::collections::hash_map::DefaultHasher;
            use std::hash::{Hash, Hasher};

            let a = AmplitudeWeight::new(1.0, -2.0);
            let b = AmplitudeWeight::new(1.0, -2.0);
            assert_eq!(a, b);
            let mut ha = DefaultHasher::new();
            let mut hb = DefaultHasher::new();
            a.hash(&mut ha);
            b.hash(&mut hb);
            assert_eq!(ha.finish(), hb.finish());
        }

        #[test]
        fn test_amplitude_display_debug() {
            let a = AmplitudeWeight::new(1.0, -0.5);
            let dbg = format!("{:?}", a);
            assert!(dbg.contains("AmplitudeWeight"));
            let disp = format!("{}", a);
            assert!(disp.contains("i"));
        }
    }

    #[cfg(all(feature = "quantum", feature = "wfst-log"))]
    mod amplitude_log_weight_tests {
        use super::super::*;

        #[test]
        fn test_amplitude_from_log_weight_roundtrip() {
            // LogWeight(0) = probability 1.0
            let lw = LogWeight::new(0.0);
            let a = AmplitudeWeight::from_log_weight(lw);
            assert!((a.to_probability() - 1.0).abs() < 1e-12);
        }

        #[test]
        fn test_amplitude_from_log_weight_half() {
            // LogWeight(-ln(0.5)) ≈ 0.6931
            let lw = LogWeight::from_probability(0.5);
            let a = AmplitudeWeight::from_log_weight(lw);
            assert!(
                (a.to_probability() - 0.5).abs() < 1e-10,
                "expected ~0.5, got {}",
                a.to_probability()
            );
        }

        #[test]
        fn test_amplitude_from_log_weight_zero_is_zero() {
            let lw = LogWeight::zero(); // +inf = probability 0
            let a = AmplitudeWeight::from_log_weight(lw);
            assert!(a.is_zero());
        }
    }

    // ════════════════════════════════════════════════════════════════════════
    // Proptest-based algebraic law verification for all semiring types
    // ════════════════════════════════════════════════════════════════════════
    //
    // Tests the 10 fundamental semiring laws:
    //   1. plus_associativity:    (a + b) + c == a + (b + c)
    //   2. times_associativity:   (a * b) * c == a * (b * c)
    //   3. plus_commutativity:    a + b == b + a
    //   4. plus_identity:         a + 0 == a
    //   5. times_left_identity:   1 * a == a
    //   6. times_right_identity:  a * 1 == a
    //   7. left_annihilation:     0 * a == 0
    //   8. right_annihilation:    a * 0 == 0
    //   9. left_distributivity:   a * (b + c) == (a * b) + (a * c)
    //  10. right_distributivity:  (a + b) * c == (a * c) + (b * c)
    //
    // Each type is tested with 300 randomly generated inputs per law.

    /// Generates proptest-based algebraic law tests for a semiring type.
    ///
    /// The macro generates a submodule containing proptest functions for all
    /// 10 semiring laws (8 core + 2 distributivity).
    macro_rules! semiring_law_tests {
        ($mod_name:ident, $type:ty, $arb:expr) => {
            mod $mod_name {
                use super::super::*;
                use proptest::prelude::*;

                proptest! {
                    #![proptest_config(ProptestConfig::with_cases(300))]

                    // Law 1: Plus associativity — (a + b) + c == a + (b + c)
                    #[test]
                    fn plus_associativity(a in $arb, b in $arb, c in $arb) {
                        let ab_c = a.plus(&b).plus(&c);
                        let a_bc = a.plus(&b.plus(&c));
                        prop_assert!(ab_c.approx_eq(&a_bc, 1e-10),
                            "({:?} + {:?}) + {:?} = {:?}  !=  {:?} = {:?} + ({:?} + {:?})",
                            a, b, c, ab_c, a_bc, a, b, c);
                    }

                    // Law 2: Times associativity — (a * b) * c == a * (b * c)
                    #[test]
                    fn times_associativity(a in $arb, b in $arb, c in $arb) {
                        let ab_c = a.times(&b).times(&c);
                        let a_bc = a.times(&b.times(&c));
                        prop_assert!(ab_c.approx_eq(&a_bc, 1e-10),
                            "({:?} * {:?}) * {:?} = {:?}  !=  {:?} = {:?} * ({:?} * {:?})",
                            a, b, c, ab_c, a_bc, a, b, c);
                    }

                    // Law 3: Plus commutativity — a + b == b + a
                    #[test]
                    fn plus_commutativity(a in $arb, b in $arb) {
                        let ab = a.plus(&b);
                        let ba = b.plus(&a);
                        prop_assert!(ab.approx_eq(&ba, 1e-10),
                            "{:?} + {:?} = {:?}  !=  {:?} = {:?} + {:?}",
                            a, b, ab, ba, b, a);
                    }

                    // Law 4: Plus identity — a + 0 == a
                    #[test]
                    fn plus_identity(a in $arb) {
                        let z = <$type>::zero();
                        let a_plus_z = a.plus(&z);
                        let z_plus_a = z.plus(&a);
                        prop_assert!(a_plus_z.approx_eq(&a, 1e-10),
                            "{:?} + zero = {:?}  !=  {:?}", a, a_plus_z, a);
                        prop_assert!(z_plus_a.approx_eq(&a, 1e-10),
                            "zero + {:?} = {:?}  !=  {:?}", a, z_plus_a, a);
                    }

                    // Law 5: Times left identity — 1 * a == a
                    #[test]
                    fn times_left_identity(a in $arb) {
                        let one = <$type>::one();
                        let one_a = one.times(&a);
                        prop_assert!(one_a.approx_eq(&a, 1e-10),
                            "one * {:?} = {:?}  !=  {:?}", a, one_a, a);
                    }

                    // Law 6: Times right identity — a * 1 == a
                    #[test]
                    fn times_right_identity(a in $arb) {
                        let one = <$type>::one();
                        let a_one = a.times(&one);
                        prop_assert!(a_one.approx_eq(&a, 1e-10),
                            "{:?} * one = {:?}  !=  {:?}", a, a_one, a);
                    }

                    // Law 7: Left annihilation — 0 * a == 0
                    #[test]
                    fn left_annihilation(a in $arb) {
                        let z = <$type>::zero();
                        let z_a = z.times(&a);
                        prop_assert!(z_a.approx_eq(&z, 1e-10),
                            "zero * {:?} = {:?}  !=  zero = {:?}", a, z_a, z);
                    }

                    // Law 8: Right annihilation — a * 0 == 0
                    #[test]
                    fn right_annihilation(a in $arb) {
                        let z = <$type>::zero();
                        let a_z = a.times(&z);
                        prop_assert!(a_z.approx_eq(&z, 1e-10),
                            "{:?} * zero = {:?}  !=  zero = {:?}", a, a_z, z);
                    }

                    // Law 9: Left distributivity — a * (b + c) == (a * b) + (a * c)
                    #[test]
                    fn left_distributivity(a in $arb, b in $arb, c in $arb) {
                        let lhs = a.times(&b.plus(&c));
                        let rhs = a.times(&b).plus(&a.times(&c));
                        prop_assert!(lhs.approx_eq(&rhs, 1e-10),
                            "{:?} * ({:?} + {:?}) = {:?}  !=  {:?} = ({:?}*{:?}) + ({:?}*{:?})",
                            a, b, c, lhs, rhs, a, b, a, c);
                    }

                    // Law 10: Right distributivity — (a + b) * c == (a * c) + (b * c)
                    #[test]
                    fn right_distributivity(a in $arb, b in $arb, c in $arb) {
                        let lhs = a.plus(&b).times(&c);
                        let rhs = a.times(&c).plus(&b.times(&c));
                        prop_assert!(lhs.approx_eq(&rhs, 1e-10),
                            "({:?} + {:?}) * {:?} = {:?}  !=  {:?} = ({:?}*{:?}) + ({:?}*{:?})",
                            a, b, c, lhs, rhs, a, c, b, c);
                    }
                }
            }
        };
    }

    // TropicalWeight: (R+ union {+inf}, min, +, +inf, 0.0)
    // Non-negative values only to ensure star convergence and valid domain.
    semiring_law_tests!(
        tropical_laws,
        TropicalWeight,
        (0.0f64..1000.0).prop_map(TropicalWeight::new)
    );

    // CountingWeight: (N, +, *, 0, 1) with saturating arithmetic
    semiring_law_tests!(
        counting_laws,
        CountingWeight,
        (0u64..1000).prop_map(CountingWeight::new)
    );

    // BooleanWeight: ({false, true}, or, and, false, true)
    semiring_law_tests!(
        boolean_laws,
        BooleanWeight,
        proptest::bool::ANY.prop_map(BooleanWeight::new)
    );

    // EditWeight: (N union {inf}, min, +, inf, 0)
    // Capped at 50 to avoid overflow in saturating_add for 3-element products.
    semiring_law_tests!(
        edit_laws,
        EditWeight,
        (0u32..50).prop_map(EditWeight::new)
    );

    // ContextWeight: (P(Labels), union, intersection, empty, U)
    // Using small bitsets to keep tests fast.
    semiring_law_tests!(
        context_laws,
        ContextWeight,
        (any::<u64>(), any::<u64>()).prop_map(|(lo, hi)| ContextWeight::new(lo as u128 | ((hi as u128) << 64)))
    );

    // ComplexityWeight: (N union {inf}, min, max, inf, 0)
    // Bottleneck semiring: plus=min, times=max. Distributivity holds (lattice).
    semiring_law_tests!(
        complexity_laws,
        ComplexityWeight,
        (0u32..1000).prop_map(ComplexityWeight::new)
    );

    // ViterbiWeight: ([0,1], max, *, 0, 1)
    // Probabilities in [0,1]. Distributivity: a * max(b,c) = max(a*b, a*c)
    // holds for non-negative a.
    semiring_law_tests!(
        viterbi_laws,
        ViterbiWeight,
        (0.0f64..=1.0).prop_map(ViterbiWeight::new)
    );

    // ArcticWeight: (R union {-inf}, max, +, -inf, 0)
    // Uses finite non-positive values for star convergence compatibility,
    // but all laws hold for arbitrary finite values.
    semiring_law_tests!(
        arctic_laws,
        ArcticWeight,
        (-1000.0f64..1000.0).prop_map(ArcticWeight::new)
    );

    // FuzzyWeight: ([0,1], max, min, 0, 1)
    // Possibilistic semiring. Distributivity: min(a, max(b,c)) = max(min(a,b), min(a,c))
    // holds (lattice distributivity).
    semiring_law_tests!(
        fuzzy_laws,
        FuzzyWeight,
        (0.0f64..=1.0).prop_map(FuzzyWeight::new)
    );

    // ProductWeight<TropicalWeight, EditWeight>: component-wise operations
    // Tests that the product of two valid semirings is itself a valid semiring.
    semiring_law_tests!(
        product_tropical_edit_laws,
        ProductWeight<TropicalWeight, EditWeight>,
        ((0.0f64..1000.0).prop_map(TropicalWeight::new),
         (0u32..50).prop_map(EditWeight::new))
            .prop_map(|(t, e)| ProductWeight::new(t, e))
    );

    // ProductWeight<BooleanWeight, CountingWeight>: component-wise operations
    semiring_law_tests!(
        product_boolean_counting_laws,
        ProductWeight<BooleanWeight, CountingWeight>,
        (proptest::bool::ANY.prop_map(BooleanWeight::new),
         (0u64..1000).prop_map(CountingWeight::new))
            .prop_map(|(b, c)| ProductWeight::new(b, c))
    );

    // ── TruncationWeight special handling ────────────────────────────────
    //
    // TruncationWeight<K> has zero() == one() == TruncationWeight(0), which
    // means it is NOT a proper semiring in the strict algebraic sense:
    //   - Left/right annihilation fails: zero * a = min(0 + a, K) = a != 0
    //   - The fact that zero == one conflates additive and multiplicative
    //     identities, which is only valid in the trivial ring {0}.
    //
    // However, the remaining laws (associativity, commutativity, identity,
    // distributivity) DO hold. We test those individually.
    mod truncation_laws {
        use super::super::*;
        use proptest::prelude::*;

        proptest! {
            #![proptest_config(ProptestConfig::with_cases(300))]

            // Law 1: Plus associativity
            #[test]
            fn plus_associativity(
                a in (0u32..8).prop_map(TruncationWeight::<8>::new),
                b in (0u32..8).prop_map(TruncationWeight::<8>::new),
                c in (0u32..8).prop_map(TruncationWeight::<8>::new),
            ) {
                let ab_c = a.plus(&b).plus(&c);
                let a_bc = a.plus(&b.plus(&c));
                prop_assert!(ab_c.approx_eq(&a_bc, 1e-10),
                    "plus_assoc: ({:?} + {:?}) + {:?} = {:?}  !=  {:?}", a, b, c, ab_c, a_bc);
            }

            // Law 2: Times associativity
            #[test]
            fn times_associativity(
                a in (0u32..4).prop_map(TruncationWeight::<8>::new),
                b in (0u32..4).prop_map(TruncationWeight::<8>::new),
                c in (0u32..4).prop_map(TruncationWeight::<8>::new),
            ) {
                let ab_c = a.times(&b).times(&c);
                let a_bc = a.times(&b.times(&c));
                prop_assert!(ab_c.approx_eq(&a_bc, 1e-10),
                    "times_assoc: ({:?} * {:?}) * {:?} = {:?}  !=  {:?}", a, b, c, ab_c, a_bc);
            }

            // Law 3: Plus commutativity
            #[test]
            fn plus_commutativity(
                a in (0u32..8).prop_map(TruncationWeight::<8>::new),
                b in (0u32..8).prop_map(TruncationWeight::<8>::new),
            ) {
                let ab = a.plus(&b);
                let ba = b.plus(&a);
                prop_assert!(ab.approx_eq(&ba, 1e-10),
                    "plus_comm: {:?} + {:?} = {:?}  !=  {:?}", a, b, ab, ba);
            }

            // Law 4: Plus identity — a + 0 == a
            // NOTE: zero() == TruncationWeight(0) and plus = max, so
            // max(a, 0) = a for all a >= 0. This holds.
            #[test]
            fn plus_identity(
                a in (0u32..8).prop_map(TruncationWeight::<8>::new),
            ) {
                let z = TruncationWeight::<8>::zero();
                let a_z = a.plus(&z);
                let z_a = z.plus(&a);
                prop_assert!(a_z.approx_eq(&a, 1e-10),
                    "plus_id: {:?} + zero = {:?}  !=  {:?}", a, a_z, a);
                prop_assert!(z_a.approx_eq(&a, 1e-10),
                    "plus_id: zero + {:?} = {:?}  !=  {:?}", a, z_a, a);
            }

            // Law 5+6: Times identity — 1 * a == a and a * 1 == a
            // one() = TruncationWeight(0), times = min(a+b, K).
            // one * a = min(0 + a.0, K) = a (since a.0 <= K). Holds.
            #[test]
            fn times_identity(
                a in (0u32..8).prop_map(TruncationWeight::<8>::new),
            ) {
                let one = TruncationWeight::<8>::one();
                let one_a = one.times(&a);
                let a_one = a.times(&one);
                prop_assert!(one_a.approx_eq(&a, 1e-10),
                    "times_left_id: one * {:?} = {:?}  !=  {:?}", a, one_a, a);
                prop_assert!(a_one.approx_eq(&a, 1e-10),
                    "times_right_id: {:?} * one = {:?}  !=  {:?}", a, a_one, a);
            }

            // Laws 7+8 (annihilation) SKIPPED: zero == one == TruncationWeight(0),
            // so zero * a = min(0 + a, K) = a, not zero. Annihilation fails
            // because the additive and multiplicative identities coincide at 0,
            // yet the "annihilator" should send everything to 0 under times.

            // Laws 9+10: Distributivity
            // a * (b + c) = min(a + max(b, c), K)
            // (a*b) + (a*c) = max(min(a+b, K), min(a+c, K))
            // These are equal when a+max(b,c) <= K and a+min(b,c) <= K,
            // but can differ near the saturation boundary.
            // Use small values to stay below K=8.
            #[test]
            fn left_distributivity(
                a in (0u32..3).prop_map(TruncationWeight::<8>::new),
                b in (0u32..3).prop_map(TruncationWeight::<8>::new),
                c in (0u32..3).prop_map(TruncationWeight::<8>::new),
            ) {
                let lhs = a.times(&b.plus(&c));
                let rhs = a.times(&b).plus(&a.times(&c));
                prop_assert!(lhs.approx_eq(&rhs, 1e-10),
                    "left_dist: {:?} * ({:?} + {:?}) = {:?}  !=  {:?}", a, b, c, lhs, rhs);
            }

            #[test]
            fn right_distributivity(
                a in (0u32..3).prop_map(TruncationWeight::<8>::new),
                b in (0u32..3).prop_map(TruncationWeight::<8>::new),
                c in (0u32..3).prop_map(TruncationWeight::<8>::new),
            ) {
                let lhs = a.plus(&b).times(&c);
                let rhs = a.times(&c).plus(&b.times(&c));
                prop_assert!(lhs.approx_eq(&rhs, 1e-10),
                    "right_dist: ({:?} + {:?}) * {:?} = {:?}  !=  {:?}", a, b, c, lhs, rhs);
            }
        }
    }

    // ── Additional type-specific proptest properties ─────────────────────

    mod idempotent_plus_tests {
        use super::super::*;
        use proptest::prelude::*;

        proptest! {
            #![proptest_config(ProptestConfig::with_cases(300))]

            // TropicalWeight is idempotent: a + a == a (min(a, a) = a)
            #[test]
            fn prop_tropical_idempotent_plus(
                a in (0.0f64..1000.0).prop_map(TropicalWeight::new),
            ) {
                prop_assert!(a.plus(&a).approx_eq(&a, 1e-10),
                    "tropical idempotent: {:?} + {:?} = {:?}  !=  {:?}",
                    a, a, a.plus(&a), a);
            }

            // BooleanWeight is idempotent: a + a == a (a || a = a)
            #[test]
            fn prop_boolean_idempotent_plus(
                a in proptest::bool::ANY.prop_map(BooleanWeight::new),
            ) {
                prop_assert!(a.plus(&a).approx_eq(&a, 1e-10),
                    "boolean idempotent: {:?} + {:?} = {:?}  !=  {:?}",
                    a, a, a.plus(&a), a);
            }

            // EditWeight is idempotent: a + a == a (min(a, a) = a)
            #[test]
            fn prop_edit_idempotent_plus(
                a in (0u32..50).prop_map(EditWeight::new),
            ) {
                prop_assert!(a.plus(&a).approx_eq(&a, 1e-10),
                    "edit idempotent: {:?} + {:?} = {:?}  !=  {:?}",
                    a, a, a.plus(&a), a);
            }

            // ContextWeight is idempotent: a + a == a (a | a = a)
            #[test]
            fn prop_context_idempotent_plus(
                a in any::<u128>().prop_map(ContextWeight::new),
            ) {
                prop_assert!(a.plus(&a).approx_eq(&a, 1e-10),
                    "context idempotent: {:?} + {:?} = {:?}  !=  {:?}",
                    a, a, a.plus(&a), a);
            }

            // ComplexityWeight is idempotent: a + a == a (min(a, a) = a)
            #[test]
            fn prop_complexity_idempotent_plus(
                a in (0u32..1000).prop_map(ComplexityWeight::new),
            ) {
                prop_assert!(a.plus(&a).approx_eq(&a, 1e-10),
                    "complexity idempotent: {:?} + {:?} = {:?}  !=  {:?}",
                    a, a, a.plus(&a), a);
            }

            // ViterbiWeight is idempotent: a + a == a (max(a, a) = a)
            #[test]
            fn prop_viterbi_idempotent_plus(
                a in (0.0f64..=1.0).prop_map(ViterbiWeight::new),
            ) {
                prop_assert!(a.plus(&a).approx_eq(&a, 1e-10),
                    "viterbi idempotent: {:?} + {:?} = {:?}  !=  {:?}",
                    a, a, a.plus(&a), a);
            }

            // ArcticWeight is idempotent: a + a == a (max(a, a) = a)
            #[test]
            fn prop_arctic_idempotent_plus(
                a in (-1000.0f64..1000.0).prop_map(ArcticWeight::new),
            ) {
                prop_assert!(a.plus(&a).approx_eq(&a, 1e-10),
                    "arctic idempotent: {:?} + {:?} = {:?}  !=  {:?}",
                    a, a, a.plus(&a), a);
            }

            // FuzzyWeight is idempotent: a + a == a (max(a, a) = a)
            #[test]
            fn prop_fuzzy_idempotent_plus(
                a in (0.0f64..=1.0).prop_map(FuzzyWeight::new),
            ) {
                prop_assert!(a.plus(&a).approx_eq(&a, 1e-10),
                    "fuzzy idempotent: {:?} + {:?} = {:?}  !=  {:?}",
                    a, a, a.plus(&a), a);
            }

            // TruncationWeight is idempotent: a + a == a (max(a, a) = a)
            #[test]
            fn prop_truncation_idempotent_plus(
                a in (0u32..8).prop_map(TruncationWeight::<8>::new),
            ) {
                prop_assert!(a.plus(&a).approx_eq(&a, 1e-10),
                    "truncation idempotent: {:?} + {:?} = {:?}  !=  {:?}",
                    a, a, a.plus(&a), a);
            }
        }
    }

    mod star_fixpoint_tests {
        use super::super::*;
        use proptest::prelude::*;

        proptest! {
            #![proptest_config(ProptestConfig::with_cases(300))]

            // Star fixpoint for TropicalWeight:
            // a.star() should satisfy: a* = 1 + a * a*
            // For non-negative TropicalWeight, star(a) = one = 0.0.
            // Then 1 + a * a* = min(0.0, a + 0.0) = min(0.0, a) = 0.0 for a >= 0.
            #[test]
            fn prop_star_fixpoint_tropical(
                a in (0.0f64..100.0).prop_map(TropicalWeight::new),
            ) {
                let star_a = a.star();
                let rhs = TropicalWeight::one().plus(&a.times(&star_a));
                prop_assert!(star_a.approx_eq(&rhs, 1e-10),
                    "star fixpoint: star({:?}) = {:?}  !=  1 + {:?} * star({:?}) = {:?}",
                    a, star_a, a, a, rhs);
            }

            // Star fixpoint for BooleanWeight:
            // star(a) = true for all a. 1 + a * star(a) = true || (a && true) = true.
            #[test]
            fn prop_star_fixpoint_boolean(
                a in proptest::bool::ANY.prop_map(BooleanWeight::new),
            ) {
                let star_a = a.star();
                let rhs = BooleanWeight::one().plus(&a.times(&star_a));
                prop_assert!(star_a.approx_eq(&rhs, 1e-10),
                    "star fixpoint: star({:?}) = {:?}  !=  {:?}", a, star_a, rhs);
            }

            // Star fixpoint for EditWeight:
            // star(a) = one = EditWeight(0). 1 + a * a* = min(0, a + 0) = 0.
            #[test]
            fn prop_star_fixpoint_edit(
                a in (0u32..50).prop_map(EditWeight::new),
            ) {
                let star_a = a.star();
                let rhs = EditWeight::one().plus(&a.times(&star_a));
                prop_assert!(star_a.approx_eq(&rhs, 1e-10),
                    "star fixpoint: star({:?}) = {:?}  !=  {:?}", a, star_a, rhs);
            }

            // Star fixpoint for ViterbiWeight:
            // star(a) = 1.0. 1 + a * a* = max(1.0, a * 1.0) = max(1.0, a) = 1.0
            // since a in [0,1].
            #[test]
            fn prop_star_fixpoint_viterbi(
                a in (0.0f64..=1.0).prop_map(ViterbiWeight::new),
            ) {
                let star_a = a.star();
                let rhs = ViterbiWeight::one().plus(&a.times(&star_a));
                prop_assert!(star_a.approx_eq(&rhs, 1e-10),
                    "star fixpoint: star({:?}) = {:?}  !=  {:?}", a, star_a, rhs);
            }

            // Star fixpoint for ArcticWeight (non-positive values):
            // star(a) = one = 0.0 for a <= 0.
            // 1 + a * a* = max(0.0, a + 0.0) = max(0.0, a) = 0.0 for a <= 0.
            #[test]
            fn prop_star_fixpoint_arctic(
                a in (-100.0f64..=0.0).prop_map(ArcticWeight::new),
            ) {
                let star_a = a.star();
                let rhs = ArcticWeight::one().plus(&a.times(&star_a));
                prop_assert!(star_a.approx_eq(&rhs, 1e-10),
                    "star fixpoint: star({:?}) = {:?}  !=  {:?}", a, star_a, rhs);
            }

            // Star fixpoint for FuzzyWeight:
            // star(a) = 1.0. 1 + a * a* = max(1.0, min(a, 1.0)) = 1.0.
            #[test]
            fn prop_star_fixpoint_fuzzy(
                a in (0.0f64..=1.0).prop_map(FuzzyWeight::new),
            ) {
                let star_a = a.star();
                let rhs = FuzzyWeight::one().plus(&a.times(&star_a));
                prop_assert!(star_a.approx_eq(&rhs, 1e-10),
                    "star fixpoint: star({:?}) = {:?}  !=  {:?}", a, star_a, rhs);
            }

            // Star fixpoint for ComplexityWeight:
            // star(a) = one = ComplexityWeight(0).
            // 1 + a * a* = min(0, max(a.0, 0)) = min(0, a.0) = 0 for a.0 >= 0.
            // Wait: min(0, max(a.0, 0)) = min(0, a.0) only if a.0 >= 0,
            // but max(a.0, 0) = a.0 for a.0 >= 0. And min(0, a.0) = 0 for a.0 >= 0.
            // Actually: 1 + a * a* where + is min and * is max:
            //   a * a* = max(a.0, 0) = a.0 for a.0 >= 0
            //   1 + (a * a*) = min(0, a.0) = 0 for a.0 >= 0
            // So a* = 0 == one. And rhs = 0 == one. They match.
            #[test]
            fn prop_star_fixpoint_complexity(
                a in (0u32..1000).prop_map(ComplexityWeight::new),
            ) {
                let star_a = a.star();
                let rhs = ComplexityWeight::one().plus(&a.times(&star_a));
                prop_assert!(star_a.approx_eq(&rhs, 1e-10),
                    "star fixpoint: star({:?}) = {:?}  !=  {:?}", a, star_a, rhs);
            }

            // Star fixpoint for ContextWeight:
            // star(a) = one = U (all bits set).
            // 1 + a * a* = U | (a & U) = U | a = U. Matches.
            #[test]
            fn prop_star_fixpoint_context(
                a in any::<u128>().prop_map(ContextWeight::new),
            ) {
                let star_a = a.star();
                let rhs = ContextWeight::one().plus(&a.times(&star_a));
                prop_assert!(star_a.approx_eq(&rhs, 1e-10),
                    "star fixpoint: star({:?}) = {:?}  !=  {:?}", a, star_a, rhs);
            }
        }
    }

    // ── Feature-gated proptest suites ────────────────────────────────────

    #[cfg(feature = "wfst-log")]
    mod log_weight_proptest_laws {
        use super::super::*;
        use proptest::prelude::*;

        proptest! {
            #![proptest_config(ProptestConfig::with_cases(300))]

            // Law 1: Plus associativity for LogWeight
            #[test]
            fn plus_associativity(
                a in (0.0f64..100.0).prop_map(LogWeight::new),
                b in (0.0f64..100.0).prop_map(LogWeight::new),
                c in (0.0f64..100.0).prop_map(LogWeight::new),
            ) {
                let ab_c = a.plus(&b).plus(&c);
                let a_bc = a.plus(&b.plus(&c));
                prop_assert!(ab_c.approx_eq(&a_bc, 1e-8),
                    "log plus_assoc: ({:?} + {:?}) + {:?} = {:?}  !=  {:?}",
                    a, b, c, ab_c, a_bc);
            }

            // Law 2: Times associativity for LogWeight
            #[test]
            fn times_associativity(
                a in (0.0f64..100.0).prop_map(LogWeight::new),
                b in (0.0f64..100.0).prop_map(LogWeight::new),
                c in (0.0f64..100.0).prop_map(LogWeight::new),
            ) {
                let ab_c = a.times(&b).times(&c);
                let a_bc = a.times(&b.times(&c));
                prop_assert!(ab_c.approx_eq(&a_bc, 1e-10),
                    "log times_assoc: ({:?} * {:?}) * {:?} = {:?}  !=  {:?}",
                    a, b, c, ab_c, a_bc);
            }

            // Law 3: Plus commutativity for LogWeight
            #[test]
            fn plus_commutativity(
                a in (0.0f64..100.0).prop_map(LogWeight::new),
                b in (0.0f64..100.0).prop_map(LogWeight::new),
            ) {
                let ab = a.plus(&b);
                let ba = b.plus(&a);
                prop_assert!(ab.approx_eq(&ba, 1e-10),
                    "log plus_comm: {:?} + {:?} = {:?}  !=  {:?}", a, b, ab, ba);
            }

            // Law 4: Plus identity
            #[test]
            fn plus_identity(a in (0.0f64..100.0).prop_map(LogWeight::new)) {
                let z = LogWeight::zero();
                prop_assert!(a.plus(&z).approx_eq(&a, 1e-10),
                    "log plus_id right: {:?}", a);
                prop_assert!(z.plus(&a).approx_eq(&a, 1e-10),
                    "log plus_id left: {:?}", a);
            }

            // Law 5: Times left identity
            #[test]
            fn times_left_identity(a in (0.0f64..100.0).prop_map(LogWeight::new)) {
                let one = LogWeight::one();
                prop_assert!(one.times(&a).approx_eq(&a, 1e-10),
                    "log times_left_id: {:?}", a);
            }

            // Law 6: Times right identity
            #[test]
            fn times_right_identity(a in (0.0f64..100.0).prop_map(LogWeight::new)) {
                let one = LogWeight::one();
                prop_assert!(a.times(&one).approx_eq(&a, 1e-10),
                    "log times_right_id: {:?}", a);
            }

            // Law 7: Left annihilation
            #[test]
            fn left_annihilation(a in (0.0f64..100.0).prop_map(LogWeight::new)) {
                let z = LogWeight::zero();
                let result = z.times(&a);
                prop_assert!(result.is_zero(),
                    "log left_annih: zero * {:?} = {:?}", a, result);
            }

            // Law 8: Right annihilation
            #[test]
            fn right_annihilation(a in (0.0f64..100.0).prop_map(LogWeight::new)) {
                let z = LogWeight::zero();
                let result = a.times(&z);
                prop_assert!(result.is_zero(),
                    "log right_annih: {:?} * zero = {:?}", a, result);
            }

            // Law 9: Left distributivity
            // LogWeight times is +, plus is log-sum-exp.
            // a * (b + c) = a + logsumexp(b, c)
            // (a*b) + (a*c) = logsumexp(a+b, a+c)
            // These are equal because logsumexp(a+b, a+c) = a + logsumexp(b, c).
            #[test]
            fn left_distributivity(
                a in (0.0f64..50.0).prop_map(LogWeight::new),
                b in (0.0f64..50.0).prop_map(LogWeight::new),
                c in (0.0f64..50.0).prop_map(LogWeight::new),
            ) {
                let lhs = a.times(&b.plus(&c));
                let rhs = a.times(&b).plus(&a.times(&c));
                prop_assert!(lhs.approx_eq(&rhs, 1e-8),
                    "log left_dist: {:?} * ({:?} + {:?}) = {:?}  !=  {:?}",
                    a, b, c, lhs, rhs);
            }

            // Law 10: Right distributivity
            #[test]
            fn right_distributivity(
                a in (0.0f64..50.0).prop_map(LogWeight::new),
                b in (0.0f64..50.0).prop_map(LogWeight::new),
                c in (0.0f64..50.0).prop_map(LogWeight::new),
            ) {
                let lhs = a.plus(&b).times(&c);
                let rhs = a.times(&c).plus(&b.times(&c));
                prop_assert!(lhs.approx_eq(&rhs, 1e-8),
                    "log right_dist: ({:?} + {:?}) * {:?} = {:?}  !=  {:?}",
                    a, b, c, lhs, rhs);
            }

            // LogWeight is NOT idempotent: a + a != a
            // Verify: logsumexp(a, a) = a - ln(2) != a
            #[test]
            fn non_idempotent_plus(
                a in (0.1f64..50.0).prop_map(LogWeight::new),
            ) {
                let aa = a.plus(&a);
                // a + a = a - ln(2) in log space
                let expected_value = a.0 - 2.0_f64.ln();
                prop_assert!(aa.approx_eq(&LogWeight::new(expected_value), 1e-10),
                    "log non-idempotent: {:?} + {:?} = {:?}, expected LogWeight({:.4})",
                    a, a, aa, expected_value);
            }

            // Star fixpoint: star(a) ≈ 1 + a * star(a) for a > 0
            #[test]
            fn star_fixpoint(
                a in (0.1f64..10.0).prop_map(LogWeight::new),
            ) {
                let star_a = a.star();
                let rhs = LogWeight::one().plus(&a.times(&star_a));
                prop_assert!(star_a.approx_eq(&rhs, 1e-4),
                    "log star fixpoint: star({:?}) = {:?}  !=  {:?}", a, star_a, rhs);
            }
        }
    }

    #[cfg(feature = "wfst-log")]
    mod entropy_weight_proptest_laws {
        use super::super::*;
        use proptest::prelude::*;

        proptest! {
            #![proptest_config(ProptestConfig::with_cases(300))]

            // Law 2: Times associativity for EntropyWeight
            #[test]
            fn times_associativity(
                a in (0.0f64..50.0, 0.0f64..50.0).prop_map(|(w, e)| EntropyWeight::new(w, e)),
                b in (0.0f64..50.0, 0.0f64..50.0).prop_map(|(w, e)| EntropyWeight::new(w, e)),
                c in (0.0f64..50.0, 0.0f64..50.0).prop_map(|(w, e)| EntropyWeight::new(w, e)),
            ) {
                let ab_c = a.times(&b).times(&c);
                let a_bc = a.times(&b.times(&c));
                prop_assert!(ab_c.approx_eq(&a_bc, 1e-8),
                    "entropy times_assoc: {:?} vs {:?}", ab_c, a_bc);
            }

            // Law 3: Plus commutativity for EntropyWeight
            #[test]
            fn plus_commutativity(
                a in (0.0f64..50.0, 0.0f64..50.0).prop_map(|(w, e)| EntropyWeight::new(w, e)),
                b in (0.0f64..50.0, 0.0f64..50.0).prop_map(|(w, e)| EntropyWeight::new(w, e)),
            ) {
                let ab = a.plus(&b);
                let ba = b.plus(&a);
                prop_assert!(ab.approx_eq(&ba, 1e-8),
                    "entropy plus_comm: {:?} + {:?} = {:?}  !=  {:?}", a, b, ab, ba);
            }

            // Law 4: Plus identity
            #[test]
            fn plus_identity(
                a in (0.0f64..50.0, 0.0f64..50.0).prop_map(|(w, e)| EntropyWeight::new(w, e)),
            ) {
                let z = EntropyWeight::zero();
                prop_assert!(a.plus(&z).approx_eq(&a, 1e-10),
                    "entropy plus_id right: {:?}", a);
                prop_assert!(z.plus(&a).approx_eq(&a, 1e-10),
                    "entropy plus_id left: {:?}", a);
            }

            // Law 5+6: Times identity
            #[test]
            fn times_identity(
                a in (0.0f64..50.0, 0.0f64..50.0).prop_map(|(w, e)| EntropyWeight::new(w, e)),
            ) {
                let one = EntropyWeight::one();
                prop_assert!(one.times(&a).approx_eq(&a, 1e-10),
                    "entropy times_left_id: {:?}", a);
                prop_assert!(a.times(&one).approx_eq(&a, 1e-10),
                    "entropy times_right_id: {:?}", a);
            }

            // Law 7+8: Annihilation
            // zero.times(a) should give zero.
            // zero = (inf, 0). zero.times(a) = (inf + a.w, 0 + a.e) = (inf, a.e).
            // But zero = (inf, 0.0) and is_zero checks weight == inf.
            // So the result is_zero() = true even though expectation differs.
            // approx_eq checks: both zero -> true. So this works.
            #[test]
            fn left_annihilation(
                a in (0.0f64..50.0, 0.0f64..50.0).prop_map(|(w, e)| EntropyWeight::new(w, e)),
            ) {
                let z = EntropyWeight::zero();
                let result = z.times(&a);
                prop_assert!(result.is_zero(),
                    "entropy left_annih: zero * {:?} = {:?}", a, result);
            }

            #[test]
            fn right_annihilation(
                a in (0.0f64..50.0, 0.0f64..50.0).prop_map(|(w, e)| EntropyWeight::new(w, e)),
            ) {
                let z = EntropyWeight::zero();
                let result = a.times(&z);
                prop_assert!(result.is_zero(),
                    "entropy right_annih: {:?} * zero = {:?}", a, result);
            }

            // Star fixpoint for EntropyWeight:
            // star(a) ≈ 1 + a * star(a)
            #[test]
            fn star_fixpoint(
                a in (0.5f64..10.0, 0.0f64..5.0).prop_map(|(w, e)| EntropyWeight::new(w, e)),
            ) {
                let star_a = a.star();
                if !star_a.is_zero() {
                    let rhs = EntropyWeight::one().plus(&a.times(&star_a));
                    prop_assert!(star_a.approx_eq(&rhs, 1e-4),
                        "entropy star fixpoint: star({:?}) = {:?}  !=  {:?}", a, star_a, rhs);
                }
            }
        }
    }

    #[cfg(feature = "quantum")]
    mod amplitude_weight_proptest_laws {
        use super::super::*;
        use proptest::prelude::*;

        proptest! {
            #![proptest_config(ProptestConfig::with_cases(300))]

            // Law 1: Plus associativity
            #[test]
            fn plus_associativity(
                a in (-10.0f64..10.0, -10.0f64..10.0).prop_map(|(r, i)| AmplitudeWeight::new(r, i)),
                b in (-10.0f64..10.0, -10.0f64..10.0).prop_map(|(r, i)| AmplitudeWeight::new(r, i)),
                c in (-10.0f64..10.0, -10.0f64..10.0).prop_map(|(r, i)| AmplitudeWeight::new(r, i)),
            ) {
                let ab_c = a.plus(&b).plus(&c);
                let a_bc = a.plus(&b.plus(&c));
                prop_assert!(ab_c.approx_eq(&a_bc, 1e-10),
                    "amplitude plus_assoc: {:?} vs {:?}", ab_c, a_bc);
            }

            // Law 2: Times associativity
            #[test]
            fn times_associativity(
                a in (-10.0f64..10.0, -10.0f64..10.0).prop_map(|(r, i)| AmplitudeWeight::new(r, i)),
                b in (-10.0f64..10.0, -10.0f64..10.0).prop_map(|(r, i)| AmplitudeWeight::new(r, i)),
                c in (-10.0f64..10.0, -10.0f64..10.0).prop_map(|(r, i)| AmplitudeWeight::new(r, i)),
            ) {
                let ab_c = a.times(&b).times(&c);
                let a_bc = a.times(&b.times(&c));
                prop_assert!(ab_c.approx_eq(&a_bc, 1e-8),
                    "amplitude times_assoc: {:?} vs {:?}", ab_c, a_bc);
            }

            // Law 3: Plus commutativity
            #[test]
            fn plus_commutativity(
                a in (-10.0f64..10.0, -10.0f64..10.0).prop_map(|(r, i)| AmplitudeWeight::new(r, i)),
                b in (-10.0f64..10.0, -10.0f64..10.0).prop_map(|(r, i)| AmplitudeWeight::new(r, i)),
            ) {
                let ab = a.plus(&b);
                let ba = b.plus(&a);
                prop_assert!(ab.approx_eq(&ba, 1e-10),
                    "amplitude plus_comm: {:?} vs {:?}", ab, ba);
            }

            // Law 4: Plus identity
            #[test]
            fn plus_identity(
                a in (-10.0f64..10.0, -10.0f64..10.0).prop_map(|(r, i)| AmplitudeWeight::new(r, i)),
            ) {
                let z = AmplitudeWeight::zero();
                prop_assert!(a.plus(&z).approx_eq(&a, 1e-10), "amplitude plus_id right");
                prop_assert!(z.plus(&a).approx_eq(&a, 1e-10), "amplitude plus_id left");
            }

            // Law 5: Times left identity
            #[test]
            fn times_left_identity(
                a in (-10.0f64..10.0, -10.0f64..10.0).prop_map(|(r, i)| AmplitudeWeight::new(r, i)),
            ) {
                let one = AmplitudeWeight::one();
                prop_assert!(one.times(&a).approx_eq(&a, 1e-10), "amplitude times_left_id");
            }

            // Law 6: Times right identity
            #[test]
            fn times_right_identity(
                a in (-10.0f64..10.0, -10.0f64..10.0).prop_map(|(r, i)| AmplitudeWeight::new(r, i)),
            ) {
                let one = AmplitudeWeight::one();
                prop_assert!(a.times(&one).approx_eq(&a, 1e-10), "amplitude times_right_id");
            }

            // Law 7: Left annihilation
            #[test]
            fn left_annihilation(
                a in (-10.0f64..10.0, -10.0f64..10.0).prop_map(|(r, i)| AmplitudeWeight::new(r, i)),
            ) {
                let z = AmplitudeWeight::zero();
                prop_assert!(z.times(&a).approx_eq(&z, 1e-10), "amplitude left_annih");
            }

            // Law 8: Right annihilation
            #[test]
            fn right_annihilation(
                a in (-10.0f64..10.0, -10.0f64..10.0).prop_map(|(r, i)| AmplitudeWeight::new(r, i)),
            ) {
                let z = AmplitudeWeight::zero();
                prop_assert!(a.times(&z).approx_eq(&z, 1e-10), "amplitude right_annih");
            }

            // Law 9: Left distributivity — holds for complex numbers (ring)
            #[test]
            fn left_distributivity(
                a in (-10.0f64..10.0, -10.0f64..10.0).prop_map(|(r, i)| AmplitudeWeight::new(r, i)),
                b in (-10.0f64..10.0, -10.0f64..10.0).prop_map(|(r, i)| AmplitudeWeight::new(r, i)),
                c in (-10.0f64..10.0, -10.0f64..10.0).prop_map(|(r, i)| AmplitudeWeight::new(r, i)),
            ) {
                let lhs = a.times(&b.plus(&c));
                let rhs = a.times(&b).plus(&a.times(&c));
                prop_assert!(lhs.approx_eq(&rhs, 1e-8),
                    "amplitude left_dist: {:?} vs {:?}", lhs, rhs);
            }

            // Law 10: Right distributivity
            #[test]
            fn right_distributivity(
                a in (-10.0f64..10.0, -10.0f64..10.0).prop_map(|(r, i)| AmplitudeWeight::new(r, i)),
                b in (-10.0f64..10.0, -10.0f64..10.0).prop_map(|(r, i)| AmplitudeWeight::new(r, i)),
                c in (-10.0f64..10.0, -10.0f64..10.0).prop_map(|(r, i)| AmplitudeWeight::new(r, i)),
            ) {
                let lhs = a.plus(&b).times(&c);
                let rhs = a.times(&c).plus(&b.times(&c));
                prop_assert!(lhs.approx_eq(&rhs, 1e-8),
                    "amplitude right_dist: {:?} vs {:?}", lhs, rhs);
            }
        }
    }
}
