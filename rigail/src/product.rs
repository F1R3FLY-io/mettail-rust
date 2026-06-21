use super::*;

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
        ProductWeight { left: S1::zero(), right: S2::zero() }
    }

    #[inline]
    fn one() -> Self {
        ProductWeight { left: S1::one(), right: S2::one() }
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
        self.left
            .cmp(&other.left)
            .then_with(|| self.right.cmp(&other.right))
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
        ProductWeight { left: S1::one(), right: S2::one() }
    }
}

impl<S1: DetectableZero, S2: DetectableZero> DetectableZero for ProductWeight<S1, S2> where
    ProductWeight<S1, S2>: Semiring
{
}

impl<S1: IdempotentSemiring, S2: IdempotentSemiring> IdempotentSemiring for ProductWeight<S1, S2> where
    ProductWeight<S1, S2>: Semiring
{
}

impl<S1: CompleteSemiring, S2: CompleteSemiring> CompleteSemiring for ProductWeight<S1, S2> where
    ProductWeight<S1, S2>: Semiring
{
}

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
