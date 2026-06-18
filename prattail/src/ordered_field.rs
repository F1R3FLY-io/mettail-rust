//! `OrderedFieldAlgebra<P>` — an effective Boolean algebra of **unbounded
//! interval unions** over any totally-ordered point type `P`.
//!
//! This generalizes [`IntervalAlgebra`](crate::symbolic::IntervalAlgebra) (which
//! is bounded to a fixed `[min, max)` `i64` universe) to:
//!
//! - **arbitrary-precision integers** (`num_bigint::BigInt`, discrete),
//! - **exact rationals** (`num_rational::BigRational`, dense — also the carrier
//!   for fixed-point decimals, whose value is exactly `unscaled / 10^places`),
//! - **floats** ([`OrderedF64`], a total order over `f64`),
//! - and bounded machine integers (`i128`, discrete) for completeness.
//!
//! prattail must **not** depend on `mettail-runtime` (that would cycle:
//! `runtime → prattail`), so the runtime's `CanonicalBigInt`/`CanonicalBigRat`/
//! `CanonicalFixedPoint` cannot appear here. Instead this module is generic over
//! an [`OrderedPoint`] trait and instantiated with prattail-native point types
//! (`BigInt`/`BigRational`/`OrderedF64`/`i128`). The codegen seam converts a
//! language's concrete numeric domain values to/from these point types.
//!
//! ## Endpoints, density, and the single oracle
//!
//! Predicates are normalized unions of intervals whose endpoints are
//! [`Bound`]s — `NegInf | PosInf | Incl(p) | Excl(p)` — so open/closed and
//! ±∞ are all representable. Structural ordering of endpoints
//! (sorting/overlap) is *dense* (position-based), but **emptiness, witness
//! generation, and gap detection route through the single density-aware oracle
//! [`OrderedPoint::witness_in`]**. That one method per point type is what makes
//! `not`/merge correct on *both* discrete and dense domains with shared code:
//! e.g. `[1,2] ∪ [3,4]` collapses to `[1,4]` over `BigInt` (no integer strictly
//! between 2 and 3) but stays split over `BigRational`.

use std::cmp::Ordering;
use std::fmt::Debug;
use std::hash::Hash;
use std::marker::PhantomData;

use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::One;

use crate::symbolic::BooleanAlgebra;

// ══════════════════════════════════════════════════════════════════════════════
// Bound
// ══════════════════════════════════════════════════════════════════════════════

/// An interval endpoint over a point type `P`.
///
/// As a *lower* bound: `NegInf` = unbounded below, `Incl(a)` = starts at `a`
/// (`x ≥ a`), `Excl(a)` = starts just above `a` (`x > a`), `PosInf` = an empty
/// start (never used in a non-empty interval). As an *upper* bound: dually.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Bound<P> {
    /// Unbounded below (−∞).
    NegInf,
    /// Unbounded above (+∞).
    PosInf,
    /// Closed endpoint at `p`.
    Incl(P),
    /// Open endpoint at `p`.
    Excl(P),
}

// ══════════════════════════════════════════════════════════════════════════════
// OrderedPoint
// ══════════════════════════════════════════════════════════════════════════════

/// A totally-ordered point type that knows how to **witness** an interval —
/// the single density-aware operation the algebra needs.
///
/// `witness_in(lo, hi)` returns some value lying within the interval whose lower
/// bound is `lo` and upper bound is `hi`, or `None` if the interval is empty
/// **for this domain**. A discrete domain (`BigInt`, `i128`) reports `(2, 3)`
/// (exclusive–exclusive) as empty; a dense domain (`BigRational`, `f64`) reports
/// it as non-empty (e.g. `2.5`). All other algebra operations are domain-generic
/// and delegate emptiness/gap questions here.
pub trait OrderedPoint: Clone + Debug + Eq + Hash + Ord + Send + Sync + 'static {
    /// A representative element of the interval `(lo, hi)` honoring the bounds'
    /// inclusivities, or `None` if the interval contains no element of this
    /// domain.
    fn witness_in(lo: &Bound<Self>, hi: &Bound<Self>) -> Option<Self>;
}

// ── i128 (discrete, bounded machine integer) ──────────────────────────────────

impl OrderedPoint for i128 {
    fn witness_in(lo: &Bound<i128>, hi: &Bound<i128>) -> Option<i128> {
        // Effective inclusive minimum implied by the lower bound, or None for −∞.
        let lo_min: Option<i128> = match lo {
            Bound::NegInf => None,
            Bound::Incl(a) => Some(*a),
            Bound::Excl(a) => Some(a.checked_add(1)?),
            Bound::PosInf => return None,
        };
        let hi_max: Option<i128> = match hi {
            Bound::PosInf => None,
            Bound::Incl(b) => Some(*b),
            Bound::Excl(b) => Some(b.checked_sub(1)?),
            Bound::NegInf => return None,
        };
        match (lo_min, hi_max) {
            (Some(a), Some(b)) => (a <= b).then_some(a),
            (Some(a), None) => Some(a),
            (None, Some(b)) => Some(b),
            (None, None) => Some(0),
        }
    }
}

// ── BigInt (discrete, arbitrary precision) ────────────────────────────────────

impl OrderedPoint for BigInt {
    fn witness_in(lo: &Bound<BigInt>, hi: &Bound<BigInt>) -> Option<BigInt> {
        let lo_min: Option<BigInt> = match lo {
            Bound::NegInf => None,
            Bound::Incl(a) => Some(a.clone()),
            Bound::Excl(a) => Some(a + BigInt::one()),
            Bound::PosInf => return None,
        };
        let hi_max: Option<BigInt> = match hi {
            Bound::PosInf => None,
            Bound::Incl(b) => Some(b.clone()),
            Bound::Excl(b) => Some(b - BigInt::one()),
            Bound::NegInf => return None,
        };
        match (lo_min, hi_max) {
            (Some(a), Some(b)) => (a <= b).then_some(a),
            (Some(a), None) => Some(a),
            (None, Some(b)) => Some(b),
            (None, None) => Some(BigInt::ZERO),
        }
    }
}

// ── BigRational (dense; also the carrier for fixed-point decimals) ────────────

impl OrderedPoint for BigRational {
    fn witness_in(lo: &Bound<BigRational>, hi: &Bound<BigRational>) -> Option<BigRational> {
        let two = || BigRational::from_integer(BigInt::from(2));
        let one = || BigRational::one();
        match (lo, hi) {
            (Bound::PosInf, _) | (_, Bound::NegInf) => None,
            (Bound::NegInf, Bound::PosInf) => Some(BigRational::from_integer(BigInt::ZERO)),
            (Bound::NegInf, Bound::Incl(b)) => Some(b.clone()),
            (Bound::NegInf, Bound::Excl(b)) => Some(b - one()),
            (Bound::Incl(a), Bound::PosInf) => Some(a.clone()),
            (Bound::Excl(a), Bound::PosInf) => Some(a + one()),
            (lo_b, hi_b) => {
                let (a, a_incl) = match lo_b {
                    Bound::Incl(a) => (a.clone(), true),
                    Bound::Excl(a) => (a.clone(), false),
                    _ => unreachable!("handled above"),
                };
                let (b, b_incl) = match hi_b {
                    Bound::Incl(b) => (b.clone(), true),
                    Bound::Excl(b) => (b.clone(), false),
                    _ => unreachable!("handled above"),
                };
                match a.cmp(&b) {
                    Ordering::Greater => None,
                    Ordering::Equal => (a_incl && b_incl).then_some(a),
                    // Dense: the midpoint is strictly between a and b, so it
                    // satisfies every open/closed combination.
                    Ordering::Less => Some((&a + &b) / two()),
                }
            },
        }
    }
}

// ── OrderedF64 (total order over f64) ─────────────────────────────────────────

/// A total order over `f64` (via [`f64::total_cmp`]), so floats can be a
/// [`OrderedPoint`]. `NaN` is ordered as the maximal element; `-0.0 < 0.0` is
/// flattened to equal by `total_cmp`'s usual convention is NOT used — we keep
/// `total_cmp` exactly, which distinguishes `-0.0 < +0.0`. Equality/hash are by
/// bit pattern so the type is `Eq + Hash`.
#[derive(Clone, Copy, Debug)]
pub struct OrderedF64(pub f64);

impl PartialEq for OrderedF64 {
    fn eq(&self, other: &Self) -> bool {
        self.0.total_cmp(&other.0) == Ordering::Equal
    }
}
impl Eq for OrderedF64 {}
impl Hash for OrderedF64 {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.0.to_bits().hash(state);
    }
}
impl PartialOrd for OrderedF64 {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}
impl Ord for OrderedF64 {
    fn cmp(&self, other: &Self) -> Ordering {
        self.0.total_cmp(&other.0)
    }
}

impl OrderedPoint for OrderedF64 {
    fn witness_in(lo: &Bound<OrderedF64>, hi: &Bound<OrderedF64>) -> Option<OrderedF64> {
        // Effective inclusive minimum / maximum, using next-representable floats
        // for exclusive bounds (exact: there is no float strictly between `x` and
        // `x.next_up()`).
        let lo_min: Option<f64> = match lo {
            Bound::NegInf => None,
            Bound::Incl(a) => Some(a.0),
            Bound::Excl(a) => Some(a.0.next_up()),
            Bound::PosInf => return None,
        };
        let hi_max: Option<f64> = match hi {
            Bound::PosInf => None,
            Bound::Incl(b) => Some(b.0),
            Bound::Excl(b) => Some(b.0.next_down()),
            Bound::NegInf => return None,
        };
        match (lo_min, hi_max) {
            (Some(a), Some(b)) => (a.total_cmp(&b) != Ordering::Greater).then_some(OrderedF64(a)),
            (Some(a), None) => Some(OrderedF64(a)),
            (None, Some(b)) => Some(OrderedF64(b)),
            (None, None) => Some(OrderedF64(0.0)),
        }
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// Endpoint comparison helpers (dense / position-based)
// ══════════════════════════════════════════════════════════════════════════════

/// Order two **lower** bounds: which one starts earlier (is the smaller start)?
fn cmp_lower<P: Ord>(a: &Bound<P>, b: &Bound<P>) -> Ordering {
    use Bound::*;
    match (a, b) {
        (NegInf, NegInf) => Ordering::Equal,
        (NegInf, _) => Ordering::Less,
        (_, NegInf) => Ordering::Greater,
        (PosInf, PosInf) => Ordering::Equal,
        (PosInf, _) => Ordering::Greater,
        (_, PosInf) => Ordering::Less,
        (Incl(x), Incl(y)) | (Excl(x), Excl(y)) => x.cmp(y),
        // At equal value, Incl(x) (starts AT x) is earlier than Excl(x) (starts after x).
        (Incl(x), Excl(y)) => x.cmp(y).then(Ordering::Less),
        (Excl(x), Incl(y)) => x.cmp(y).then(Ordering::Greater),
    }
}

/// Order two **upper** bounds: which one ends earlier (is the smaller end)?
fn cmp_upper<P: Ord>(a: &Bound<P>, b: &Bound<P>) -> Ordering {
    use Bound::*;
    match (a, b) {
        (PosInf, PosInf) => Ordering::Equal,
        (PosInf, _) => Ordering::Greater,
        (_, PosInf) => Ordering::Less,
        (NegInf, NegInf) => Ordering::Equal,
        (NegInf, _) => Ordering::Less,
        (_, NegInf) => Ordering::Greater,
        (Incl(x), Incl(y)) | (Excl(x), Excl(y)) => x.cmp(y),
        // At equal value, Incl(x) (ends AT x) is later than Excl(x) (ends before x).
        (Incl(x), Excl(y)) => x.cmp(y).then(Ordering::Greater),
        (Excl(x), Incl(y)) => x.cmp(y).then(Ordering::Less),
    }
}

/// Dense (position-based) test: could the interval `[lo, hi]` be non-empty?
/// (Discreteness is handled separately by [`OrderedPoint::witness_in`].)
fn pos_lower_le_upper<P: Ord>(lo: &Bound<P>, hi: &Bound<P>) -> bool {
    use Bound::*;
    match (lo, hi) {
        (NegInf, _) | (_, PosInf) => true,
        (PosInf, _) | (_, NegInf) => false,
        (Incl(x), Incl(y)) => x <= y,
        (Incl(x), Excl(y)) | (Excl(x), Incl(y)) | (Excl(x), Excl(y)) => x < y,
    }
}

/// The lower bound of the gap that begins just above this **upper** bound.
fn flip_upper_to_lower<P: Clone>(hi: &Bound<P>) -> Bound<P> {
    match hi {
        Bound::Incl(x) => Bound::Excl(x.clone()), // ends at x → gap is x+
        Bound::Excl(x) => Bound::Incl(x.clone()), // ends before x → gap is [x
        Bound::PosInf => Bound::PosInf,
        Bound::NegInf => Bound::NegInf,
    }
}

/// The upper bound of the gap that ends just below this **lower** bound.
fn flip_lower_to_upper<P: Clone>(lo: &Bound<P>) -> Bound<P> {
    match lo {
        Bound::Incl(x) => Bound::Excl(x.clone()), // starts at x → gap is x)
        Bound::Excl(x) => Bound::Incl(x.clone()), // starts after x → gap is x]
        Bound::NegInf => Bound::NegInf,
        Bound::PosInf => Bound::PosInf,
    }
}

/// Whether the element `x` is at or above the lower bound `lo`.
fn lower_contains<P: Ord>(lo: &Bound<P>, x: &P) -> bool {
    match lo {
        Bound::NegInf => true,
        Bound::Incl(a) => x >= a,
        Bound::Excl(a) => x > a,
        Bound::PosInf => false,
    }
}

/// Whether the element `x` is at or below the upper bound `hi`.
fn upper_contains<P: Ord>(hi: &Bound<P>, x: &P) -> bool {
    match hi {
        Bound::PosInf => true,
        Bound::Incl(b) => x <= b,
        Bound::Excl(b) => x < b,
        Bound::NegInf => false,
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// OrderedFieldPred
// ══════════════════════════════════════════════════════════════════════════════

/// A predicate over `P`: a normalized (sorted, disjoint, maximally-merged) union
/// of intervals. The empty `Vec` is `⊥`; `[(NegInf, PosInf)]` is `⊤`.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct OrderedFieldPred<P> {
    intervals: Vec<(Bound<P>, Bound<P>)>,
}

impl<P: OrderedPoint> OrderedFieldPred<P> {
    /// The everywhere-true predicate.
    pub fn top() -> Self {
        OrderedFieldPred {
            intervals: vec![(Bound::NegInf, Bound::PosInf)],
        }
    }

    /// The everywhere-false predicate.
    pub fn bottom() -> Self {
        OrderedFieldPred { intervals: Vec::new() }
    }

    /// A single closed range `[lo, hi]`.
    pub fn closed(lo: P, hi: P) -> Self {
        OrderedFieldPred::from_intervals(vec![(Bound::Incl(lo), Bound::Incl(hi))])
    }

    /// A single half-open range `[lo, hi)`.
    pub fn half_open(lo: P, hi: P) -> Self {
        OrderedFieldPred::from_intervals(vec![(Bound::Incl(lo), Bound::Excl(hi))])
    }

    /// `{ x | x ≥ lo }`.
    pub fn at_least(lo: P) -> Self {
        OrderedFieldPred::from_intervals(vec![(Bound::Incl(lo), Bound::PosInf)])
    }

    /// `{ x | x ≤ hi }`.
    pub fn at_most(hi: P) -> Self {
        OrderedFieldPred::from_intervals(vec![(Bound::NegInf, Bound::Incl(hi))])
    }

    /// The singleton `{ p }`.
    pub fn point(p: P) -> Self {
        OrderedFieldPred::from_intervals(vec![(Bound::Incl(p.clone()), Bound::Incl(p))])
    }

    /// Build a normalized predicate from raw intervals.
    pub fn from_intervals(mut raw: Vec<(Bound<P>, Bound<P>)>) -> Self {
        // Drop intervals that are empty for this domain (density-aware).
        raw.retain(|(lo, hi)| P::witness_in(lo, hi).is_some());
        raw.sort_by(|a, b| cmp_lower(&a.0, &b.0).then_with(|| cmp_upper(&a.1, &b.1)));
        let mut merged: Vec<(Bound<P>, Bound<P>)> = Vec::with_capacity(raw.len());
        for iv in raw {
            if let Some(last) = merged.last_mut() {
                let overlaps = pos_lower_le_upper(&iv.0, &last.1);
                let gap_empty =
                    P::witness_in(&flip_upper_to_lower(&last.1), &flip_lower_to_upper(&iv.0))
                        .is_none();
                if overlaps || gap_empty {
                    if cmp_upper(&iv.1, &last.1) == Ordering::Greater {
                        last.1 = iv.1;
                    }
                    continue;
                }
            }
            merged.push(iv);
        }
        OrderedFieldPred { intervals: merged }
    }

    fn intersect(&self, other: &Self) -> Self {
        let mut out = Vec::new();
        for a in &self.intervals {
            for b in &other.intervals {
                let lo = if cmp_lower(&a.0, &b.0) == Ordering::Greater {
                    a.0.clone()
                } else {
                    b.0.clone()
                };
                let hi = if cmp_upper(&a.1, &b.1) == Ordering::Less {
                    a.1.clone()
                } else {
                    b.1.clone()
                };
                if pos_lower_le_upper(&lo, &hi) {
                    out.push((lo, hi));
                }
            }
        }
        OrderedFieldPred::from_intervals(out)
    }

    fn union(&self, other: &Self) -> Self {
        let mut out = self.intervals.clone();
        out.extend(other.intervals.iter().cloned());
        OrderedFieldPred::from_intervals(out)
    }

    fn complement(&self) -> Self {
        // `self.intervals` is normalized (sorted, disjoint). Walk the gaps.
        let mut out = Vec::new();
        let mut cursor: Bound<P> = Bound::NegInf;
        for (lo, hi) in &self.intervals {
            if !matches!(lo, Bound::NegInf) {
                let gap_hi = flip_lower_to_upper(lo);
                out.push((cursor.clone(), gap_hi));
            }
            if matches!(hi, Bound::PosInf) {
                cursor = Bound::PosInf;
            } else {
                cursor = flip_upper_to_lower(hi);
            }
        }
        if !matches!(cursor, Bound::PosInf) {
            out.push((cursor, Bound::PosInf));
        }
        OrderedFieldPred::from_intervals(out)
    }

    fn contains(&self, x: &P) -> bool {
        self.intervals
            .iter()
            .any(|(lo, hi)| lower_contains(lo, x) && upper_contains(hi, x))
    }

    fn first_witness(&self) -> Option<P> {
        self.intervals
            .iter()
            .find_map(|(lo, hi)| P::witness_in(lo, hi))
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// OrderedFieldAlgebra
// ══════════════════════════════════════════════════════════════════════════════

/// The effective Boolean algebra of interval unions over `P`. Zero-sized — the
/// universe is the whole (unbounded) domain `P`.
#[derive(Clone, Debug)]
pub struct OrderedFieldAlgebra<P>(PhantomData<fn() -> P>);

impl<P: OrderedPoint> OrderedFieldAlgebra<P> {
    /// Construct the algebra.
    pub fn new() -> Self {
        OrderedFieldAlgebra(PhantomData)
    }
}

impl<P: OrderedPoint> Default for OrderedFieldAlgebra<P> {
    fn default() -> Self {
        OrderedFieldAlgebra::new()
    }
}

impl<P: OrderedPoint> BooleanAlgebra for OrderedFieldAlgebra<P> {
    type Predicate = OrderedFieldPred<P>;
    type Domain = P;

    fn true_pred(&self) -> OrderedFieldPred<P> {
        OrderedFieldPred::top()
    }

    fn false_pred(&self) -> OrderedFieldPred<P> {
        OrderedFieldPred::bottom()
    }

    fn and(&self, a: &OrderedFieldPred<P>, b: &OrderedFieldPred<P>) -> OrderedFieldPred<P> {
        a.intersect(b)
    }

    fn or(&self, a: &OrderedFieldPred<P>, b: &OrderedFieldPred<P>) -> OrderedFieldPred<P> {
        a.union(b)
    }

    fn not(&self, a: &OrderedFieldPred<P>) -> OrderedFieldPred<P> {
        a.complement()
    }

    fn is_satisfiable(&self, a: &OrderedFieldPred<P>) -> bool {
        a.first_witness().is_some()
    }

    fn witness(&self, a: &OrderedFieldPred<P>) -> Option<P> {
        a.first_witness()
    }

    fn evaluate(&self, pred: &OrderedFieldPred<P>, elem: &P) -> bool {
        pred.contains(elem)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn bi(n: i64) -> BigInt {
        BigInt::from(n)
    }
    fn rat(n: i64, d: i64) -> BigRational {
        BigRational::new(BigInt::from(n), BigInt::from(d))
    }

    #[test]
    fn bigint_basic_ops() {
        let alg = OrderedFieldAlgebra::<BigInt>::new();
        let a = OrderedFieldPred::closed(bi(0), bi(10));
        let b = OrderedFieldPred::closed(bi(5), bi(20));
        assert!(alg.is_satisfiable(&a));
        assert!(alg.evaluate(&a, &bi(5)));
        assert!(!alg.evaluate(&a, &bi(11)));

        let inter = alg.and(&a, &b);
        assert!(alg.evaluate(&inter, &bi(5)));
        assert!(alg.evaluate(&inter, &bi(10)));
        assert!(!alg.evaluate(&inter, &bi(4)));
        assert!(!alg.evaluate(&inter, &bi(11)));

        let uni = alg.or(&a, &b);
        assert!(alg.evaluate(&uni, &bi(0)));
        assert!(alg.evaluate(&uni, &bi(20)));
        assert!(!alg.evaluate(&uni, &bi(21)));

        // Complement of [0,10] over the integers is (-inf,-1] ∪ [11,+inf).
        let comp = alg.not(&a);
        assert!(alg.evaluate(&comp, &bi(-1)));
        assert!(alg.evaluate(&comp, &bi(11)));
        assert!(!alg.evaluate(&comp, &bi(0)));
        assert!(!alg.evaluate(&comp, &bi(10)));
        // Double negation.
        assert!(!alg.is_satisfiable(&alg.and(&a, &comp)));
        assert_eq!(alg.not(&comp), a);
    }

    #[test]
    fn discrete_open_interval_is_empty_but_dense_is_not() {
        // (2, 3): no integer strictly between, but rationals like 5/2 qualify.
        let int_alg = OrderedFieldAlgebra::<BigInt>::new();
        let open_int = OrderedFieldPred::<BigInt>::from_intervals(vec![(
            Bound::Excl(bi(2)),
            Bound::Excl(bi(3)),
        )]);
        assert!(!int_alg.is_satisfiable(&open_int));

        let rat_alg = OrderedFieldAlgebra::<BigRational>::new();
        let open_rat = OrderedFieldPred::<BigRational>::from_intervals(vec![(
            Bound::Excl(rat(2, 1)),
            Bound::Excl(rat(3, 1)),
        )]);
        assert!(rat_alg.is_satisfiable(&open_rat));
        assert!(rat_alg.evaluate(&open_rat, &rat(5, 2)));
        assert!(!rat_alg.evaluate(&open_rat, &rat(2, 1)));
    }

    #[test]
    fn discrete_adjacent_intervals_merge() {
        // [1,2] ∪ [3,4] = [1,4] over the integers (2 and 3 are adjacent).
        let alg = OrderedFieldAlgebra::<BigInt>::new();
        let merged = alg
            .or(&OrderedFieldPred::closed(bi(1), bi(2)), &OrderedFieldPred::closed(bi(3), bi(4)));
        // Equivalent to [1,4].
        assert_eq!(merged, OrderedFieldPred::closed(bi(1), bi(4)));
        for v in 1..=4 {
            assert!(alg.evaluate(&merged, &bi(v)));
        }
        assert!(!alg.evaluate(&merged, &bi(0)));
        assert!(!alg.evaluate(&merged, &bi(5)));
    }

    #[test]
    fn dense_half_open_intervals_merge_at_shared_point() {
        // [1,2) ∪ [2,3) = [1,3) over the rationals (2 is covered by the second).
        let alg = OrderedFieldAlgebra::<BigRational>::new();
        let merged = alg.or(
            &OrderedFieldPred::half_open(rat(1, 1), rat(2, 1)),
            &OrderedFieldPred::half_open(rat(2, 1), rat(3, 1)),
        );
        assert_eq!(merged, OrderedFieldPred::half_open(rat(1, 1), rat(3, 1)));
        assert!(alg.evaluate(&merged, &rat(2, 1)));
        assert!(!alg.evaluate(&merged, &rat(3, 1)));
    }

    #[test]
    fn dense_split_intervals_do_not_merge() {
        // [1,2] ∪ [3,4] stays split over the rationals (gap (2,3) is non-empty).
        let alg = OrderedFieldAlgebra::<BigRational>::new();
        let merged = alg.or(
            &OrderedFieldPred::closed(rat(1, 1), rat(2, 1)),
            &OrderedFieldPred::closed(rat(3, 1), rat(4, 1)),
        );
        assert!(!alg.evaluate(&merged, &rat(5, 2))); // 2.5 is in the gap
        assert!(alg.evaluate(&merged, &rat(2, 1)));
        assert!(alg.evaluate(&merged, &rat(3, 1)));
    }

    #[test]
    fn unbounded_and_witness() {
        let alg = OrderedFieldAlgebra::<BigInt>::new();
        let ge5 = OrderedFieldPred::at_least(bi(5));
        assert_eq!(alg.witness(&ge5), Some(bi(5)));
        let le_neg = OrderedFieldPred::at_most(bi(-3));
        assert_eq!(alg.witness(&le_neg), Some(bi(-3)));
        // Disjoint unbounded both ways.
        let both = alg.or(&ge5, &le_neg);
        assert!(alg.evaluate(&both, &bi(100)));
        assert!(alg.evaluate(&both, &bi(-100)));
        assert!(!alg.evaluate(&both, &bi(0)));
        // Its complement is the bounded middle [-2, 4].
        let mid = alg.not(&both);
        assert!(alg.evaluate(&mid, &bi(0)));
        assert!(alg.evaluate(&mid, &bi(-2)));
        assert!(alg.evaluate(&mid, &bi(4)));
        assert!(!alg.evaluate(&mid, &bi(5)));
        assert!(!alg.evaluate(&mid, &bi(-3)));
    }

    #[test]
    fn float_total_order_and_intervals() {
        let alg = OrderedFieldAlgebra::<OrderedF64>::new();
        let unit = OrderedFieldPred::half_open(OrderedF64(0.0), OrderedF64(1.0));
        assert!(alg.evaluate(&unit, &OrderedF64(0.0)));
        assert!(alg.evaluate(&unit, &OrderedF64(0.5)));
        assert!(!alg.evaluate(&unit, &OrderedF64(1.0)));
        assert!(alg.is_satisfiable(&unit));
        // Witness lies in [0,1).
        let w = alg.witness(&unit).expect("nonempty");
        assert!(alg.evaluate(&unit, &w));
        // Complement excludes the unit interval.
        let comp = alg.not(&unit);
        assert!(alg.evaluate(&comp, &OrderedF64(1.0)));
        assert!(!alg.evaluate(&comp, &OrderedF64(0.5)));
    }

    #[test]
    fn float_adjacent_open_interval_empty() {
        // (x, x.next_up()) has no float strictly between → empty.
        let alg = OrderedFieldAlgebra::<OrderedF64>::new();
        let x = 1.0_f64;
        let nxt = x.next_up();
        let open = OrderedFieldPred::<OrderedF64>::from_intervals(vec![(
            Bound::Excl(OrderedF64(x)),
            Bound::Excl(OrderedF64(nxt)),
        )]);
        assert!(!alg.is_satisfiable(&open));
    }

    #[test]
    fn i128_ops() {
        let alg = OrderedFieldAlgebra::<i128>::new();
        let p = OrderedFieldPred::closed(0i128, 100i128);
        assert!(alg.evaluate(&p, &50));
        assert!(!alg.evaluate(&p, &101));
        let comp = alg.not(&p);
        assert!(alg.evaluate(&comp, &-1));
        assert!(alg.evaluate(&comp, &101));
        assert_eq!(alg.not(&comp), p);
    }

    #[test]
    fn boolean_algebra_laws_hold_semantically() {
        let alg = OrderedFieldAlgebra::<BigInt>::new();
        let a = OrderedFieldPred::closed(bi(0), bi(10));
        let b = OrderedFieldPred::closed(bi(5), bi(15));
        // a ∧ ¬a = ⊥
        assert!(!alg.is_satisfiable(&alg.and(&a, &alg.not(&a))));
        // a ∨ ¬a = ⊤  (its complement is unsatisfiable)
        assert!(!alg.is_satisfiable(&alg.not(&alg.or(&a, &alg.not(&a)))));
        // De Morgan: ¬(a ∧ b) ≡ ¬a ∨ ¬b
        let lhs = alg.not(&alg.and(&a, &b));
        let rhs = alg.or(&alg.not(&a), &alg.not(&b));
        // semantic equivalence: symmetric difference empty
        let sym = alg.or(&alg.and(&lhs, &alg.not(&rhs)), &alg.and(&rhs, &alg.not(&lhs)));
        assert!(!alg.is_satisfiable(&sym));
    }
}
