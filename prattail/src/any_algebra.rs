//! `AnyAlgebra` — a single concrete carrier that lets the symbolic-automata
//! machinery range over a *family* of effective Boolean algebras (one per data
//! sort) without generic-explosion or `dyn`.
//!
//! ## Why this exists
//!
//! [`BooleanAlgebra`](crate::symbolic::BooleanAlgebra) is parametric in its
//! `Predicate`/`Domain` associated types. Every concrete algebra therefore
//! produces a *different* `SymbolicAutomaton<A>` / `SymbolicFiniteTransducer<A,
//! B>` instantiation. To make one transducer guard predicates of *any* supported
//! data type — and, later, to put a heterogeneous payload on each node of a
//! symbolic tree automaton whose children have different sorts — we need a
//! **single** `Predicate`/`Domain` pair that can stand for any leaf sort.
//!
//! `AnyAlgebra` is that carrier: a closed `enum` (no `dyn`, so `Predicate: Eq +
//! Hash` survives for minterm/determinization hashing and there is no allocation
//! on the hot guard-evaluation path), dispatched by a `match`.
//!
//! ## Many-sorted semantics (exact, not approximate)
//!
//! Predicates ([`AnyPred`]) are boolean combinations of *per-sort leaf*
//! predicates. The domain ([`AnyDomain`]) is the **disjoint union** of the
//! per-sort domains — every concrete element has exactly one sort.
//!
//! A given `AnyAlgebra` *value* (e.g. [`AnyAlgebra::Int`]) is the algebra **of
//! one sort**; its decision procedures answer questions *about elements of that
//! sort*. A leaf predicate of a foreign sort is unsatisfiable by an element of
//! this sort, so it **projects to `⊥`** when this algebra interprets a formula
//! (see [`fold_pred`]). This is the standard slice of a many-sorted algebra and
//! is fully exact:
//!
//! - `Int(a) ∧ Char(b)` is unsatisfiable for *every* sort (no element is both an
//!   `Int` and a `Char`), so [`AnyAlgebra::is_satisfiable`] returns `false`.
//! - `Int(a) ∨ Char(b)` interpreted by the `Int` algebra is satisfiable iff `a`
//!   is; the same formula interpreted by the `Char` algebra is satisfiable iff
//!   `b` is.
//! - `¬Int(a)` interpreted by the `Char` algebra is `⊤`.
//!
//! Cross-sort *unions* that must be satisfiable-by-anyone are expressed with the
//! `Sum`/`Product` combinators, which combine the per-sort answers; they are not
//! the job of a single leaf algebra.
//!
//! ## Supported sorts
//!
//! Scalar leaves wrapping the concrete effective Boolean algebras:
//! - [`Sort::Int`]   → `IntervalAlgebra` (bounded `i64`)
//! - [`Sort::Char`]  → `CharClassAlgebra` (Unicode)
//! - [`Sort::Bool`]  → `KatBooleanAlgebra` (propositional truth assignments)
//! - [`Sort::BigInt`]→ `OrderedFieldAlgebra<BigInt>` (unbounded integers)
//! - [`Sort::BigRat`]→ `OrderedFieldAlgebra<BigRational>` (exact rationals)
//! - [`Sort::Fixed`] → `OrderedFieldAlgebra<BigRational>` (fixed-point decimals,
//!   value `= unscaled / 10^places`, a distinct sort sharing the rational carrier)
//! - [`Sort::Float`] → `OrderedFieldAlgebra<OrderedF64>` (`f64`, total order)
//!
//! M1 (later steps) adds `Str` and the `Product`/`Sum`/`Collection`/`Tree`
//! combinator variants; the [`SortRegistry`] is the lookup table those
//! combinators consult to fetch the algebra for a child sort.

use std::collections::HashMap;

use num_bigint::BigInt;
use num_rational::BigRational;

use crate::kat::BooleanTest;
use crate::ordered_field::{OrderedF64, OrderedFieldAlgebra, OrderedFieldPred};
use crate::symbolic::{
    BooleanAlgebra, CharClassAlgebra, CharClassPred, IntervalAlgebra, IntervalPred,
    KatBooleanAlgebra,
};

// ══════════════════════════════════════════════════════════════════════════════
// Sort
// ══════════════════════════════════════════════════════════════════════════════

/// The sort (data type) a leaf algebra ranges over.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Sort {
    /// Bounded integers — `IntervalAlgebra`.
    Int,
    /// Unicode scalar values — `CharClassAlgebra`.
    Char,
    /// Propositional truth assignments — `KatBooleanAlgebra`.
    Bool,
    /// Arbitrary-precision integers — `OrderedFieldAlgebra<BigInt>`.
    BigInt,
    /// Exact rationals — `OrderedFieldAlgebra<BigRational>`.
    BigRat,
    /// Fixed-point decimals (value `= unscaled / 10^places`), carried as exact
    /// rationals but a distinct sort — `OrderedFieldAlgebra<BigRational>`.
    Fixed,
    /// `f64` under a total order — `OrderedFieldAlgebra<OrderedF64>`.
    Float,
}

// ══════════════════════════════════════════════════════════════════════════════
// AnyDomain — the disjoint union of per-sort domains
// ══════════════════════════════════════════════════════════════════════════════

/// A concrete element of one of the supported sorts. Every value has exactly one
/// sort (see [`AnyDomain::sort`]).
#[derive(Clone, Debug)]
pub enum AnyDomain {
    /// An integer element (sort [`Sort::Int`]).
    Int(i64),
    /// A character element (sort [`Sort::Char`]).
    Char(char),
    /// A truth assignment (sort [`Sort::Bool`]).
    Bool(HashMap<String, bool>),
    /// An arbitrary-precision integer (sort [`Sort::BigInt`]).
    BigInt(BigInt),
    /// An exact rational (sort [`Sort::BigRat`]).
    BigRat(BigRational),
    /// A fixed-point decimal as an exact rational (sort [`Sort::Fixed`]).
    Fixed(BigRational),
    /// A float (sort [`Sort::Float`]).
    Float(OrderedF64),
}

impl AnyDomain {
    /// The sort of this element.
    pub fn sort(&self) -> Sort {
        match self {
            AnyDomain::Int(_) => Sort::Int,
            AnyDomain::Char(_) => Sort::Char,
            AnyDomain::Bool(_) => Sort::Bool,
            AnyDomain::BigInt(_) => Sort::BigInt,
            AnyDomain::BigRat(_) => Sort::BigRat,
            AnyDomain::Fixed(_) => Sort::Fixed,
            AnyDomain::Float(_) => Sort::Float,
        }
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// AnyPred — boolean combinations of per-sort leaf predicates
// ══════════════════════════════════════════════════════════════════════════════

/// A predicate over [`AnyDomain`]: a boolean combination of per-sort leaf
/// predicates. `Eq + Hash` are derived (every leaf predicate type is `Eq +
/// Hash`), which the minterm/determinization machinery relies on.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum AnyPred {
    /// Satisfied by every element of every sort.
    True,
    /// Satisfied by no element.
    False,
    /// An integer-sort leaf predicate.
    Int(IntervalPred),
    /// A character-sort leaf predicate.
    Char(CharClassPred),
    /// A boolean-sort leaf predicate.
    Bool(BooleanTest),
    /// A big-integer-sort leaf predicate.
    BigInt(OrderedFieldPred<BigInt>),
    /// A rational-sort leaf predicate.
    BigRat(OrderedFieldPred<BigRational>),
    /// A fixed-point-sort leaf predicate (rational carrier, distinct sort).
    Fixed(OrderedFieldPred<BigRational>),
    /// A float-sort leaf predicate.
    Float(OrderedFieldPred<OrderedF64>),
    /// Conjunction.
    And(Box<AnyPred>, Box<AnyPred>),
    /// Disjunction.
    Or(Box<AnyPred>, Box<AnyPred>),
    /// Negation.
    Not(Box<AnyPred>),
}

impl AnyPred {
    /// If this is a leaf predicate, the sort it constrains; `None` for the
    /// boolean-combination nodes and the `True`/`False` constants.
    pub fn leaf_sort(&self) -> Option<Sort> {
        match self {
            AnyPred::Int(_) => Some(Sort::Int),
            AnyPred::Char(_) => Some(Sort::Char),
            AnyPred::Bool(_) => Some(Sort::Bool),
            AnyPred::BigInt(_) => Some(Sort::BigInt),
            AnyPred::BigRat(_) => Some(Sort::BigRat),
            AnyPred::Fixed(_) => Some(Sort::Fixed),
            AnyPred::Float(_) => Some(Sort::Float),
            AnyPred::True | AnyPred::False | AnyPred::And(..) | AnyPred::Or(..) | AnyPred::Not(_) => {
                None
            },
        }
    }
}

/// Project an [`AnyPred`] onto a single sort and evaluate the boolean structure
/// inside that sort's algebra `alg`. `leaf` recognizes the leaf predicates that
/// belong to `alg`'s sort; leaves of any *other* sort fall through to
/// `alg.false_pred()` (a foreign-sort predicate is unsatisfiable by an element
/// of this sort). The result is exact for `alg`'s sort.
fn fold_pred<A, F>(alg: &A, p: &AnyPred, leaf: &F) -> A::Predicate
where
    A: BooleanAlgebra,
    F: Fn(&AnyPred) -> Option<A::Predicate>,
{
    match p {
        AnyPred::True => alg.true_pred(),
        AnyPred::False => alg.false_pred(),
        AnyPred::And(a, b) => alg.and(&fold_pred(alg, a, leaf), &fold_pred(alg, b, leaf)),
        AnyPred::Or(a, b) => alg.or(&fold_pred(alg, a, leaf), &fold_pred(alg, b, leaf)),
        AnyPred::Not(x) => alg.not(&fold_pred(alg, x, leaf)),
        // A leaf node: matched-sort → its inner predicate; foreign-sort → ⊥.
        AnyPred::Int(_)
        | AnyPred::Char(_)
        | AnyPred::Bool(_)
        | AnyPred::BigInt(_)
        | AnyPred::BigRat(_)
        | AnyPred::Fixed(_)
        | AnyPred::Float(_) => leaf(p).unwrap_or_else(|| alg.false_pred()),
    }
}

fn int_leaf(p: &AnyPred) -> Option<IntervalPred> {
    match p {
        AnyPred::Int(x) => Some(x.clone()),
        _ => None,
    }
}
fn char_leaf(p: &AnyPred) -> Option<CharClassPred> {
    match p {
        AnyPred::Char(x) => Some(x.clone()),
        _ => None,
    }
}
fn bool_leaf(p: &AnyPred) -> Option<BooleanTest> {
    match p {
        AnyPred::Bool(x) => Some(x.clone()),
        _ => None,
    }
}
fn bigint_leaf(p: &AnyPred) -> Option<OrderedFieldPred<BigInt>> {
    match p {
        AnyPred::BigInt(x) => Some(x.clone()),
        _ => None,
    }
}
fn bigrat_leaf(p: &AnyPred) -> Option<OrderedFieldPred<BigRational>> {
    match p {
        AnyPred::BigRat(x) => Some(x.clone()),
        _ => None,
    }
}
fn fixed_leaf(p: &AnyPred) -> Option<OrderedFieldPred<BigRational>> {
    match p {
        AnyPred::Fixed(x) => Some(x.clone()),
        _ => None,
    }
}
fn float_leaf(p: &AnyPred) -> Option<OrderedFieldPred<OrderedF64>> {
    match p {
        AnyPred::Float(x) => Some(x.clone()),
        _ => None,
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// AnyAlgebra — the per-sort effective Boolean algebra carrier
// ══════════════════════════════════════════════════════════════════════════════

/// A single effective Boolean algebra, tagged by the sort it ranges over.
#[derive(Clone, Debug)]
pub enum AnyAlgebra {
    /// Bounded-integer algebra.
    Int(IntervalAlgebra),
    /// Unicode character-class algebra.
    Char(CharClassAlgebra),
    /// Propositional (KAT) algebra.
    Bool(KatBooleanAlgebra),
    /// Arbitrary-precision integer algebra.
    BigInt(OrderedFieldAlgebra<BigInt>),
    /// Exact rational algebra.
    BigRat(OrderedFieldAlgebra<BigRational>),
    /// Fixed-point algebra (rational carrier, distinct sort).
    Fixed(OrderedFieldAlgebra<BigRational>),
    /// Float algebra.
    Float(OrderedFieldAlgebra<OrderedF64>),
}

impl AnyAlgebra {
    /// The sort this algebra ranges over.
    pub fn sort(&self) -> Sort {
        match self {
            AnyAlgebra::Int(_) => Sort::Int,
            AnyAlgebra::Char(_) => Sort::Char,
            AnyAlgebra::Bool(_) => Sort::Bool,
            AnyAlgebra::BigInt(_) => Sort::BigInt,
            AnyAlgebra::BigRat(_) => Sort::BigRat,
            AnyAlgebra::Fixed(_) => Sort::Fixed,
            AnyAlgebra::Float(_) => Sort::Float,
        }
    }
}

impl BooleanAlgebra for AnyAlgebra {
    type Predicate = AnyPred;
    type Domain = AnyDomain;

    fn true_pred(&self) -> AnyPred {
        AnyPred::True
    }

    fn false_pred(&self) -> AnyPred {
        AnyPred::False
    }

    fn and(&self, a: &AnyPred, b: &AnyPred) -> AnyPred {
        match (a, b) {
            (AnyPred::False, _) | (_, AnyPred::False) => AnyPred::False,
            (AnyPred::True, x) | (x, AnyPred::True) => x.clone(),
            // Same-sort leaves: delegate to the inner algebra to keep the
            // predicate normalized (exact, and identical to the bare algebra).
            _ => match (self, a, b) {
                (AnyAlgebra::Int(g), AnyPred::Int(x), AnyPred::Int(y)) => AnyPred::Int(g.and(x, y)),
                (AnyAlgebra::Char(g), AnyPred::Char(x), AnyPred::Char(y)) => {
                    AnyPred::Char(g.and(x, y))
                },
                (AnyAlgebra::Bool(g), AnyPred::Bool(x), AnyPred::Bool(y)) => {
                    AnyPred::Bool(g.and(x, y))
                },
                (AnyAlgebra::BigInt(g), AnyPred::BigInt(x), AnyPred::BigInt(y)) => {
                    AnyPred::BigInt(g.and(x, y))
                },
                (AnyAlgebra::BigRat(g), AnyPred::BigRat(x), AnyPred::BigRat(y)) => {
                    AnyPred::BigRat(g.and(x, y))
                },
                (AnyAlgebra::Fixed(g), AnyPred::Fixed(x), AnyPred::Fixed(y)) => {
                    AnyPred::Fixed(g.and(x, y))
                },
                (AnyAlgebra::Float(g), AnyPred::Float(x), AnyPred::Float(y)) => {
                    AnyPred::Float(g.and(x, y))
                },
                _ => AnyPred::And(Box::new(a.clone()), Box::new(b.clone())),
            },
        }
    }

    fn or(&self, a: &AnyPred, b: &AnyPred) -> AnyPred {
        match (a, b) {
            (AnyPred::True, _) | (_, AnyPred::True) => AnyPred::True,
            (AnyPred::False, x) | (x, AnyPred::False) => x.clone(),
            _ => match (self, a, b) {
                (AnyAlgebra::Int(g), AnyPred::Int(x), AnyPred::Int(y)) => AnyPred::Int(g.or(x, y)),
                (AnyAlgebra::Char(g), AnyPred::Char(x), AnyPred::Char(y)) => {
                    AnyPred::Char(g.or(x, y))
                },
                (AnyAlgebra::Bool(g), AnyPred::Bool(x), AnyPred::Bool(y)) => {
                    AnyPred::Bool(g.or(x, y))
                },
                (AnyAlgebra::BigInt(g), AnyPred::BigInt(x), AnyPred::BigInt(y)) => {
                    AnyPred::BigInt(g.or(x, y))
                },
                (AnyAlgebra::BigRat(g), AnyPred::BigRat(x), AnyPred::BigRat(y)) => {
                    AnyPred::BigRat(g.or(x, y))
                },
                (AnyAlgebra::Fixed(g), AnyPred::Fixed(x), AnyPred::Fixed(y)) => {
                    AnyPred::Fixed(g.or(x, y))
                },
                (AnyAlgebra::Float(g), AnyPred::Float(x), AnyPred::Float(y)) => {
                    AnyPred::Float(g.or(x, y))
                },
                _ => AnyPred::Or(Box::new(a.clone()), Box::new(b.clone())),
            },
        }
    }

    fn not(&self, a: &AnyPred) -> AnyPred {
        match (self, a) {
            (_, AnyPred::True) => AnyPred::False,
            (_, AnyPred::False) => AnyPred::True,
            // Double-negation elimination is sound: every leaf algebra is a
            // classical Boolean algebra and the projection semantics is classical.
            (_, AnyPred::Not(inner)) => (**inner).clone(),
            (AnyAlgebra::Int(g), AnyPred::Int(x)) => AnyPred::Int(g.not(x)),
            (AnyAlgebra::Char(g), AnyPred::Char(x)) => AnyPred::Char(g.not(x)),
            (AnyAlgebra::Bool(g), AnyPred::Bool(x)) => AnyPred::Bool(g.not(x)),
            (AnyAlgebra::BigInt(g), AnyPred::BigInt(x)) => AnyPred::BigInt(g.not(x)),
            (AnyAlgebra::BigRat(g), AnyPred::BigRat(x)) => AnyPred::BigRat(g.not(x)),
            (AnyAlgebra::Fixed(g), AnyPred::Fixed(x)) => AnyPred::Fixed(g.not(x)),
            (AnyAlgebra::Float(g), AnyPred::Float(x)) => AnyPred::Float(g.not(x)),
            _ => AnyPred::Not(Box::new(a.clone())),
        }
    }

    fn is_satisfiable(&self, a: &AnyPred) -> bool {
        match self {
            AnyAlgebra::Int(g) => g.is_satisfiable(&fold_pred(g, a, &int_leaf)),
            AnyAlgebra::Char(g) => g.is_satisfiable(&fold_pred(g, a, &char_leaf)),
            AnyAlgebra::Bool(g) => g.is_satisfiable(&fold_pred(g, a, &bool_leaf)),
            AnyAlgebra::BigInt(g) => g.is_satisfiable(&fold_pred(g, a, &bigint_leaf)),
            AnyAlgebra::BigRat(g) => g.is_satisfiable(&fold_pred(g, a, &bigrat_leaf)),
            AnyAlgebra::Fixed(g) => g.is_satisfiable(&fold_pred(g, a, &fixed_leaf)),
            AnyAlgebra::Float(g) => g.is_satisfiable(&fold_pred(g, a, &float_leaf)),
        }
    }

    fn witness(&self, a: &AnyPred) -> Option<AnyDomain> {
        match self {
            AnyAlgebra::Int(g) => g.witness(&fold_pred(g, a, &int_leaf)).map(AnyDomain::Int),
            AnyAlgebra::Char(g) => g.witness(&fold_pred(g, a, &char_leaf)).map(AnyDomain::Char),
            AnyAlgebra::Bool(g) => g.witness(&fold_pred(g, a, &bool_leaf)).map(AnyDomain::Bool),
            AnyAlgebra::BigInt(g) => {
                g.witness(&fold_pred(g, a, &bigint_leaf)).map(AnyDomain::BigInt)
            },
            AnyAlgebra::BigRat(g) => {
                g.witness(&fold_pred(g, a, &bigrat_leaf)).map(AnyDomain::BigRat)
            },
            AnyAlgebra::Fixed(g) => g.witness(&fold_pred(g, a, &fixed_leaf)).map(AnyDomain::Fixed),
            AnyAlgebra::Float(g) => g.witness(&fold_pred(g, a, &float_leaf)).map(AnyDomain::Float),
        }
    }

    fn evaluate(&self, pred: &AnyPred, elem: &AnyDomain) -> bool {
        match (self, elem) {
            (AnyAlgebra::Int(g), AnyDomain::Int(v)) => g.evaluate(&fold_pred(g, pred, &int_leaf), v),
            (AnyAlgebra::Char(g), AnyDomain::Char(v)) => {
                g.evaluate(&fold_pred(g, pred, &char_leaf), v)
            },
            (AnyAlgebra::Bool(g), AnyDomain::Bool(v)) => {
                g.evaluate(&fold_pred(g, pred, &bool_leaf), v)
            },
            (AnyAlgebra::BigInt(g), AnyDomain::BigInt(v)) => {
                g.evaluate(&fold_pred(g, pred, &bigint_leaf), v)
            },
            (AnyAlgebra::BigRat(g), AnyDomain::BigRat(v)) => {
                g.evaluate(&fold_pred(g, pred, &bigrat_leaf), v)
            },
            (AnyAlgebra::Fixed(g), AnyDomain::Fixed(v)) => {
                g.evaluate(&fold_pred(g, pred, &fixed_leaf), v)
            },
            (AnyAlgebra::Float(g), AnyDomain::Float(v)) => {
                g.evaluate(&fold_pred(g, pred, &float_leaf), v)
            },
            // The element is not of this algebra's sort.
            _ => false,
        }
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// SortRegistry — sort → algebra lookup table
// ══════════════════════════════════════════════════════════════════════════════

/// Maps each active [`Sort`] to the [`AnyAlgebra`] that decides it. This is the
/// table the structured combinators (`Product`/`Sum`/`Collection`/`Tree`)
/// consult to fetch the algebra for a child sort.
#[derive(Clone, Debug, Default)]
pub struct SortRegistry {
    algebras: HashMap<Sort, AnyAlgebra>,
}

impl SortRegistry {
    /// An empty registry.
    pub fn new() -> Self {
        SortRegistry { algebras: HashMap::new() }
    }

    /// Register (or replace) the algebra for `sort`.
    pub fn insert(&mut self, sort: Sort, algebra: AnyAlgebra) {
        self.algebras.insert(sort, algebra);
    }

    /// The algebra registered for `sort`, if any.
    pub fn get(&self, sort: Sort) -> Option<&AnyAlgebra> {
        self.algebras.get(&sort)
    }

    /// Whether `sort` is active in this registry.
    pub fn contains(&self, sort: Sort) -> bool {
        self.algebras.contains_key(&sort)
    }

    /// The active sorts.
    pub fn sorts(&self) -> impl Iterator<Item = Sort> + '_ {
        self.algebras.keys().copied()
    }

    /// Number of active sorts.
    pub fn len(&self) -> usize {
        self.algebras.len()
    }

    /// Whether the registry is empty.
    pub fn is_empty(&self) -> bool {
        self.algebras.is_empty()
    }

    /// The default scalar registry: every scalar sort with its algebra. `Int`
    /// uses the bounded universe `[int_lo, int_hi)`; `Bool` uses `bool_atoms`;
    /// the unbounded numeric leaves and `Char` are parameter-free.
    pub fn scalars(int_lo: i64, int_hi: i64, bool_atoms: Vec<String>) -> Self {
        let mut registry = SortRegistry::new();
        registry.insert(Sort::Int, AnyAlgebra::Int(IntervalAlgebra::new(int_lo, int_hi)));
        registry.insert(Sort::Char, AnyAlgebra::Char(CharClassAlgebra::new()));
        registry.insert(Sort::Bool, AnyAlgebra::Bool(KatBooleanAlgebra::new(bool_atoms)));
        registry.insert(Sort::BigInt, AnyAlgebra::BigInt(OrderedFieldAlgebra::new()));
        registry.insert(Sort::BigRat, AnyAlgebra::BigRat(OrderedFieldAlgebra::new()));
        registry.insert(Sort::Fixed, AnyAlgebra::Fixed(OrderedFieldAlgebra::new()));
        registry.insert(Sort::Float, AnyAlgebra::Float(OrderedFieldAlgebra::new()));
        registry
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

    /// The `AnyAlgebra::Int` wrapper answers identically to the bare
    /// `IntervalAlgebra` for `Int` formulas.
    #[test]
    fn wrapper_matches_interval_suite() {
        let bare = IntervalAlgebra::new(0, 100);
        let any = AnyAlgebra::Int(IntervalAlgebra::new(0, 100));
        let preds = [
            IntervalPred::True,
            IntervalPred::False,
            IntervalPred::Range(10, 20),
            IntervalPred::Union(vec![(0, 5), (30, 40)]),
            IntervalPred::Not(Box::new(IntervalPred::Range(10, 20))),
        ];
        for p in &preds {
            let wrapped = AnyPred::Int(p.clone());
            assert_eq!(bare.is_satisfiable(p), any.is_satisfiable(&wrapped));
            assert_eq!(
                bare.witness(p),
                match any.witness(&wrapped) {
                    Some(AnyDomain::Int(v)) => Some(v),
                    None => None,
                    other => panic!("expected Int witness, got {other:?}"),
                },
            );
            for v in [0i64, 12, 35, 99] {
                assert_eq!(bare.evaluate(p, &v), any.evaluate(&wrapped, &AnyDomain::Int(v)));
            }
        }
    }

    /// The `AnyAlgebra::Bool` wrapper answers identically to the bare
    /// `KatBooleanAlgebra` for `Bool` formulas.
    #[test]
    fn wrapper_matches_kat_suite() {
        let atoms = vec!["p".to_string(), "q".to_string()];
        let bare = KatBooleanAlgebra::new(atoms.clone());
        let any = AnyAlgebra::Bool(KatBooleanAlgebra::new(atoms));
        let p = BooleanTest::Atom("p".to_string());
        let q = BooleanTest::Atom("q".to_string());
        let preds = [
            BooleanTest::True,
            BooleanTest::False,
            p.clone(),
            BooleanTest::And(Box::new(p.clone()), Box::new(q.clone())),
            BooleanTest::And(Box::new(p.clone()), Box::new(BooleanTest::Not(Box::new(p.clone())))),
        ];
        for pred in &preds {
            let wrapped = AnyPred::Bool(pred.clone());
            assert_eq!(bare.is_satisfiable(pred), any.is_satisfiable(&wrapped));
            assert_eq!(bare.witness(pred).is_some(), any.witness(&wrapped).is_some());
        }
    }

    /// The `AnyAlgebra::BigInt` wrapper answers identically to the bare
    /// `OrderedFieldAlgebra<BigInt>`.
    #[test]
    fn wrapper_matches_bigint_suite() {
        let bare = OrderedFieldAlgebra::<BigInt>::new();
        let any = AnyAlgebra::BigInt(OrderedFieldAlgebra::<BigInt>::new());
        let p = OrderedFieldPred::closed(bi(0), bi(10));
        let wrapped = AnyPred::BigInt(p.clone());
        assert_eq!(bare.is_satisfiable(&p), any.is_satisfiable(&wrapped));
        assert!(any.evaluate(&wrapped, &AnyDomain::BigInt(bi(5))));
        assert!(!any.evaluate(&wrapped, &AnyDomain::BigInt(bi(11))));
        // not / and / or delegate exactly.
        let comp = any.not(&wrapped);
        assert!(any.evaluate(&comp, &AnyDomain::BigInt(bi(11))));
        assert!(!any.is_satisfiable(&any.and(&wrapped, &comp)));
    }

    /// `Fixed` and `BigRat` are distinct sorts even though they share the
    /// rational carrier: a `BigRat` predicate is foreign to the `Fixed` algebra.
    #[test]
    fn fixed_and_bigrat_are_distinct_sorts() {
        let fixed = AnyAlgebra::Fixed(OrderedFieldAlgebra::<BigRational>::new());
        let bigrat_pred = AnyPred::BigRat(OrderedFieldPred::closed(rat(0, 1), rat(1, 1)));
        // The Fixed algebra treats a BigRat leaf as foreign → ⊥.
        assert!(!fixed.is_satisfiable(&bigrat_pred));
        // Its own Fixed predicate is satisfiable.
        let fixed_pred = AnyPred::Fixed(OrderedFieldPred::closed(rat(0, 1), rat(1, 1)));
        assert!(fixed.is_satisfiable(&fixed_pred));
        assert!(fixed.evaluate(&fixed_pred, &AnyDomain::Fixed(rat(1, 2))));
    }

    #[test]
    fn float_wrapper_works() {
        let any = AnyAlgebra::Float(OrderedFieldAlgebra::<OrderedF64>::new());
        let p = AnyPred::Float(OrderedFieldPred::half_open(OrderedF64(0.0), OrderedF64(1.0)));
        assert!(any.is_satisfiable(&p));
        assert!(any.evaluate(&p, &AnyDomain::Float(OrderedF64(0.5))));
        assert!(!any.evaluate(&p, &AnyDomain::Float(OrderedF64(1.0))));
    }

    /// A cross-sort conjunction is unsatisfiable in every sort.
    #[test]
    fn cross_sort_and_is_unsat() {
        let any_int = AnyAlgebra::Int(IntervalAlgebra::new(0, 100));
        let pred = any_int.and(&AnyPred::Int(IntervalPred::True), &AnyPred::Char(CharClassPred::True));
        assert!(!any_int.is_satisfiable(&pred));
        let any_char = AnyAlgebra::Char(CharClassAlgebra::new());
        assert!(!any_char.is_satisfiable(&pred));
    }

    /// A cross-sort disjunction is satisfiable in a given sort only through that
    /// sort's disjunct.
    #[test]
    fn cross_sort_or_projects_per_sort() {
        let int_unsat = AnyPred::Int(IntervalPred::False);
        let bigint_sat = AnyPred::BigInt(OrderedFieldPred::at_least(bi(0)));
        let any_int = AnyAlgebra::Int(IntervalAlgebra::new(0, 100));
        let or = any_int.or(&int_unsat, &bigint_sat);
        assert!(!any_int.is_satisfiable(&or));
        let any_big = AnyAlgebra::BigInt(OrderedFieldAlgebra::<BigInt>::new());
        assert!(any_big.is_satisfiable(&or));
    }

    /// Negating a foreign-sort leaf is `⊤` within this sort.
    #[test]
    fn not_of_foreign_leaf_is_top_in_this_sort() {
        let any_int = AnyAlgebra::Int(IntervalAlgebra::new(0, 100));
        let not_char = any_int.not(&AnyPred::Char(CharClassPred::True));
        assert!(any_int.is_satisfiable(&not_char));
        assert!(any_int.evaluate(&not_char, &AnyDomain::Int(42)));
    }

    /// `evaluate` returns `false` for a foreign-sort element.
    #[test]
    fn evaluate_rejects_foreign_sort_element() {
        let any_int = AnyAlgebra::Int(IntervalAlgebra::new(0, 100));
        let pred = AnyPred::Int(IntervalPred::True);
        assert!(any_int.evaluate(&pred, &AnyDomain::Int(1)));
        assert!(!any_int.evaluate(&pred, &AnyDomain::Char('a')));
        assert!(!any_int.evaluate(&pred, &AnyDomain::BigInt(bi(1))));
    }

    /// The scalar registry exposes all seven scalar sorts.
    #[test]
    fn scalar_registry_has_all_scalar_sorts() {
        let registry = SortRegistry::scalars(0, 256, vec!["p".to_string()]);
        assert_eq!(registry.len(), 7);
        for s in [Sort::Int, Sort::Char, Sort::Bool, Sort::BigInt, Sort::BigRat, Sort::Fixed, Sort::Float]
        {
            assert!(registry.contains(s), "missing sort {s:?}");
            assert_eq!(registry.get(s).map(AnyAlgebra::sort), Some(s));
        }
    }
}
