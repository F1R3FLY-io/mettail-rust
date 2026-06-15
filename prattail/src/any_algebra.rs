//! `AnyAlgebra` — a single concrete carrier that lets the symbolic-automata
//! machinery range over a *family* of effective Boolean algebras (one per data
//! sort) without generic-explosion or `dyn`.
//!
//! ## Why this exists
//!
//! [`BooleanAlgebra`](crate::symbolic::BooleanAlgebra) is parametric in its
//! `Predicate`/`Domain` associated types. Every concrete algebra
//! (`IntervalAlgebra` over `i64`, `CharClassAlgebra` over `char`,
//! `KatBooleanAlgebra` over truth assignments) therefore produces a *different*
//! `SymbolicAutomaton<A>` / `SymbolicFiniteTransducer<A, B>` instantiation.
//! To make one transducer guard predicates of *any* supported data type — and,
//! later, to put a heterogeneous payload on each node of a symbolic tree
//! automaton whose children have different sorts — we need a **single**
//! `Predicate`/`Domain` pair that can stand for any leaf sort.
//!
//! `AnyAlgebra` is that carrier. It is a closed `enum` (no `dyn`, so
//! `Predicate: Eq + Hash` survives for minterm/determinization hashing and there
//! is no allocation on the hot guard-evaluation path), dispatched by a `match`.
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
//!   is — the `Char` disjunct cannot be witnessed by an `Int` element. The same
//!   formula interpreted by the `Char` algebra is satisfiable iff `b` is.
//! - `¬Int(a)` interpreted by the `Char` algebra is `⊤` (a `Char` element is
//!   never a matching `Int`), so it is satisfiable whenever the `Char` universe
//!   is non-empty.
//!
//! Cross-sort *unions* that must be satisfiable-by-anyone are expressed with the
//! `Sum`/`Product` combinators (added in M1), which combine the per-sort
//! answers; they are not the job of a single leaf algebra.
//!
//! ## Scope of this module (M0)
//!
//! This is the substrate **skeleton**: it wraps the three effective Boolean
//! algebras that exist today — `IntervalAlgebra` (sort [`Sort::Int`]),
//! `CharClassAlgebra` (sort [`Sort::Char`]) and `KatBooleanAlgebra`
//! (sort [`Sort::Bool`]) — completely and exactly. M1 extends [`Sort`],
//! [`AnyAlgebra`], [`AnyPred`] and [`AnyDomain`] with the remaining scalar
//! leaves (`OrderedFieldAlgebra` for big-int/rat/fixed, `Float`, `Str`) and the
//! `Product`/`Sum`/`Collection`/`Tree` combinator variants; every variant added
//! there is likewise complete. The [`SortRegistry`] is the lookup table those
//! combinators use to fetch the algebra for a child sort.

use std::collections::HashMap;

use crate::kat::BooleanTest;
use crate::symbolic::{
    BooleanAlgebra, CharClassAlgebra, CharClassPred, IntervalAlgebra, IntervalPred,
    KatBooleanAlgebra,
};

// ══════════════════════════════════════════════════════════════════════════════
// Sort
// ══════════════════════════════════════════════════════════════════════════════

/// The sort (data type) a leaf algebra ranges over.
///
/// M0 provides the three scalar sorts that have backing algebras today. M1
/// extends this with `BigInt`/`BigRat`/`Fixed`/`Float`/`Str` and the structured
/// sorts (`Tuple`/`Sum`/`List`/`Bag`/`Map`/`Category`). Kept `Copy` so it is a
/// cheap key in [`SortRegistry`].
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Sort {
    /// Bounded integers — backed by `IntervalAlgebra`.
    Int,
    /// Unicode scalar values — backed by `CharClassAlgebra`.
    Char,
    /// Propositional truth assignments — backed by `KatBooleanAlgebra`.
    Bool,
}

// ══════════════════════════════════════════════════════════════════════════════
// AnyDomain — the disjoint union of per-sort domains
// ══════════════════════════════════════════════════════════════════════════════

/// A concrete element of one of the supported sorts.
///
/// Every value has exactly one sort (see [`AnyDomain::sort`]). The `Domain`
/// bound on [`BooleanAlgebra`] requires only `Clone + Debug + Send + Sync +
/// 'static`, all of which hold here.
#[derive(Clone, Debug)]
pub enum AnyDomain {
    /// An integer element (sort [`Sort::Int`]).
    Int(i64),
    /// A character element (sort [`Sort::Char`]).
    Char(char),
    /// A truth assignment (sort [`Sort::Bool`]).
    Bool(HashMap<String, bool>),
}

impl AnyDomain {
    /// The sort of this element.
    pub fn sort(&self) -> Sort {
        match self {
            AnyDomain::Int(_) => Sort::Int,
            AnyDomain::Char(_) => Sort::Char,
            AnyDomain::Bool(_) => Sort::Bool,
        }
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// AnyPred — boolean combinations of per-sort leaf predicates
// ══════════════════════════════════════════════════════════════════════════════

/// A predicate over [`AnyDomain`]: a boolean combination of per-sort leaf
/// predicates.
///
/// `Eq + Hash` are derived (every leaf predicate type is `Eq + Hash`), which the
/// minterm/determinization machinery relies on.
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
    /// Conjunction.
    And(Box<AnyPred>, Box<AnyPred>),
    /// Disjunction.
    Or(Box<AnyPred>, Box<AnyPred>),
    /// Negation.
    Not(Box<AnyPred>),
}

impl AnyPred {
    /// If this is a leaf predicate, the sort it constrains; `None` for the
    /// boolean-combination nodes and the `True`/`False` constants (which are
    /// sort-agnostic).
    pub fn leaf_sort(&self) -> Option<Sort> {
        match self {
            AnyPred::Int(_) => Some(Sort::Int),
            AnyPred::Char(_) => Some(Sort::Char),
            AnyPred::Bool(_) => Some(Sort::Bool),
            _ => None,
        }
    }
}

/// Project an [`AnyPred`] onto a single sort and evaluate the boolean structure
/// inside that sort's algebra `alg`.
///
/// `leaf` recognizes the leaf predicates that belong to `alg`'s sort and returns
/// the corresponding inner predicate; leaves of any *other* sort fall through to
/// `alg.false_pred()` (a foreign-sort predicate is unsatisfiable by an element
/// of this sort). `True`/`False`/`And`/`Or`/`Not` are mapped to `alg`'s own
/// operations, so the result is exact for `alg`'s sort.
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
        AnyPred::Int(_) | AnyPred::Char(_) | AnyPred::Bool(_) => {
            leaf(p).unwrap_or_else(|| alg.false_pred())
        },
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

// ══════════════════════════════════════════════════════════════════════════════
// AnyAlgebra — the per-sort effective Boolean algebra carrier
// ══════════════════════════════════════════════════════════════════════════════

/// A single effective Boolean algebra, tagged by the sort it ranges over.
///
/// Implements [`BooleanAlgebra`] with the uniform `Predicate = AnyPred` /
/// `Domain = AnyDomain`, so a `SymbolicAutomaton<AnyAlgebra>` /
/// `SymbolicFiniteTransducer<AnyAlgebra, AnyAlgebra>` can guard predicates of any
/// supported sort. Decision procedures interpret a formula within *this value's*
/// sort (see the module docs and [`fold_pred`]).
#[derive(Clone, Debug)]
pub enum AnyAlgebra {
    /// Bounded-integer algebra.
    Int(IntervalAlgebra),
    /// Unicode character-class algebra.
    Char(CharClassAlgebra),
    /// Propositional (KAT) algebra.
    Bool(KatBooleanAlgebra),
}

impl AnyAlgebra {
    /// The sort this algebra ranges over.
    pub fn sort(&self) -> Sort {
        match self {
            AnyAlgebra::Int(_) => Sort::Int,
            AnyAlgebra::Char(_) => Sort::Char,
            AnyAlgebra::Bool(_) => Sort::Bool,
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
                (AnyAlgebra::Int(ia), AnyPred::Int(x), AnyPred::Int(y)) => {
                    AnyPred::Int(ia.and(x, y))
                },
                (AnyAlgebra::Char(ca), AnyPred::Char(x), AnyPred::Char(y)) => {
                    AnyPred::Char(ca.and(x, y))
                },
                (AnyAlgebra::Bool(ba), AnyPred::Bool(x), AnyPred::Bool(y)) => {
                    AnyPred::Bool(ba.and(x, y))
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
                (AnyAlgebra::Int(ia), AnyPred::Int(x), AnyPred::Int(y)) => {
                    AnyPred::Int(ia.or(x, y))
                },
                (AnyAlgebra::Char(ca), AnyPred::Char(x), AnyPred::Char(y)) => {
                    AnyPred::Char(ca.or(x, y))
                },
                (AnyAlgebra::Bool(ba), AnyPred::Bool(x), AnyPred::Bool(y)) => {
                    AnyPred::Bool(ba.or(x, y))
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
            (AnyAlgebra::Int(ia), AnyPred::Int(x)) => AnyPred::Int(ia.not(x)),
            (AnyAlgebra::Char(ca), AnyPred::Char(x)) => AnyPred::Char(ca.not(x)),
            (AnyAlgebra::Bool(ba), AnyPred::Bool(x)) => AnyPred::Bool(ba.not(x)),
            _ => AnyPred::Not(Box::new(a.clone())),
        }
    }

    fn is_satisfiable(&self, a: &AnyPred) -> bool {
        match self {
            AnyAlgebra::Int(ia) => ia.is_satisfiable(&fold_pred(ia, a, &int_leaf)),
            AnyAlgebra::Char(ca) => ca.is_satisfiable(&fold_pred(ca, a, &char_leaf)),
            AnyAlgebra::Bool(ba) => ba.is_satisfiable(&fold_pred(ba, a, &bool_leaf)),
        }
    }

    fn witness(&self, a: &AnyPred) -> Option<AnyDomain> {
        match self {
            AnyAlgebra::Int(ia) => ia.witness(&fold_pred(ia, a, &int_leaf)).map(AnyDomain::Int),
            AnyAlgebra::Char(ca) => {
                ca.witness(&fold_pred(ca, a, &char_leaf)).map(AnyDomain::Char)
            },
            AnyAlgebra::Bool(ba) => {
                ba.witness(&fold_pred(ba, a, &bool_leaf)).map(AnyDomain::Bool)
            },
        }
    }

    fn evaluate(&self, pred: &AnyPred, elem: &AnyDomain) -> bool {
        match (self, elem) {
            (AnyAlgebra::Int(ia), AnyDomain::Int(v)) => {
                ia.evaluate(&fold_pred(ia, pred, &int_leaf), v)
            },
            (AnyAlgebra::Char(ca), AnyDomain::Char(v)) => {
                ca.evaluate(&fold_pred(ca, pred, &char_leaf), v)
            },
            (AnyAlgebra::Bool(ba), AnyDomain::Bool(v)) => {
                ba.evaluate(&fold_pred(ba, pred, &bool_leaf), v)
            },
            // The element is not of this algebra's sort: it cannot satisfy a
            // predicate this algebra interprets.
            _ => false,
        }
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// SortRegistry — sort → algebra lookup table
// ══════════════════════════════════════════════════════════════════════════════

/// Maps each active [`Sort`] to the [`AnyAlgebra`] that decides it.
///
/// This is the table the structured combinators (M1: `Product`/`Sum`/
/// `Collection`/`Tree`) consult to fetch the algebra for a child sort. M0 ships
/// the scalar table; M1 adds `from_grammar` (deriving the active sorts and their
/// algebras from a generated language model) and structured entries.
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

    /// The default scalar registry: `Int` over `[int_lo, int_hi)`, `Char` over
    /// the full Unicode range, and `Bool` over `bool_atoms`.
    pub fn scalars(int_lo: i64, int_hi: i64, bool_atoms: Vec<String>) -> Self {
        let mut registry = SortRegistry::new();
        registry.insert(Sort::Int, AnyAlgebra::Int(IntervalAlgebra::new(int_lo, int_hi)));
        registry.insert(Sort::Char, AnyAlgebra::Char(CharClassAlgebra::new()));
        registry.insert(Sort::Bool, AnyAlgebra::Bool(KatBooleanAlgebra::new(bool_atoms)));
        registry
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn int_universe() -> (i64, i64) {
        (0, 100)
    }

    /// The `AnyAlgebra::Int` wrapper answers `is_satisfiable`/`witness`/
    /// `evaluate` identically to the bare `IntervalAlgebra` for `Int` formulas.
    #[test]
    fn wrapper_matches_interval_suite() {
        let (lo, hi) = int_universe();
        let bare = IntervalAlgebra::new(lo, hi);
        let any = AnyAlgebra::Int(IntervalAlgebra::new(lo, hi));

        let preds = [
            IntervalPred::True,
            IntervalPred::False,
            IntervalPred::Range(10, 20),
            IntervalPred::Union(vec![(0, 5), (30, 40)]),
            IntervalPred::Not(Box::new(IntervalPred::Range(10, 20))),
        ];

        for p in &preds {
            let wrapped = AnyPred::Int(p.clone());
            assert_eq!(
                bare.is_satisfiable(p),
                any.is_satisfiable(&wrapped),
                "is_satisfiable mismatch for {p:?}",
            );
            assert_eq!(
                bare.witness(p),
                match any.witness(&wrapped) {
                    Some(AnyDomain::Int(v)) => Some(v),
                    None => None,
                    other => panic!("expected Int witness, got {other:?}"),
                },
                "witness mismatch for {p:?}",
            );
            for v in [0i64, 12, 35, 99] {
                assert_eq!(
                    bare.evaluate(p, &v),
                    any.evaluate(&wrapped, &AnyDomain::Int(v)),
                    "evaluate mismatch for {p:?} at {v}",
                );
            }
        }

        // Derived operations (and/or/not) match too.
        let a = AnyPred::Int(IntervalPred::Range(10, 50));
        let b = AnyPred::Int(IntervalPred::Range(30, 70));
        assert!(any.is_satisfiable(&any.and(&a, &b)));
        assert!(any.evaluate(&any.and(&a, &b), &AnyDomain::Int(40)));
        assert!(!any.evaluate(&any.and(&a, &b), &AnyDomain::Int(20)));
        assert!(any.evaluate(&any.or(&a, &b), &AnyDomain::Int(20)));
        assert!(!any.evaluate(&any.not(&a), &AnyDomain::Int(20)));
        assert!(any.evaluate(&any.not(&a), &AnyDomain::Int(5)));
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
            BooleanTest::Or(Box::new(p.clone()), Box::new(BooleanTest::Not(Box::new(q.clone())))),
            BooleanTest::And(Box::new(p.clone()), Box::new(BooleanTest::Not(Box::new(p.clone())))),
        ];

        for pred in &preds {
            let wrapped = AnyPred::Bool(pred.clone());
            assert_eq!(
                bare.is_satisfiable(pred),
                any.is_satisfiable(&wrapped),
                "is_satisfiable mismatch for {pred:?}",
            );
            assert_eq!(
                bare.witness(pred).is_some(),
                any.witness(&wrapped).is_some(),
                "witness presence mismatch for {pred:?}",
            );
        }
    }

    /// A cross-sort conjunction is unsatisfiable in every sort (no element is
    /// simultaneously two sorts).
    #[test]
    fn cross_sort_and_is_unsat() {
        let any_int = AnyAlgebra::Int(IntervalAlgebra::new(0, 100));
        let pred = any_int.and(
            &AnyPred::Int(IntervalPred::True),
            &AnyPred::Char(CharClassPred::True),
        );
        assert!(!any_int.is_satisfiable(&pred));

        let any_char = AnyAlgebra::Char(CharClassAlgebra::new());
        assert!(!any_char.is_satisfiable(&pred));
    }

    /// A cross-sort disjunction is satisfiable in a given sort only through that
    /// sort's disjunct.
    #[test]
    fn cross_sort_or_projects_per_sort() {
        let int_unsat = AnyPred::Int(IntervalPred::False);
        let char_sat = AnyPred::Char(CharClassPred::True);

        let any_int = AnyAlgebra::Int(IntervalAlgebra::new(0, 100));
        let or = any_int.or(&int_unsat, &char_sat);
        // The Int algebra can only witness the Int disjunct, which is `False`.
        assert!(!any_int.is_satisfiable(&or));

        // The Char algebra witnesses the Char disjunct.
        let any_char = AnyAlgebra::Char(CharClassAlgebra::new());
        assert!(any_char.is_satisfiable(&or));
    }

    /// Negating a foreign-sort leaf is `⊤` within this sort (an element of this
    /// sort is never a matching foreign-sort element).
    #[test]
    fn not_of_foreign_leaf_is_top_in_this_sort() {
        let any_int = AnyAlgebra::Int(IntervalAlgebra::new(0, 100));
        let not_char = any_int.not(&AnyPred::Char(CharClassPred::True));
        assert!(any_int.is_satisfiable(&not_char));
        assert!(any_int.evaluate(&not_char, &AnyDomain::Int(42)));
    }

    /// `evaluate` returns `false` when the element's sort differs from the
    /// algebra's sort.
    #[test]
    fn evaluate_rejects_foreign_sort_element() {
        let any_int = AnyAlgebra::Int(IntervalAlgebra::new(0, 100));
        let pred = AnyPred::Int(IntervalPred::True);
        assert!(any_int.evaluate(&pred, &AnyDomain::Int(1)));
        assert!(!any_int.evaluate(&pred, &AnyDomain::Char('a')));
    }

    /// The scalar registry exposes exactly the three scalar sorts.
    #[test]
    fn scalar_registry_has_three_sorts() {
        let registry = SortRegistry::scalars(0, 256, vec!["p".to_string()]);
        assert_eq!(registry.len(), 3);
        assert!(registry.contains(Sort::Int));
        assert!(registry.contains(Sort::Char));
        assert!(registry.contains(Sort::Bool));
        assert_eq!(registry.get(Sort::Int).map(AnyAlgebra::sort), Some(Sort::Int));
    }
}
