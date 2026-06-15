//! `AnyAlgebra` — the **uniform recursive carrier**: a single `BooleanAlgebra`
//! that can stand for any supported data type (scalar leaf *or* structured
//! combinator), so one symbolic automaton/transducer can guard predicates of any
//! type, and a tree node's heterogeneous children can share one algebra type.
//!
//! ## Design
//!
//! `AnyAlgebra` is a closed `enum` (no `dyn`, so `Predicate: Eq + Hash` survives
//! for minterm/determinization hashing). Scalar leaves wrap the concrete element
//! algebras; combinator variants box the generic combinator algebras
//! *instantiated at `AnyAlgebra` itself* — `Product(Box<NaryProductAlgebra<
//! AnyAlgebra>>)`, etc. — giving a finitely-nested uniform carrier. The
//! [`AnyPred`]/[`AnyDomain`] enums mirror this recursively (the `Box` breaks the
//! type cycle).
//!
//! ## Semantics
//!
//! Each leaf scalar follows the many-sorted projection semantics: a foreign-sort
//! leaf predicate projects to `⊥` when an algebra of another sort interprets a
//! formula (see [`fold_pred`]). Combinator variants **delegate** every operation
//! to their boxed inner algebra (extract the inner combinator predicate from the
//! `AnyPred` variant, call the inner algebra, re-wrap), so the recursion bottoms
//! out at the scalar leaves.

use std::collections::HashMap;

use num_bigint::BigInt;
use num_rational::BigRational;

use crate::collection_algebra::{BagAlgebra, BagPred};
use crate::kat::BooleanTest;
use crate::ordered_field::{OrderedF64, OrderedFieldAlgebra, OrderedFieldPred};
use crate::product_nary::{
    NaryProductAlgebra, NaryProductPred, SumAlgebra, SumPred, SumValue,
};
use crate::regex_sfa::{RegexAlgebra, RegexPred};
use crate::string_algebra::{StrPred, StringAlgebra};
use crate::sym_tree::{SymTerm, TreeAlgebra, TreePred};
use crate::symbolic::{
    BooleanAlgebra, CharClassAlgebra, CharClassPred, IntervalAlgebra, IntervalPred,
    KatBooleanAlgebra,
};

// ══════════════════════════════════════════════════════════════════════════════
// Sort
// ══════════════════════════════════════════════════════════════════════════════

/// The sort (data type) an algebra ranges over.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Sort {
    /// Bounded integers.
    Int,
    /// Unicode characters.
    Char,
    /// Propositional truth assignments.
    Bool,
    /// Arbitrary-precision integers.
    BigInt,
    /// Exact rationals.
    BigRat,
    /// Fixed-point decimals (rational carrier, distinct sort).
    Fixed,
    /// Floats.
    Float,
    /// Strings.
    Str,
    /// Tuples / records.
    Product,
    /// Variants / sums.
    Sum,
    /// Sequences.
    List,
    /// Multisets.
    Bag,
    /// Ranked terms (recursive ADTs).
    Tree,
}

// ══════════════════════════════════════════════════════════════════════════════
// AnyDomain — the disjoint union of per-sort domains
// ══════════════════════════════════════════════════════════════════════════════

/// A concrete element of one of the supported sorts.
#[derive(Clone, Debug)]
pub enum AnyDomain {
    /// Integer (`Sort::Int`).
    Int(i64),
    /// Character (`Sort::Char`).
    Char(char),
    /// Truth assignment (`Sort::Bool`).
    Bool(HashMap<String, bool>),
    /// Arbitrary-precision integer (`Sort::BigInt`).
    BigInt(BigInt),
    /// Exact rational (`Sort::BigRat`).
    BigRat(BigRational),
    /// Fixed-point decimal as a rational (`Sort::Fixed`).
    Fixed(BigRational),
    /// Float (`Sort::Float`).
    Float(OrderedF64),
    /// String (`Sort::Str`).
    Str(String),
    /// Tuple (`Sort::Product`).
    Product(Vec<AnyDomain>),
    /// Tagged variant (`Sort::Sum`). Boxed — `SumValue` holds its payload inline.
    Sum(Box<SumValue<AnyDomain>>),
    /// Sequence (`Sort::List`).
    List(Vec<AnyDomain>),
    /// Multiset (`Sort::Bag`).
    Bag(Vec<AnyDomain>),
    /// Ranked term (`Sort::Tree`). Boxed — `SymTerm` holds its payload inline.
    Tree(Box<SymTerm<AnyDomain>>),
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
            AnyDomain::Str(_) => Sort::Str,
            AnyDomain::Product(_) => Sort::Product,
            AnyDomain::Sum(_) => Sort::Sum,
            AnyDomain::List(_) => Sort::List,
            AnyDomain::Bag(_) => Sort::Bag,
            AnyDomain::Tree(_) => Sort::Tree,
        }
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// AnyPred — boolean combinations of per-sort leaf predicates
// ══════════════════════════════════════════════════════════════════════════════

/// A predicate over [`AnyDomain`].
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum AnyPred {
    /// Satisfied by every element.
    True,
    /// Satisfied by no element.
    False,
    /// Integer-sort leaf.
    Int(IntervalPred),
    /// Character-sort leaf.
    Char(CharClassPred),
    /// Boolean-sort leaf.
    Bool(BooleanTest),
    /// Big-integer-sort leaf.
    BigInt(OrderedFieldPred<BigInt>),
    /// Rational-sort leaf.
    BigRat(OrderedFieldPred<BigRational>),
    /// Fixed-point-sort leaf.
    Fixed(OrderedFieldPred<BigRational>),
    /// Float-sort leaf.
    Float(OrderedFieldPred<OrderedF64>),
    /// String-sort leaf.
    Str(StrPred),
    /// Tuple predicate.
    Product(Box<NaryProductPred<AnyPred>>),
    /// Variant predicate.
    Sum(Box<SumPred<AnyPred>>),
    /// Sequence predicate.
    List(Box<RegexPred<AnyPred>>),
    /// Multiset predicate.
    Bag(Box<BagPred<AnyPred>>),
    /// Tree predicate.
    Tree(Box<TreePred<AnyPred>>),
    /// Conjunction.
    And(Box<AnyPred>, Box<AnyPred>),
    /// Disjunction.
    Or(Box<AnyPred>, Box<AnyPred>),
    /// Negation.
    Not(Box<AnyPred>),
}

impl AnyPred {
    /// If this is a leaf predicate, the sort it constrains.
    pub fn leaf_sort(&self) -> Option<Sort> {
        match self {
            AnyPred::Int(_) => Some(Sort::Int),
            AnyPred::Char(_) => Some(Sort::Char),
            AnyPred::Bool(_) => Some(Sort::Bool),
            AnyPred::BigInt(_) => Some(Sort::BigInt),
            AnyPred::BigRat(_) => Some(Sort::BigRat),
            AnyPred::Fixed(_) => Some(Sort::Fixed),
            AnyPred::Float(_) => Some(Sort::Float),
            AnyPred::Str(_) => Some(Sort::Str),
            AnyPred::Product(_) => Some(Sort::Product),
            AnyPred::Sum(_) => Some(Sort::Sum),
            AnyPred::List(_) => Some(Sort::List),
            AnyPred::Bag(_) => Some(Sort::Bag),
            AnyPred::Tree(_) => Some(Sort::Tree),
            AnyPred::True | AnyPred::False | AnyPred::And(..) | AnyPred::Or(..) | AnyPred::Not(_) => {
                None
            },
        }
    }

    /// Whether this is a leaf (non-boolean-combination) node.
    fn is_leaf(&self) -> bool {
        self.leaf_sort().is_some()
    }
}

/// Project an [`AnyPred`] onto a single sort's algebra `alg`, evaluating the
/// boolean structure inside it. `leaf` extracts the inner predicate for `alg`'s
/// sort; leaves of any other sort project to `⊥`.
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
        other if other.is_leaf() => leaf(other).unwrap_or_else(|| alg.false_pred()),
        _ => unreachable!("all non-leaf cases handled above"),
    }
}

fn int_leaf(p: &AnyPred) -> Option<IntervalPred> {
    if let AnyPred::Int(x) = p { Some(x.clone()) } else { None }
}
fn char_leaf(p: &AnyPred) -> Option<CharClassPred> {
    if let AnyPred::Char(x) = p { Some(x.clone()) } else { None }
}
fn bool_leaf(p: &AnyPred) -> Option<BooleanTest> {
    if let AnyPred::Bool(x) = p { Some(x.clone()) } else { None }
}
fn bigint_leaf(p: &AnyPred) -> Option<OrderedFieldPred<BigInt>> {
    if let AnyPred::BigInt(x) = p { Some(x.clone()) } else { None }
}
fn bigrat_leaf(p: &AnyPred) -> Option<OrderedFieldPred<BigRational>> {
    if let AnyPred::BigRat(x) = p { Some(x.clone()) } else { None }
}
fn fixed_leaf(p: &AnyPred) -> Option<OrderedFieldPred<BigRational>> {
    if let AnyPred::Fixed(x) = p { Some(x.clone()) } else { None }
}
fn float_leaf(p: &AnyPred) -> Option<OrderedFieldPred<OrderedF64>> {
    if let AnyPred::Float(x) = p { Some(x.clone()) } else { None }
}
fn str_leaf(p: &AnyPred) -> Option<StrPred> {
    if let AnyPred::Str(x) = p { Some(x.clone()) } else { None }
}
fn product_leaf(p: &AnyPred) -> Option<NaryProductPred<AnyPred>> {
    if let AnyPred::Product(x) = p { Some((**x).clone()) } else { None }
}
fn sum_leaf(p: &AnyPred) -> Option<SumPred<AnyPred>> {
    if let AnyPred::Sum(x) = p { Some((**x).clone()) } else { None }
}
fn list_leaf(p: &AnyPred) -> Option<RegexPred<AnyPred>> {
    if let AnyPred::List(x) = p { Some((**x).clone()) } else { None }
}
fn bag_leaf(p: &AnyPred) -> Option<BagPred<AnyPred>> {
    if let AnyPred::Bag(x) = p { Some((**x).clone()) } else { None }
}
fn tree_leaf(p: &AnyPred) -> Option<TreePred<AnyPred>> {
    if let AnyPred::Tree(x) = p { Some((**x).clone()) } else { None }
}

// ══════════════════════════════════════════════════════════════════════════════
// AnyAlgebra
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
    /// String algebra.
    Str(StringAlgebra),
    /// Tuple algebra.
    Product(Box<NaryProductAlgebra<AnyAlgebra>>),
    /// Variant algebra.
    Sum(Box<SumAlgebra<AnyAlgebra>>),
    /// Sequence algebra.
    List(Box<RegexAlgebra<AnyAlgebra>>),
    /// Multiset algebra.
    Bag(Box<BagAlgebra<AnyAlgebra>>),
    /// Tree algebra.
    Tree(Box<TreeAlgebra<AnyAlgebra>>),
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
            AnyAlgebra::Str(_) => Sort::Str,
            AnyAlgebra::Product(_) => Sort::Product,
            AnyAlgebra::Sum(_) => Sort::Sum,
            AnyAlgebra::List(_) => Sort::List,
            AnyAlgebra::Bag(_) => Sort::Bag,
            AnyAlgebra::Tree(_) => Sort::Tree,
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
            // Same-sort leaves: delegate to the inner algebra (normalized, exact).
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
                (AnyAlgebra::Str(g), AnyPred::Str(x), AnyPred::Str(y)) => AnyPred::Str(g.and(x, y)),
                (AnyAlgebra::Product(g), AnyPred::Product(x), AnyPred::Product(y)) => {
                    AnyPred::Product(Box::new(g.and(x, y)))
                },
                (AnyAlgebra::Sum(g), AnyPred::Sum(x), AnyPred::Sum(y)) => {
                    AnyPred::Sum(Box::new(g.and(x, y)))
                },
                (AnyAlgebra::List(g), AnyPred::List(x), AnyPred::List(y)) => {
                    AnyPred::List(Box::new(g.and(x, y)))
                },
                (AnyAlgebra::Bag(g), AnyPred::Bag(x), AnyPred::Bag(y)) => {
                    AnyPred::Bag(Box::new(g.and(x, y)))
                },
                (AnyAlgebra::Tree(g), AnyPred::Tree(x), AnyPred::Tree(y)) => {
                    AnyPred::Tree(Box::new(g.and(x, y)))
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
                (AnyAlgebra::Str(g), AnyPred::Str(x), AnyPred::Str(y)) => AnyPred::Str(g.or(x, y)),
                (AnyAlgebra::Product(g), AnyPred::Product(x), AnyPred::Product(y)) => {
                    AnyPred::Product(Box::new(g.or(x, y)))
                },
                (AnyAlgebra::Sum(g), AnyPred::Sum(x), AnyPred::Sum(y)) => {
                    AnyPred::Sum(Box::new(g.or(x, y)))
                },
                (AnyAlgebra::List(g), AnyPred::List(x), AnyPred::List(y)) => {
                    AnyPred::List(Box::new(g.or(x, y)))
                },
                (AnyAlgebra::Bag(g), AnyPred::Bag(x), AnyPred::Bag(y)) => {
                    AnyPred::Bag(Box::new(g.or(x, y)))
                },
                (AnyAlgebra::Tree(g), AnyPred::Tree(x), AnyPred::Tree(y)) => {
                    AnyPred::Tree(Box::new(g.or(x, y)))
                },
                _ => AnyPred::Or(Box::new(a.clone()), Box::new(b.clone())),
            },
        }
    }

    fn not(&self, a: &AnyPred) -> AnyPred {
        match (self, a) {
            (_, AnyPred::True) => AnyPred::False,
            (_, AnyPred::False) => AnyPred::True,
            (_, AnyPred::Not(inner)) => (**inner).clone(),
            (AnyAlgebra::Int(g), AnyPred::Int(x)) => AnyPred::Int(g.not(x)),
            (AnyAlgebra::Char(g), AnyPred::Char(x)) => AnyPred::Char(g.not(x)),
            (AnyAlgebra::Bool(g), AnyPred::Bool(x)) => AnyPred::Bool(g.not(x)),
            (AnyAlgebra::BigInt(g), AnyPred::BigInt(x)) => AnyPred::BigInt(g.not(x)),
            (AnyAlgebra::BigRat(g), AnyPred::BigRat(x)) => AnyPred::BigRat(g.not(x)),
            (AnyAlgebra::Fixed(g), AnyPred::Fixed(x)) => AnyPred::Fixed(g.not(x)),
            (AnyAlgebra::Float(g), AnyPred::Float(x)) => AnyPred::Float(g.not(x)),
            (AnyAlgebra::Str(g), AnyPred::Str(x)) => AnyPred::Str(g.not(x)),
            (AnyAlgebra::Product(g), AnyPred::Product(x)) => AnyPred::Product(Box::new(g.not(x))),
            (AnyAlgebra::Sum(g), AnyPred::Sum(x)) => AnyPred::Sum(Box::new(g.not(x))),
            (AnyAlgebra::List(g), AnyPred::List(x)) => AnyPred::List(Box::new(g.not(x))),
            (AnyAlgebra::Bag(g), AnyPred::Bag(x)) => AnyPred::Bag(Box::new(g.not(x))),
            (AnyAlgebra::Tree(g), AnyPred::Tree(x)) => AnyPred::Tree(Box::new(g.not(x))),
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
            AnyAlgebra::Str(g) => g.is_satisfiable(&fold_pred(g, a, &str_leaf)),
            AnyAlgebra::Product(g) => g.is_satisfiable(&fold_pred(g.as_ref(), a, &product_leaf)),
            AnyAlgebra::Sum(g) => g.is_satisfiable(&fold_pred(g.as_ref(), a, &sum_leaf)),
            AnyAlgebra::List(g) => g.is_satisfiable(&fold_pred(g.as_ref(), a, &list_leaf)),
            AnyAlgebra::Bag(g) => g.is_satisfiable(&fold_pred(g.as_ref(), a, &bag_leaf)),
            AnyAlgebra::Tree(g) => g.is_satisfiable(&fold_pred(g.as_ref(), a, &tree_leaf)),
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
            AnyAlgebra::Str(g) => g.witness(&fold_pred(g, a, &str_leaf)).map(AnyDomain::Str),
            AnyAlgebra::Product(g) => {
                g.witness(&fold_pred(g.as_ref(), a, &product_leaf)).map(AnyDomain::Product)
            },
            AnyAlgebra::Sum(g) => {
                g.witness(&fold_pred(g.as_ref(), a, &sum_leaf)).map(|v| AnyDomain::Sum(Box::new(v)))
            },
            AnyAlgebra::List(g) => {
                g.witness(&fold_pred(g.as_ref(), a, &list_leaf)).map(AnyDomain::List)
            },
            AnyAlgebra::Bag(g) => {
                g.witness(&fold_pred(g.as_ref(), a, &bag_leaf)).map(AnyDomain::Bag)
            },
            AnyAlgebra::Tree(g) => {
                g.witness(&fold_pred(g.as_ref(), a, &tree_leaf)).map(|v| AnyDomain::Tree(Box::new(v)))
            },
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
            (AnyAlgebra::Str(g), AnyDomain::Str(v)) => g.evaluate(&fold_pred(g, pred, &str_leaf), v),
            (AnyAlgebra::Product(g), AnyDomain::Product(v)) => {
                g.evaluate(&fold_pred(g.as_ref(), pred, &product_leaf), v)
            },
            (AnyAlgebra::Sum(g), AnyDomain::Sum(v)) => {
                g.evaluate(&fold_pred(g.as_ref(), pred, &sum_leaf), v)
            },
            (AnyAlgebra::List(g), AnyDomain::List(v)) => {
                g.evaluate(&fold_pred(g.as_ref(), pred, &list_leaf), v)
            },
            (AnyAlgebra::Bag(g), AnyDomain::Bag(v)) => {
                g.evaluate(&fold_pred(g.as_ref(), pred, &bag_leaf), v)
            },
            (AnyAlgebra::Tree(g), AnyDomain::Tree(v)) => {
                g.evaluate(&fold_pred(g.as_ref(), pred, &tree_leaf), v)
            },
            // Element not of this algebra's sort.
            _ => false,
        }
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// SortRegistry — sort → algebra lookup table
// ══════════════════════════════════════════════════════════════════════════════

/// Maps each active scalar [`Sort`] to the [`AnyAlgebra`] that decides it (the
/// table structured combinators consult for child sorts).
#[derive(Clone, Debug, Default)]
pub struct SortRegistry {
    algebras: HashMap<Sort, AnyAlgebra>,
}

impl SortRegistry {
    /// An empty registry.
    pub fn new() -> Self {
        SortRegistry { algebras: HashMap::new() }
    }
    /// Register the algebra for `sort`.
    pub fn insert(&mut self, sort: Sort, algebra: AnyAlgebra) {
        self.algebras.insert(sort, algebra);
    }
    /// The algebra for `sort`, if any.
    pub fn get(&self, sort: Sort) -> Option<&AnyAlgebra> {
        self.algebras.get(&sort)
    }
    /// Whether `sort` is active.
    pub fn contains(&self, sort: Sort) -> bool {
        self.algebras.contains_key(&sort)
    }
    /// Active sorts.
    pub fn sorts(&self) -> impl Iterator<Item = Sort> + '_ {
        self.algebras.keys().copied()
    }
    /// Number of active sorts.
    pub fn len(&self) -> usize {
        self.algebras.len()
    }
    /// Whether empty.
    pub fn is_empty(&self) -> bool {
        self.algebras.is_empty()
    }
    /// The default scalar registry (all seven scalar sorts).
    pub fn scalars(int_lo: i64, int_hi: i64, bool_atoms: Vec<String>) -> Self {
        let mut r = SortRegistry::new();
        r.insert(Sort::Int, AnyAlgebra::Int(IntervalAlgebra::new(int_lo, int_hi)));
        r.insert(Sort::Char, AnyAlgebra::Char(CharClassAlgebra::new()));
        r.insert(Sort::Bool, AnyAlgebra::Bool(KatBooleanAlgebra::new(bool_atoms)));
        r.insert(Sort::BigInt, AnyAlgebra::BigInt(OrderedFieldAlgebra::new()));
        r.insert(Sort::BigRat, AnyAlgebra::BigRat(OrderedFieldAlgebra::new()));
        r.insert(Sort::Fixed, AnyAlgebra::Fixed(OrderedFieldAlgebra::new()));
        r.insert(Sort::Float, AnyAlgebra::Float(OrderedFieldAlgebra::new()));
        r.insert(Sort::Str, AnyAlgebra::Str(StringAlgebra::new()));
        r
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::collection_algebra::BagAlgebra;
    use crate::product_nary::{NaryProductAlgebra, NaryProductPred, SumAlgebra, SumPred};
    use crate::regex_sfa::RegexAlgebra;
    use crate::string_algebra::StrPred;
    use crate::sym_tree::{SymTerm, TreeAlgebra, TreePred};

    fn bi(n: i64) -> BigInt {
        BigInt::from(n)
    }

    #[test]
    fn scalar_wrappers_match_bare() {
        let bare = IntervalAlgebra::new(0, 100);
        let any = AnyAlgebra::Int(IntervalAlgebra::new(0, 100));
        let p = IntervalPred::Range(10, 20);
        let wrapped = AnyPred::Int(p.clone());
        assert_eq!(bare.is_satisfiable(&p), any.is_satisfiable(&wrapped));
        assert!(any.evaluate(&wrapped, &AnyDomain::Int(15)));
        assert!(!any.evaluate(&wrapped, &AnyDomain::Int(25)));
    }

    #[test]
    fn str_leaf_in_any() {
        let any = AnyAlgebra::Str(StringAlgebra::new());
        let p = AnyPred::Str(StrPred::Literal("ab".to_string()));
        assert!(any.evaluate(&p, &AnyDomain::Str("ab".to_string())));
        assert!(!any.evaluate(&p, &AnyDomain::Str("ac".to_string())));
        assert!(any.is_satisfiable(&p));
    }

    /// A tuple of (Int, Str) carried by the uniform carrier.
    #[test]
    fn product_combinator_in_any() {
        let prod = NaryProductAlgebra::new(vec![
            AnyAlgebra::Int(IntervalAlgebra::new(0, 100)),
            AnyAlgebra::Str(StringAlgebra::new()),
        ]);
        let any = AnyAlgebra::Product(Box::new(prod));
        // field 0 (Int) in [10,20) AND field 1 (Str) = "x"
        let p = AnyPred::Product(Box::new(NaryProductPred::And(
            Box::new(NaryProductPred::Field(0, AnyPred::Int(IntervalPred::Range(10, 20)))),
            Box::new(NaryProductPred::Field(1, AnyPred::Str(StrPred::Literal("x".to_string())))),
        )));
        let good = AnyDomain::Product(vec![AnyDomain::Int(15), AnyDomain::Str("x".to_string())]);
        let bad = AnyDomain::Product(vec![AnyDomain::Int(15), AnyDomain::Str("y".to_string())]);
        assert!(any.evaluate(&p, &good));
        assert!(!any.evaluate(&p, &bad));
        assert!(any.is_satisfiable(&p));
        let w = any.witness(&p).expect("nonempty");
        assert!(any.evaluate(&p, &w));
    }

    /// A variant (Int | Str) carried by the uniform carrier.
    #[test]
    fn sum_combinator_in_any() {
        let sum = SumAlgebra::new(vec![
            AnyAlgebra::Int(IntervalAlgebra::new(0, 100)),
            AnyAlgebra::Str(StringAlgebra::new()),
        ]);
        let any = AnyAlgebra::Sum(Box::new(sum));
        let p = AnyPred::Sum(Box::new(SumPred::InVariant(
            0,
            AnyPred::Int(IntervalPred::Range(0, 10)),
        )));
        assert!(
            any.evaluate(&p, &AnyDomain::Sum(Box::new(SumValue { tag: 0, payload: AnyDomain::Int(5) })))
        );
        assert!(!any
            .evaluate(&p, &AnyDomain::Sum(Box::new(SumValue { tag: 0, payload: AnyDomain::Int(50) }))));
        assert!(!any.evaluate(
            &p,
            &AnyDomain::Sum(Box::new(SumValue { tag: 1, payload: AnyDomain::Str("x".to_string()) }))
        ));
        assert!(any.is_satisfiable(&p));
    }

    /// A list of BigInts carried by the uniform carrier.
    #[test]
    fn list_combinator_in_any() {
        let list = RegexAlgebra::new(AnyAlgebra::BigInt(OrderedFieldAlgebra::new()));
        let all_pos = list.all(AnyPred::BigInt(OrderedFieldPred::at_least(bi(1))));
        let any = AnyAlgebra::List(Box::new(list));
        let p = AnyPred::List(Box::new(all_pos));
        assert!(any.evaluate(
            &p,
            &AnyDomain::List(vec![AnyDomain::BigInt(bi(1)), AnyDomain::BigInt(bi(5))])
        ));
        assert!(!any.evaluate(
            &p,
            &AnyDomain::List(vec![AnyDomain::BigInt(bi(1)), AnyDomain::BigInt(bi(0))])
        ));
        assert!(any.is_satisfiable(&p));
    }

    /// A bag of ints carried by the uniform carrier.
    #[test]
    fn bag_combinator_in_any() {
        let bag = BagAlgebra::new(AnyAlgebra::Int(IntervalAlgebra::new(0, 100)));
        let some_big = bag.any_elem(AnyPred::Int(IntervalPred::Range(50, 100)));
        let any = AnyAlgebra::Bag(Box::new(bag));
        let p = AnyPred::Bag(Box::new(some_big));
        assert!(any.evaluate(&p, &AnyDomain::Bag(vec![AnyDomain::Int(1), AnyDomain::Int(60)])));
        assert!(!any.evaluate(&p, &AnyDomain::Bag(vec![AnyDomain::Int(1), AnyDomain::Int(2)])));
        assert!(any.is_satisfiable(&p));
    }

    /// A tree with scalar payloads carried by the uniform carrier.
    #[test]
    fn tree_combinator_in_any() {
        let arities: HashMap<String, usize> =
            [("Lit".to_string(), 0usize), ("Pair".to_string(), 2usize)].into_iter().collect();
        let payloaded: std::collections::HashSet<String> = ["Lit".to_string()].into_iter().collect();
        let tree =
            TreeAlgebra::new(AnyAlgebra::Int(IntervalAlgebra::new(0, 100)), arities, payloaded);
        let any = AnyAlgebra::Tree(Box::new(tree));
        // Pattern: Lit with payload in [0,10)
        let p = AnyPred::Tree(Box::new(TreePred::Node {
            constructor: "Lit".to_string(),
            payload_guard: Some(AnyPred::Int(IntervalPred::Range(0, 10))),
            children: vec![],
        }));
        let small = AnyDomain::Tree(Box::new(SymTerm::leaf("Lit", AnyDomain::Int(5))));
        let big = AnyDomain::Tree(Box::new(SymTerm::leaf("Lit", AnyDomain::Int(50))));
        assert!(any.evaluate(&p, &small));
        assert!(!any.evaluate(&p, &big));
        assert!(any.is_satisfiable(&p));
        assert!(any.evaluate(&p, &any.witness(&p).unwrap()));
    }

    #[test]
    fn cross_sort_and_is_unsat() {
        let any_int = AnyAlgebra::Int(IntervalAlgebra::new(0, 100));
        let pred = any_int.and(&AnyPred::Int(IntervalPred::True), &AnyPred::Char(CharClassPred::True));
        assert!(!any_int.is_satisfiable(&pred));
    }

    #[test]
    fn scalar_registry_has_eight_scalar_sorts() {
        let r = SortRegistry::scalars(0, 256, vec!["p".to_string()]);
        assert_eq!(r.len(), 8);
        for s in [
            Sort::Int, Sort::Char, Sort::Bool, Sort::BigInt, Sort::BigRat, Sort::Fixed, Sort::Float,
            Sort::Str,
        ] {
            assert!(r.contains(s), "missing {s:?}");
        }
    }
}
