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

use crate::collection_algebra::{BagAlgebra, BagPred, MapAlgebra, MapPred, Singleton};
use crate::kat::BooleanTest;
use crate::ordered_field::{OrderedF64, OrderedFieldAlgebra, OrderedFieldPred};
use crate::product_nary::{NaryProductAlgebra, NaryProductPred, SumAlgebra, SumPred, SumValue};
use crate::regex_sfa::{RegexAlgebra, RegexPred};
use crate::string_algebra::{StrPred, StringAlgebra};
use crate::sym_tree::{SymTerm, TreeAlgebra, TreePred};
use crate::symbolic::{
    BooleanAlgebra, CharClassAlgebra, CharClassPred, IntervalAlgebra, IntervalPred,
    KatBooleanAlgebra,
};

#[path = "any_algebra/decision.rs"]
mod decision;
#[path = "any_algebra/lifecycle.rs"]
mod lifecycle;

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
    /// Key→value maps.
    Map,
}

// ══════════════════════════════════════════════════════════════════════════════
// AnyDomain — the disjoint union of per-sort domains
// ══════════════════════════════════════════════════════════════════════════════

/// A concrete element of one of the supported sorts.
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
    /// Key→value map (`Sort::Map`).
    Map(Vec<(AnyDomain, AnyDomain)>),
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
            AnyDomain::Map(_) => Sort::Map,
        }
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// AnyPred — boolean combinations of per-sort leaf predicates
// ══════════════════════════════════════════════════════════════════════════════

/// A predicate over [`AnyDomain`].
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
    /// Map predicate.
    Map(Box<MapPred<AnyPred, AnyPred>>),
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
            AnyPred::Map(_) => Some(Sort::Map),
            AnyPred::True
            | AnyPred::False
            | AnyPred::And(..)
            | AnyPred::Or(..)
            | AnyPred::Not(_) => None,
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
    enum Task<'pred> {
        Visit(&'pred AnyPred),
        And,
        Or,
        Not,
    }

    let mut tasks = vec![Task::Visit(p)];
    let mut values = Vec::new();
    while let Some(task) = tasks.pop() {
        match task {
            Task::Visit(AnyPred::True) => values.push(alg.true_pred()),
            Task::Visit(AnyPred::False) => values.push(alg.false_pred()),
            Task::Visit(AnyPred::And(left, right)) => {
                tasks.push(Task::And);
                tasks.push(Task::Visit(right));
                tasks.push(Task::Visit(left));
            },
            Task::Visit(AnyPred::Or(left, right)) => {
                tasks.push(Task::Or);
                tasks.push(Task::Visit(right));
                tasks.push(Task::Visit(left));
            },
            Task::Visit(AnyPred::Not(body)) => {
                tasks.push(Task::Not);
                tasks.push(Task::Visit(body));
            },
            Task::Visit(other) if other.is_leaf() => {
                values.push(leaf(other).unwrap_or_else(|| alg.false_pred()));
            },
            Task::Visit(_) => unreachable!("all non-leaf cases handled above"),
            kind @ (Task::And | Task::Or) => {
                let right = values.pop().expect("predicate fold lost right operand");
                let left = values.pop().expect("predicate fold lost left operand");
                values.push(match kind {
                    Task::And => alg.and(&left, &right),
                    Task::Or => alg.or(&left, &right),
                    _ => unreachable!(),
                });
            },
            Task::Not => {
                let body = values.pop().expect("predicate fold lost negated operand");
                values.push(alg.not(&body));
            },
        }
    }
    debug_assert_eq!(values.len(), 1);
    values.pop().expect("predicate fold produced no value")
}

fn int_leaf(p: &AnyPred) -> Option<IntervalPred> {
    if let AnyPred::Int(x) = p {
        Some(x.clone())
    } else {
        None
    }
}
fn char_leaf(p: &AnyPred) -> Option<CharClassPred> {
    if let AnyPred::Char(x) = p {
        Some(x.clone())
    } else {
        None
    }
}
fn bool_leaf(p: &AnyPred) -> Option<BooleanTest> {
    if let AnyPred::Bool(x) = p {
        Some(x.clone())
    } else {
        None
    }
}
fn bigint_leaf(p: &AnyPred) -> Option<OrderedFieldPred<BigInt>> {
    if let AnyPred::BigInt(x) = p {
        Some(x.clone())
    } else {
        None
    }
}
fn bigrat_leaf(p: &AnyPred) -> Option<OrderedFieldPred<BigRational>> {
    if let AnyPred::BigRat(x) = p {
        Some(x.clone())
    } else {
        None
    }
}
fn fixed_leaf(p: &AnyPred) -> Option<OrderedFieldPred<BigRational>> {
    if let AnyPred::Fixed(x) = p {
        Some(x.clone())
    } else {
        None
    }
}
fn float_leaf(p: &AnyPred) -> Option<OrderedFieldPred<OrderedF64>> {
    if let AnyPred::Float(x) = p {
        Some(x.clone())
    } else {
        None
    }
}
fn str_leaf(p: &AnyPred) -> Option<StrPred> {
    if let AnyPred::Str(x) = p {
        Some(x.clone())
    } else {
        None
    }
}
fn product_leaf(p: &AnyPred) -> Option<NaryProductPred<AnyPred>> {
    if let AnyPred::Product(x) = p {
        Some((**x).clone())
    } else {
        None
    }
}
fn sum_leaf(p: &AnyPred) -> Option<SumPred<AnyPred>> {
    if let AnyPred::Sum(x) = p {
        Some((**x).clone())
    } else {
        None
    }
}
fn list_leaf(p: &AnyPred) -> Option<RegexPred<AnyPred>> {
    if let AnyPred::List(x) = p {
        Some((**x).clone())
    } else {
        None
    }
}
fn bag_leaf(p: &AnyPred) -> Option<BagPred<AnyPred>> {
    if let AnyPred::Bag(x) = p {
        Some((**x).clone())
    } else {
        None
    }
}
fn tree_leaf(p: &AnyPred) -> Option<TreePred<AnyPred>> {
    if let AnyPred::Tree(x) = p {
        Some((**x).clone())
    } else {
        None
    }
}
fn map_leaf(p: &AnyPred) -> Option<MapPred<AnyPred, AnyPred>> {
    if let AnyPred::Map(x) = p {
        Some((**x).clone())
    } else {
        None
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// AnyAlgebra
// ══════════════════════════════════════════════════════════════════════════════

/// A single effective Boolean algebra, tagged by the sort it ranges over.
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
    /// Map algebra (key algebra must support `Singleton`; `AnyAlgebra` does).
    Map(Box<MapAlgebra<AnyAlgebra, AnyAlgebra>>),
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
            AnyAlgebra::Map(_) => Sort::Map,
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
                (AnyAlgebra::Map(g), AnyPred::Map(x), AnyPred::Map(y)) => {
                    AnyPred::Map(Box::new(g.and(x, y)))
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
                (AnyAlgebra::Map(g), AnyPred::Map(x), AnyPred::Map(y)) => {
                    AnyPred::Map(Box::new(g.or(x, y)))
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
            (AnyAlgebra::Map(g), AnyPred::Map(x)) => AnyPred::Map(Box::new(g.not(x))),
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
            AnyAlgebra::Map(g) => g.is_satisfiable(&fold_pred(g.as_ref(), a, &map_leaf)),
        }
    }

    fn witness(&self, a: &AnyPred) -> Option<AnyDomain> {
        match self {
            AnyAlgebra::Int(g) => g.witness(&fold_pred(g, a, &int_leaf)).map(AnyDomain::Int),
            AnyAlgebra::Char(g) => g.witness(&fold_pred(g, a, &char_leaf)).map(AnyDomain::Char),
            AnyAlgebra::Bool(g) => g.witness(&fold_pred(g, a, &bool_leaf)).map(AnyDomain::Bool),
            AnyAlgebra::BigInt(g) => g
                .witness(&fold_pred(g, a, &bigint_leaf))
                .map(AnyDomain::BigInt),
            AnyAlgebra::BigRat(g) => g
                .witness(&fold_pred(g, a, &bigrat_leaf))
                .map(AnyDomain::BigRat),
            AnyAlgebra::Fixed(g) => g
                .witness(&fold_pred(g, a, &fixed_leaf))
                .map(AnyDomain::Fixed),
            AnyAlgebra::Float(g) => g
                .witness(&fold_pred(g, a, &float_leaf))
                .map(AnyDomain::Float),
            AnyAlgebra::Str(g) => g.witness(&fold_pred(g, a, &str_leaf)).map(AnyDomain::Str),
            AnyAlgebra::Product(g) => g
                .witness(&fold_pred(g.as_ref(), a, &product_leaf))
                .map(AnyDomain::Product),
            AnyAlgebra::Sum(g) => g
                .witness(&fold_pred(g.as_ref(), a, &sum_leaf))
                .map(|v| AnyDomain::Sum(Box::new(v))),
            AnyAlgebra::List(g) => g
                .witness(&fold_pred(g.as_ref(), a, &list_leaf))
                .map(AnyDomain::List),
            AnyAlgebra::Bag(g) => g
                .witness(&fold_pred(g.as_ref(), a, &bag_leaf))
                .map(AnyDomain::Bag),
            AnyAlgebra::Tree(g) => g
                .witness(&fold_pred(g.as_ref(), a, &tree_leaf))
                .map(|v| AnyDomain::Tree(Box::new(v))),
            AnyAlgebra::Map(g) => g
                .witness(&fold_pred(g.as_ref(), a, &map_leaf))
                .map(AnyDomain::Map),
        }
    }

    fn evaluate(&self, pred: &AnyPred, elem: &AnyDomain) -> bool {
        decision::evaluate(self, pred, elem)
    }
}

/// Exact singleton construction across the recursive uniform carrier.
fn point_any(algebra: &AnyAlgebra, value: &AnyDomain) -> AnyPred {
    enum Task<'input> {
        Visit(&'input AnyAlgebra, &'input AnyDomain),
        VisitTree(&'input AnyAlgebra, &'input SymTerm<AnyDomain>),
        Product(usize),
        Sum(usize),
        List(usize),
        Bag {
            elem: &'input AnyAlgebra,
            total: usize,
            counts: Vec<u64>,
        },
        Tree {
            constructor: String,
            has_payload: bool,
            child_count: usize,
        },
        WrapTree,
        Map {
            key: &'input AnyAlgebra,
            val: &'input AnyAlgebra,
            count: usize,
        },
    }

    fn take_predicates(values: &mut Vec<AnyPred>, count: usize) -> Vec<AnyPred> {
        let start = values
            .len()
            .checked_sub(count)
            .expect("singleton PDA lost predicates");
        values.split_off(start)
    }

    let mut tasks = vec![Task::Visit(algebra, value)];
    let mut predicates = Vec::new();
    let mut trees = Vec::new();
    while let Some(task) = tasks.pop() {
        match task {
            Task::Visit(AnyAlgebra::Int(g), AnyDomain::Int(value)) => {
                predicates.push(AnyPred::Int(g.point(value)));
            },
            Task::Visit(AnyAlgebra::Char(g), AnyDomain::Char(value)) => {
                predicates.push(AnyPred::Char(g.point(value)));
            },
            Task::Visit(AnyAlgebra::Bool(g), AnyDomain::Bool(value)) => {
                predicates.push(AnyPred::Bool(g.point(value)));
            },
            Task::Visit(AnyAlgebra::BigInt(g), AnyDomain::BigInt(value)) => {
                predicates.push(AnyPred::BigInt(g.point(value)));
            },
            Task::Visit(AnyAlgebra::BigRat(g), AnyDomain::BigRat(value)) => {
                predicates.push(AnyPred::BigRat(g.point(value)));
            },
            Task::Visit(AnyAlgebra::Fixed(g), AnyDomain::Fixed(value)) => {
                predicates.push(AnyPred::Fixed(g.point(value)));
            },
            Task::Visit(AnyAlgebra::Float(g), AnyDomain::Float(value)) => {
                predicates.push(AnyPred::Float(g.point(value)));
            },
            Task::Visit(AnyAlgebra::Str(g), AnyDomain::Str(value)) => {
                predicates.push(AnyPred::Str(g.point(value)));
            },
            Task::Visit(AnyAlgebra::Product(g), AnyDomain::Product(values))
                if values.len() == g.fields.len() =>
            {
                tasks.push(Task::Product(values.len()));
                for (field, value) in g.fields.iter().zip(values).rev() {
                    tasks.push(Task::Visit(field, value));
                }
            },
            Task::Visit(AnyAlgebra::Sum(g), AnyDomain::Sum(value))
                if value.tag < g.variants.len() =>
            {
                tasks.push(Task::Sum(value.tag));
                tasks.push(Task::Visit(&g.variants[value.tag], &value.payload));
            },
            Task::Visit(AnyAlgebra::List(g), AnyDomain::List(values)) => {
                tasks.push(Task::List(values.len()));
                for value in values.iter().rev() {
                    tasks.push(Task::Visit(&g.elem, value));
                }
            },
            Task::Visit(AnyAlgebra::Bag(g), AnyDomain::Bag(values)) => {
                let mut groups: Vec<(&AnyDomain, u64)> = Vec::new();
                for value in values {
                    if let Some(group) = groups.iter_mut().find(|(domain, _)| *domain == value) {
                        group.1 += 1;
                    } else {
                        groups.push((value, 1));
                    }
                }
                let counts = groups.iter().map(|(_, count)| *count).collect();
                tasks.push(Task::Bag {
                    elem: &g.elem,
                    total: values.len(),
                    counts,
                });
                for (value, _) in groups.into_iter().rev() {
                    tasks.push(Task::Visit(&g.elem, value));
                }
            },
            Task::Visit(AnyAlgebra::Tree(g), AnyDomain::Tree(term)) => {
                tasks.push(Task::WrapTree);
                tasks.push(Task::VisitTree(&g.elem, term));
            },
            Task::Visit(AnyAlgebra::Map(g), AnyDomain::Map(entries)) => {
                tasks.push(Task::Map {
                    key: &g.key,
                    val: &g.val,
                    count: entries.len(),
                });
                for (key, value) in entries.iter().rev() {
                    tasks.push(Task::Visit(&g.val, value));
                    tasks.push(Task::Visit(&g.key, key));
                }
            },
            Task::Visit(_, _) => predicates.push(AnyPred::False),
            Task::VisitTree(elem, term) => {
                tasks.push(Task::Tree {
                    constructor: term.constructor.clone(),
                    has_payload: term.payload.is_some(),
                    child_count: term.children.len(),
                });
                for child in term.children.iter().rev() {
                    tasks.push(Task::VisitTree(elem, child));
                }
                if let Some(payload) = &term.payload {
                    tasks.push(Task::Visit(elem, payload));
                }
            },
            Task::Product(count) => {
                let fields = take_predicates(&mut predicates, count);
                let mut acc = NaryProductPred::True;
                for (index, predicate) in fields.into_iter().enumerate() {
                    let atom = NaryProductPred::Field(index, predicate);
                    acc = match acc {
                        NaryProductPred::True => atom,
                        other => NaryProductPred::And(Box::new(other), Box::new(atom)),
                    };
                }
                predicates.push(AnyPred::Product(Box::new(acc)));
            },
            Task::Sum(tag) => {
                let payload = predicates.pop().expect("singleton PDA lost sum payload");
                predicates.push(AnyPred::Sum(Box::new(SumPred::InVariant(tag, payload))));
            },
            Task::List(count) => {
                let elements = take_predicates(&mut predicates, count);
                let mut acc = RegexPred::Epsilon;
                for predicate in elements {
                    acc = RegexPred::Concat(Box::new(acc), Box::new(RegexPred::Elem(predicate)));
                }
                predicates.push(AnyPred::List(Box::new(acc)));
            },
            Task::Bag { elem, total, counts } => {
                let classes = take_predicates(&mut predicates, counts.len());
                let mut acc = BagPred::Count {
                    class: elem.true_pred(),
                    lo: total as u64,
                    hi: Some(total as u64),
                };
                for (class, count) in classes.into_iter().zip(counts) {
                    let atom = BagPred::Count { class, lo: count, hi: Some(count) };
                    acc = BagPred::And(Box::new(acc), Box::new(atom));
                }
                predicates.push(AnyPred::Bag(Box::new(acc)));
            },
            Task::Tree { constructor, has_payload, child_count } => {
                let child_start = trees
                    .len()
                    .checked_sub(child_count)
                    .expect("singleton PDA lost tree children");
                let children = trees.split_off(child_start);
                let payload_guard =
                    has_payload.then(|| predicates.pop().expect("singleton PDA lost tree payload"));
                trees.push(TreePred::Node { constructor, payload_guard, children });
            },
            Task::WrapTree => {
                let tree = trees.pop().expect("singleton PDA lost tree root");
                predicates.push(AnyPred::Tree(Box::new(tree)));
            },
            Task::Map { key, val, count } => {
                let entries = take_predicates(&mut predicates, count * 2);
                let mut acc = MapPred::CountEntries {
                    key_class: key.true_pred(),
                    val_class: val.true_pred(),
                    lo: count as u64,
                    hi: Some(count as u64),
                };
                let mut entries = entries.into_iter();
                while let Some(key_class) = entries.next() {
                    let val_class = entries.next().expect("singleton PDA lost map value");
                    let atom = MapPred::CountEntries { key_class, val_class, lo: 1, hi: Some(1) };
                    acc = MapPred::And(Box::new(acc), Box::new(atom));
                }
                predicates.push(AnyPred::Map(Box::new(acc)));
            },
        }
    }
    debug_assert!(trees.is_empty());
    debug_assert_eq!(predicates.len(), 1);
    predicates
        .pop()
        .expect("singleton PDA produced no predicate")
}

impl Singleton for AnyAlgebra {
    fn point(&self, value: &AnyDomain) -> AnyPred {
        point_any(self, value)
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

// ══════════════════════════════════════════════════════════════════════════════
// SortedGuard — a guard predicate tagged with the sort it constrains
// ══════════════════════════════════════════════════════════════════════════════

/// A guard predicate paired with the [`Sort`] of the value it constrains.
///
/// This is the OSLF carrier's unit of currency: instead of carrying a guard as
/// an untyped [`AnyPred`] (whose `leaf_sort` may be `None` for boolean
/// combinations), a `SortedGuard` records the *owning* sort explicitly so a
/// consumer can resolve the deciding algebra from a [`SortRegistry`] without
/// re-deriving it from the predicate shape. The `.0`-inert wiring produces
/// these but does not yet route live consumers through them (that is `.1`).
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct SortedGuard {
    /// The sort the value being guarded ranges over.
    pub sort: Sort,
    /// The predicate constraining that value.
    pub pred: AnyPred,
}

// ══════════════════════════════════════════════════════════════════════════════
// NativeKind → Sort  (OSLF carrier route)
// ══════════════════════════════════════════════════════════════════════════════

/// Map the parser's native-type classification ([`mettail_ast::language::NativeKind`])
/// to the carrier [`Sort`] that decides it.
///
/// Every bounded-integer width collapses to [`Sort::Int`] (the bounded
/// [`IntervalAlgebra`] universe); `Bool → Bool`, `Str → Str`,
/// `Float32/Float64 → Float`, `CanonicalBigInt → BigInt`,
/// `CanonicalBigRat → BigRat`, `CanonicalFixedPoint → Fixed`. `Other` (custom
/// wrappers, collection containers, user ADTs) has no scalar sort and returns
/// `None` — such a category is decided structurally, not by a scalar leaf.
///
/// This reuses the *real* `NativeKind` variants (it does not re-classify a
/// string), so the carrier's scalar resolution tracks the parser's
/// `NativeKind::from_syn_type` exactly.
pub fn sort_of_native(kind: mettail_ast::language::NativeKind) -> Option<Sort> {
    use mettail_ast::language::NativeKind;
    match kind {
        NativeKind::Int8
        | NativeKind::Int16
        | NativeKind::Int32
        | NativeKind::Int64
        | NativeKind::Int128
        | NativeKind::Isize
        | NativeKind::UInt8
        | NativeKind::UInt16
        | NativeKind::UInt32
        | NativeKind::UInt64
        | NativeKind::UInt128
        | NativeKind::Usize => Some(Sort::Int),
        NativeKind::Bool => Some(Sort::Bool),
        NativeKind::Str => Some(Sort::Str),
        NativeKind::Float32 | NativeKind::Float64 => Some(Sort::Float),
        NativeKind::CanonicalBigInt => Some(Sort::BigInt),
        NativeKind::CanonicalBigRat => Some(Sort::BigRat),
        NativeKind::CanonicalFixedPoint => Some(Sort::Fixed),
        NativeKind::Other => None,
    }
}

/// Resolve a parser [`CategoryInfo`](crate::pipeline::CategoryInfo)'s scalar
/// [`Sort`], if it has one.
///
/// `ci.native_type` is the *full path string* the bridge stores
/// (`native_type_to_full_string` — e.g. `"i32"`, `"mettail_runtime::CanonicalBigRat"`,
/// `"Vec < Proc >"`). This parses it back into a [`syn::Type`] and classifies
/// it with the **same** `NativeKind::from_syn_type` the parser uses (which keys
/// off the last path segment), then maps through [`sort_of_native`]. A category
/// with no `native_type`, an unparseable type, or an `Other` kind has no scalar
/// sort and returns `None`.
pub fn sort_of_category(ci: &crate::pipeline::CategoryInfo) -> Option<Sort> {
    let type_str = ci.native_type.as_deref()?;
    // Mirror the parser: classify by the last path segment via the real
    // `NativeKind::from_syn_type`. `native_type_to_full_string` collapses
    // `::` spacing but otherwise yields a parseable type; if a future bridge
    // ever stored an unparseable string the category is treated as non-scalar.
    let ty: syn::Type = syn::parse_str(type_str).ok()?;
    let kind = mettail_ast::language::NativeKind::from_syn_type(&ty);
    sort_of_native(kind)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::collection_algebra::{BagAlgebra, MapAlgebra, Singleton};
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

    // ══════════════════════════════════════════════════════════════════════
    // Wrapper faithfulness (M0 invariant) — property tests
    //
    // The carrier invariant `AnyAlgebra::<Sort>(leaf) ≡ leaf`: for every scalar
    // sort, the wrapped algebra decides the wrapped predicate exactly as the
    // bare leaf decides the bare predicate, on `is_satisfiable`, `witness`
    // (Some/None agreement + the carried witness genuinely satisfies the
    // wrapped predicate through the carrier), and `evaluate` (agreement on a
    // freely-chosen domain element). These three are the Rust counterpart of
    // the Coq `AnyAlgebraProjectionSound.v` wrapper-faithfulness theorem.
    //
    // Predicate / domain generators mirror the shapes the existing per-leaf
    // suites (Interval / CharClass / KAT / String / OrderedField) exercise.
    // ══════════════════════════════════════════════════════════════════════

    use num_rational::BigRational;
    use proptest::prelude::*;

    use crate::ordered_field::{OrderedF64, OrderedFieldPred};

    /// Assert the three faithfulness facts for one (bare algebra, wrapped
    /// algebra, bare pred, wrap-pred, wrap-domain) tuple at a single element.
    fn assert_faithful<L>(
        bare: &L,
        any: &AnyAlgebra,
        p: &L::Predicate,
        wrap_pred: impl Fn(&L::Predicate) -> AnyPred,
        wrap_dom: impl Fn(L::Domain) -> AnyDomain,
        elem: L::Domain,
    ) -> Result<(), proptest::test_runner::TestCaseError>
    where
        L: BooleanAlgebra,
    {
        let wrapped = wrap_pred(p);
        // (1) SAT agreement.
        prop_assert_eq!(bare.is_satisfiable(p), any.is_satisfiable(&wrapped));
        // (2) WITNESS Some/None agreement + carried witness validity.
        let bare_w = bare.witness(p);
        let any_w = any.witness(&wrapped);
        prop_assert_eq!(bare_w.is_some(), any_w.is_some());
        if let Some(d) = any_w {
            // The carrier's own witness must satisfy the wrapped predicate
            // through the carrier (closes the loop without comparing the raw
            // domain elements, which the leaf is free to choose differently).
            prop_assert!(any.evaluate(&wrapped, &d));
        }
        // (3) EVALUATE agreement on a freely-chosen element.
        prop_assert_eq!(bare.evaluate(p, &elem), any.evaluate(&wrapped, &wrap_dom(elem)));
        Ok(())
    }

    // ── Int (IntervalAlgebra over [0,100)) ──────────────────────────────────
    prop_compose! {
        fn arb_interval_pred()(
            choice in 0u8..6,
            a in 0i64..100, b in 0i64..100,
        ) -> IntervalPred {
            let (lo, hi) = (a.min(b), a.max(b) + 1);
            match choice {
                0 => IntervalPred::True,
                1 => IntervalPred::False,
                2 => IntervalPred::Range(lo, hi),
                3 => IntervalPred::Union(vec![(lo, hi)]),
                4 => IntervalPred::Not(Box::new(IntervalPred::Range(lo, hi))),
                _ => IntervalPred::Range(a, a + 1),
            }
        }
    }

    proptest! {
        #[test]
        fn faithful_int(p in arb_interval_pred(), e in 0i64..100) {
            let bare = IntervalAlgebra::new(0, 100);
            let any = AnyAlgebra::Int(IntervalAlgebra::new(0, 100));
            assert_faithful(&bare, &any, &p, |q| AnyPred::Int(q.clone()), AnyDomain::Int, e)?;
        }
    }

    // ── Char (CharClassAlgebra) ─────────────────────────────────────────────
    prop_compose! {
        fn arb_charclass_pred()(
            choice in 0u8..5,
            a in 0u32..128, b in 0u32..128,
        ) -> CharClassPred {
            let ca = char::from_u32(a).unwrap_or('a');
            let cb = char::from_u32(b).unwrap_or('z');
            let (lo, hi) = if ca <= cb { (ca, cb) } else { (cb, ca) };
            match choice {
                0 => CharClassPred::True,
                1 => CharClassPred::False,
                2 => CharClassPred::Range(lo, hi),
                3 => CharClassPred::Union(vec![(lo, hi)]),
                _ => CharClassPred::Not(Box::new(CharClassPred::Range(lo, hi))),
            }
        }
    }

    proptest! {
        #[test]
        fn faithful_char(p in arb_charclass_pred(), e in 0u32..128) {
            let bare = CharClassAlgebra::new();
            let any = AnyAlgebra::Char(CharClassAlgebra::new());
            let ce = char::from_u32(e).unwrap_or('a');
            assert_faithful(&bare, &any, &p, |q| AnyPred::Char(q.clone()), AnyDomain::Char, ce)?;
        }
    }

    // ── Bool (KatBooleanAlgebra over atoms {p,q}) ───────────────────────────
    fn arb_boolean_test() -> impl Strategy<Value = BooleanTest> {
        let leaf = prop_oneof![
            Just(BooleanTest::True),
            Just(BooleanTest::False),
            Just(BooleanTest::Atom("p".to_string())),
            Just(BooleanTest::Atom("q".to_string())),
        ];
        leaf.prop_recursive(3, 8, 2, |inner| {
            prop_oneof![
                inner.clone().prop_map(|t| BooleanTest::not(t)),
                (inner.clone(), inner.clone()).prop_map(|(a, b)| BooleanTest::and(a, b)),
                (inner.clone(), inner).prop_map(|(a, b)| BooleanTest::or(a, b)),
            ]
        })
    }

    prop_compose! {
        fn arb_bool_valuation()(p in any::<bool>(), q in any::<bool>()) -> HashMap<String, bool> {
            let mut m = HashMap::new();
            m.insert("p".to_string(), p);
            m.insert("q".to_string(), q);
            m
        }
    }

    proptest! {
        #[test]
        fn faithful_bool(p in arb_boolean_test(), v in arb_bool_valuation()) {
            let atoms = vec!["p".to_string(), "q".to_string()];
            let bare = KatBooleanAlgebra::new(atoms.clone());
            let any = AnyAlgebra::Bool(KatBooleanAlgebra::new(atoms));
            assert_faithful(&bare, &any, &p, |q| AnyPred::Bool(q.clone()), AnyDomain::Bool, v)?;
        }
    }

    // ── BigInt (OrderedFieldAlgebra<BigInt>) ────────────────────────────────
    prop_compose! {
        fn arb_bigint_pred()(choice in 0u8..6, a in -50i64..50, b in -50i64..50) -> OrderedFieldPred<BigInt> {
            let (lo, hi) = (a.min(b), a.max(b));
            match choice {
                0 => OrderedFieldPred::top(),
                1 => OrderedFieldPred::bottom(),
                2 => OrderedFieldPred::closed(bi(lo), bi(hi)),
                3 => OrderedFieldPred::at_least(bi(lo)),
                4 => OrderedFieldPred::at_most(bi(hi)),
                _ => OrderedFieldPred::point(bi(a)),
            }
        }
    }

    proptest! {
        #[test]
        fn faithful_bigint(p in arb_bigint_pred(), e in -50i64..50) {
            let bare = OrderedFieldAlgebra::<BigInt>::new();
            let any = AnyAlgebra::BigInt(OrderedFieldAlgebra::<BigInt>::new());
            assert_faithful(&bare, &any, &p, |q| AnyPred::BigInt(q.clone()), AnyDomain::BigInt, bi(e))?;
        }
    }

    // ── BigRat / Fixed (OrderedFieldAlgebra<BigRational>) ────────────────────
    prop_compose! {
        fn arb_rational_pred()(choice in 0u8..6, a in -20i64..20, b in -20i64..20) -> OrderedFieldPred<BigRational> {
            let ra = BigRational::from(bi(a.min(b)));
            let rb = BigRational::from(bi(a.max(b)));
            match choice {
                0 => OrderedFieldPred::top(),
                1 => OrderedFieldPred::bottom(),
                2 => OrderedFieldPred::closed(ra.clone(), rb),
                3 => OrderedFieldPred::at_least(ra),
                4 => OrderedFieldPred::at_most(rb),
                _ => OrderedFieldPred::point(BigRational::from(bi(a))),
            }
        }
    }

    proptest! {
        #[test]
        fn faithful_bigrat(p in arb_rational_pred(), e in -20i64..20) {
            let bare = OrderedFieldAlgebra::<BigRational>::new();
            let any = AnyAlgebra::BigRat(OrderedFieldAlgebra::<BigRational>::new());
            let re = BigRational::from(bi(e));
            assert_faithful(&bare, &any, &p, |q| AnyPred::BigRat(q.clone()), AnyDomain::BigRat, re)?;
        }

        #[test]
        fn faithful_fixed(p in arb_rational_pred(), e in -20i64..20) {
            let bare = OrderedFieldAlgebra::<BigRational>::new();
            let any = AnyAlgebra::Fixed(OrderedFieldAlgebra::<BigRational>::new());
            let re = BigRational::from(bi(e));
            assert_faithful(&bare, &any, &p, |q| AnyPred::Fixed(q.clone()), AnyDomain::Fixed, re)?;
        }
    }

    // ── Float (OrderedFieldAlgebra<OrderedF64>) ─────────────────────────────
    prop_compose! {
        fn arb_float_pred()(choice in 0u8..6, a in -100i64..100, b in -100i64..100) -> OrderedFieldPred<OrderedF64> {
            let fa = OrderedF64((a.min(b)) as f64);
            let fb = OrderedF64((a.max(b)) as f64);
            match choice {
                0 => OrderedFieldPred::top(),
                1 => OrderedFieldPred::bottom(),
                2 => OrderedFieldPred::closed(fa, fb),
                3 => OrderedFieldPred::at_least(fa),
                4 => OrderedFieldPred::at_most(fb),
                _ => OrderedFieldPred::point(OrderedF64(a as f64)),
            }
        }
    }

    proptest! {
        #[test]
        fn faithful_float(p in arb_float_pred(), e in -100i64..100) {
            let bare = OrderedFieldAlgebra::<OrderedF64>::new();
            let any = AnyAlgebra::Float(OrderedFieldAlgebra::<OrderedF64>::new());
            let fe = OrderedF64(e as f64);
            assert_faithful(&bare, &any, &p, |q| AnyPred::Float(q.clone()), AnyDomain::Float, fe)?;
        }
    }

    // ── Str (StringAlgebra) ─────────────────────────────────────────────────
    prop_compose! {
        fn arb_str_pred()(choice in 0u8..6, s in "[ab]{0,3}", lo in 0usize..3, extra in 0usize..3) -> StrPred {
            match choice {
                0 => StrPred::Empty,
                1 => StrPred::Epsilon,
                2 => StrPred::Literal(s),
                3 => StrPred::Length(lo, Some(lo + extra)),
                4 => StrPred::any(),
                _ => StrPred::char_range('a', 'b'),
            }
        }
    }

    proptest! {
        #[test]
        fn faithful_str(p in arb_str_pred(), e in "[ab]{0,4}") {
            let bare = StringAlgebra::new();
            let any = AnyAlgebra::Str(StringAlgebra::new());
            assert_faithful(&bare, &any, &p, |q| AnyPred::Str(q.clone()), AnyDomain::Str, e)?;
        }
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
        let p =
            AnyPred::Sum(Box::new(SumPred::InVariant(0, AnyPred::Int(IntervalPred::Range(0, 10)))));
        assert!(any.evaluate(
            &p,
            &AnyDomain::Sum(Box::new(SumValue { tag: 0, payload: AnyDomain::Int(5) }))
        ));
        assert!(!any.evaluate(
            &p,
            &AnyDomain::Sum(Box::new(SumValue { tag: 0, payload: AnyDomain::Int(50) }))
        ));
        assert!(!any.evaluate(
            &p,
            &AnyDomain::Sum(Box::new(SumValue {
                tag: 1,
                payload: AnyDomain::Str("x".to_string())
            }))
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
            [("Lit".to_string(), 0usize), ("Pair".to_string(), 2usize)]
                .into_iter()
                .collect();
        let payloaded: std::collections::HashSet<String> =
            ["Lit".to_string()].into_iter().collect();
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
        let pred =
            any_int.and(&AnyPred::Int(IntervalPred::True), &AnyPred::Char(CharClassPred::True));
        assert!(!any_int.is_satisfiable(&pred));
    }

    /// A map (Int → Str) carried by the uniform carrier (key=AnyAlgebra needs
    /// Singleton, which AnyAlgebra implements).
    #[test]
    fn map_combinator_in_any() {
        let map = MapAlgebra::new(
            AnyAlgebra::Int(IntervalAlgebra::new(0, 1000)),
            AnyAlgebra::Str(StringAlgebra::new()),
        );
        let p = map.entry(
            AnyPred::Int(IntervalPred::Range(0, 10)),
            AnyPred::Str(StrPred::Literal("x".to_string())),
        );
        let any = AnyAlgebra::Map(Box::new(map));
        let pred = AnyPred::Map(Box::new(p));
        let good = AnyDomain::Map(vec![(AnyDomain::Int(5), AnyDomain::Str("x".to_string()))]);
        let bad = AnyDomain::Map(vec![(AnyDomain::Int(5), AnyDomain::Str("y".to_string()))]);
        assert!(any.evaluate(&pred, &good));
        assert!(!any.evaluate(&pred, &bad));
        assert!(any.is_satisfiable(&pred));
        let w = any.witness(&pred).expect("nonempty");
        assert!(any.evaluate(&pred, &w));
    }

    /// `Singleton::point` over the carrier (scalars + a composite).
    #[test]
    fn singleton_points() {
        let any = AnyAlgebra::Int(IntervalAlgebra::new(0, 100));
        let pt = any.point(&AnyDomain::Int(42));
        assert!(any.evaluate(&pt, &AnyDomain::Int(42)));
        assert!(!any.evaluate(&pt, &AnyDomain::Int(43)));

        let prod = AnyAlgebra::Product(Box::new(NaryProductAlgebra::new(vec![
            AnyAlgebra::Int(IntervalAlgebra::new(0, 100)),
            AnyAlgebra::Str(StringAlgebra::new()),
        ])));
        let v = AnyDomain::Product(vec![AnyDomain::Int(7), AnyDomain::Str("k".to_string())]);
        let pt = prod.point(&v);
        assert!(prod.evaluate(&pt, &v));
        assert!(!prod.evaluate(
            &pt,
            &AnyDomain::Product(vec![AnyDomain::Int(8), AnyDomain::Str("k".to_string())])
        ));
    }

    #[test]
    fn scalar_registry_has_eight_scalar_sorts() {
        let r = SortRegistry::scalars(0, 256, vec!["p".to_string()]);
        assert_eq!(r.len(), 8);
        for s in [
            Sort::Int,
            Sort::Char,
            Sort::Bool,
            Sort::BigInt,
            Sort::BigRat,
            Sort::Fixed,
            Sort::Float,
            Sort::Str,
        ] {
            assert!(r.contains(s), "missing {s:?}");
        }
    }
}
