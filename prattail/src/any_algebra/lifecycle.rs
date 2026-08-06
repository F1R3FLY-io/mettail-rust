//! Unified heap-backed lifecycle machines for the recursive `Any*` carriers.
//!
//! The structured variants point back to the carrier through generic product, sum, regex, bag,
//! tree, and map wrappers. Delegating a lifecycle trait to those wrappers would therefore still
//! grow the native stack on an alternating `Any* -> wrapper -> Any*` chain. The machines below
//! traverse both sides of each boundary in one worklist.

use std::fmt;
use std::hash::{Hash, Hasher};

use super::{AnyAlgebra, AnyDomain, AnyPred};
use crate::collection_algebra::{BagAlgebra, BagPred, MapAlgebra, MapPred};
use crate::product_nary::{NaryProductAlgebra, NaryProductPred, SumAlgebra, SumPred, SumValue};
use crate::regex_sfa::{RegexAlgebra, RegexPred};
use crate::sym_tree::{SymTerm, TreeAlgebra, TreePred};
use crate::symbolic::IntervalAlgebra;

// ══════════════════════════════════════════════════════════════════════════════
// AnyDomain + embedded SumValue/SymTerm
// ══════════════════════════════════════════════════════════════════════════════

enum DomainCloneTask<'domain> {
    Domain(&'domain AnyDomain),
    Term(&'domain SymTerm<AnyDomain>),
    Product(usize),
    Sum(usize),
    List(usize),
    Bag(usize),
    Map(usize),
    Tree,
    BuildTerm {
        constructor: String,
        has_payload: bool,
        child_count: usize,
    },
}

impl Clone for AnyDomain {
    fn clone(&self) -> Self {
        let mut tasks = vec![DomainCloneTask::Domain(self)];
        let mut domains = Vec::new();
        let mut terms = Vec::new();
        while let Some(task) = tasks.pop() {
            match task {
                DomainCloneTask::Domain(AnyDomain::Int(value)) => {
                    domains.push(AnyDomain::Int(*value));
                },
                DomainCloneTask::Domain(AnyDomain::Char(value)) => {
                    domains.push(AnyDomain::Char(*value));
                },
                DomainCloneTask::Domain(AnyDomain::Bool(value)) => {
                    domains.push(AnyDomain::Bool(value.clone()));
                },
                DomainCloneTask::Domain(AnyDomain::BigInt(value)) => {
                    domains.push(AnyDomain::BigInt(value.clone()));
                },
                DomainCloneTask::Domain(AnyDomain::BigRat(value)) => {
                    domains.push(AnyDomain::BigRat(value.clone()));
                },
                DomainCloneTask::Domain(AnyDomain::Fixed(value)) => {
                    domains.push(AnyDomain::Fixed(value.clone()));
                },
                DomainCloneTask::Domain(AnyDomain::Float(value)) => {
                    domains.push(AnyDomain::Float(*value));
                },
                DomainCloneTask::Domain(AnyDomain::Str(value)) => {
                    domains.push(AnyDomain::Str(value.clone()));
                },
                DomainCloneTask::Domain(AnyDomain::Product(values)) => {
                    push_domain_sequence(
                        &mut tasks,
                        DomainCloneTask::Product(values.len()),
                        values,
                    );
                },
                DomainCloneTask::Domain(AnyDomain::Sum(value)) => {
                    tasks.push(DomainCloneTask::Sum(value.tag));
                    tasks.push(DomainCloneTask::Domain(&value.payload));
                },
                DomainCloneTask::Domain(AnyDomain::List(values)) => {
                    push_domain_sequence(&mut tasks, DomainCloneTask::List(values.len()), values);
                },
                DomainCloneTask::Domain(AnyDomain::Bag(values)) => {
                    push_domain_sequence(&mut tasks, DomainCloneTask::Bag(values.len()), values);
                },
                DomainCloneTask::Domain(AnyDomain::Tree(term)) => {
                    tasks.push(DomainCloneTask::Tree);
                    tasks.push(DomainCloneTask::Term(term));
                },
                DomainCloneTask::Domain(AnyDomain::Map(entries)) => {
                    tasks.push(DomainCloneTask::Map(entries.len()));
                    for (key, value) in entries.iter().rev() {
                        tasks.push(DomainCloneTask::Domain(value));
                        tasks.push(DomainCloneTask::Domain(key));
                    }
                },
                DomainCloneTask::Term(term) => {
                    tasks.push(DomainCloneTask::BuildTerm {
                        constructor: term.constructor.clone(),
                        has_payload: term.payload.is_some(),
                        child_count: term.children.len(),
                    });
                    for child in term.children.iter().rev() {
                        tasks.push(DomainCloneTask::Term(child));
                    }
                    if let Some(payload) = &term.payload {
                        tasks.push(DomainCloneTask::Domain(payload));
                    }
                },
                DomainCloneTask::Product(count) => {
                    let values = take_domain_values(&mut domains, count);
                    domains.push(AnyDomain::Product(values));
                },
                DomainCloneTask::Sum(tag) => {
                    let payload = domains.pop().expect("AnyDomain clone lost sum payload");
                    domains.push(AnyDomain::Sum(Box::new(SumValue { tag, payload })));
                },
                DomainCloneTask::List(count) => {
                    let values = take_domain_values(&mut domains, count);
                    domains.push(AnyDomain::List(values));
                },
                DomainCloneTask::Bag(count) => {
                    let values = take_domain_values(&mut domains, count);
                    domains.push(AnyDomain::Bag(values));
                },
                DomainCloneTask::Map(count) => {
                    let flat = take_domain_values(&mut domains, count * 2);
                    let mut entries = Vec::with_capacity(count);
                    let mut flat = flat.into_iter();
                    while let Some(key) = flat.next() {
                        let value = flat.next().expect("AnyDomain clone lost map value");
                        entries.push((key, value));
                    }
                    domains.push(AnyDomain::Map(entries));
                },
                DomainCloneTask::Tree => {
                    let term = terms.pop().expect("AnyDomain clone lost tree root");
                    domains.push(AnyDomain::Tree(Box::new(term)));
                },
                DomainCloneTask::BuildTerm { constructor, has_payload, child_count } => {
                    let child_start = terms
                        .len()
                        .checked_sub(child_count)
                        .expect("AnyDomain clone lost term children");
                    let children = terms.split_off(child_start);
                    let payload = has_payload
                        .then(|| domains.pop().expect("AnyDomain clone lost term payload"));
                    terms.push(SymTerm { constructor, payload, children });
                },
            }
        }
        debug_assert!(terms.is_empty());
        debug_assert_eq!(domains.len(), 1);
        domains.pop().expect("AnyDomain clone produced no value")
    }
}

fn push_domain_sequence<'domain>(
    tasks: &mut Vec<DomainCloneTask<'domain>>,
    build: DomainCloneTask<'domain>,
    values: &'domain [AnyDomain],
) {
    tasks.push(build);
    for value in values.iter().rev() {
        tasks.push(DomainCloneTask::Domain(value));
    }
}

fn take_domain_values(values: &mut Vec<AnyDomain>, count: usize) -> Vec<AnyDomain> {
    let start = values
        .len()
        .checked_sub(count)
        .expect("AnyDomain clone lost sequence values");
    values.split_off(start)
}

enum DomainPair<'domain> {
    Domain(&'domain AnyDomain, &'domain AnyDomain),
    Term(&'domain SymTerm<AnyDomain>, &'domain SymTerm<AnyDomain>),
}

impl PartialEq for AnyDomain {
    fn eq(&self, other: &Self) -> bool {
        let mut work = vec![DomainPair::Domain(self, other)];
        while let Some(pair) = work.pop() {
            match pair {
                DomainPair::Domain(left, right) => match (left, right) {
                    (AnyDomain::Int(a), AnyDomain::Int(b)) if a == b => {},
                    (AnyDomain::Char(a), AnyDomain::Char(b)) if a == b => {},
                    (AnyDomain::Bool(a), AnyDomain::Bool(b)) if a == b => {},
                    (AnyDomain::BigInt(a), AnyDomain::BigInt(b)) if a == b => {},
                    (AnyDomain::BigRat(a), AnyDomain::BigRat(b)) if a == b => {},
                    (AnyDomain::Fixed(a), AnyDomain::Fixed(b)) if a == b => {},
                    (AnyDomain::Float(a), AnyDomain::Float(b)) if a == b => {},
                    (AnyDomain::Str(a), AnyDomain::Str(b)) if a == b => {},
                    (AnyDomain::Product(a), AnyDomain::Product(b))
                    | (AnyDomain::List(a), AnyDomain::List(b))
                    | (AnyDomain::Bag(a), AnyDomain::Bag(b))
                        if a.len() == b.len() =>
                    {
                        for (a, b) in a.iter().zip(b).rev() {
                            work.push(DomainPair::Domain(a, b));
                        }
                    },
                    (AnyDomain::Sum(a), AnyDomain::Sum(b)) if a.tag == b.tag => {
                        work.push(DomainPair::Domain(&a.payload, &b.payload));
                    },
                    (AnyDomain::Tree(a), AnyDomain::Tree(b)) => {
                        work.push(DomainPair::Term(a, b));
                    },
                    (AnyDomain::Map(a), AnyDomain::Map(b)) if a.len() == b.len() => {
                        for ((ak, av), (bk, bv)) in a.iter().zip(b).rev() {
                            work.push(DomainPair::Domain(av, bv));
                            work.push(DomainPair::Domain(ak, bk));
                        }
                    },
                    _ => return false,
                },
                DomainPair::Term(left, right) => {
                    if left.constructor != right.constructor
                        || left.payload.is_some() != right.payload.is_some()
                        || left.children.len() != right.children.len()
                    {
                        return false;
                    }
                    for (left, right) in left.children.iter().zip(&right.children).rev() {
                        work.push(DomainPair::Term(left, right));
                    }
                    if let (Some(left), Some(right)) = (&left.payload, &right.payload) {
                        work.push(DomainPair::Domain(left, right));
                    }
                },
            }
        }
        true
    }
}

impl Eq for AnyDomain {}

enum DomainDebugTask<'domain> {
    Domain(&'domain AnyDomain),
    Term(&'domain SymTerm<AnyDomain>),
    Text(&'static str),
}

impl fmt::Debug for AnyDomain {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut tasks = vec![DomainDebugTask::Domain(self)];
        while let Some(task) = tasks.pop() {
            match task {
                DomainDebugTask::Text(text) => formatter.write_str(text)?,
                DomainDebugTask::Domain(AnyDomain::Int(value)) => {
                    write!(formatter, "Int({value:?})")?;
                },
                DomainDebugTask::Domain(AnyDomain::Char(value)) => {
                    write!(formatter, "Char({value:?})")?;
                },
                DomainDebugTask::Domain(AnyDomain::Bool(value)) => {
                    write!(formatter, "Bool({value:?})")?;
                },
                DomainDebugTask::Domain(AnyDomain::BigInt(value)) => {
                    write!(formatter, "BigInt({value:?})")?;
                },
                DomainDebugTask::Domain(AnyDomain::BigRat(value)) => {
                    write!(formatter, "BigRat({value:?})")?;
                },
                DomainDebugTask::Domain(AnyDomain::Fixed(value)) => {
                    write!(formatter, "Fixed({value:?})")?;
                },
                DomainDebugTask::Domain(AnyDomain::Float(value)) => {
                    write!(formatter, "Float({value:?})")?;
                },
                DomainDebugTask::Domain(AnyDomain::Str(value)) => {
                    write!(formatter, "Str({value:?})")?;
                },
                DomainDebugTask::Domain(AnyDomain::Product(values)) => {
                    push_domain_debug_list(&mut tasks, "Product([", values, "])");
                },
                DomainDebugTask::Domain(AnyDomain::Sum(value)) => {
                    tasks.push(DomainDebugTask::Text(" })"));
                    tasks.push(DomainDebugTask::Domain(&value.payload));
                    write!(formatter, "Sum(SumValue {{ tag: {:?}, payload: ", value.tag)?;
                },
                DomainDebugTask::Domain(AnyDomain::List(values)) => {
                    push_domain_debug_list(&mut tasks, "List([", values, "])");
                },
                DomainDebugTask::Domain(AnyDomain::Bag(values)) => {
                    push_domain_debug_list(&mut tasks, "Bag([", values, "])");
                },
                DomainDebugTask::Domain(AnyDomain::Tree(term)) => {
                    tasks.push(DomainDebugTask::Text(")"));
                    tasks.push(DomainDebugTask::Term(term));
                    formatter.write_str("Tree(")?;
                },
                DomainDebugTask::Domain(AnyDomain::Map(entries)) => {
                    tasks.push(DomainDebugTask::Text("])"));
                    for (index, (key, value)) in entries.iter().enumerate().rev() {
                        tasks.push(DomainDebugTask::Text(")"));
                        tasks.push(DomainDebugTask::Domain(value));
                        tasks.push(DomainDebugTask::Text(", "));
                        tasks.push(DomainDebugTask::Domain(key));
                        tasks.push(DomainDebugTask::Text("("));
                        if index > 0 {
                            tasks.push(DomainDebugTask::Text(", "));
                        }
                    }
                    formatter.write_str("Map([")?;
                },
                DomainDebugTask::Term(term) => {
                    tasks.push(DomainDebugTask::Text("] }"));
                    for (index, child) in term.children.iter().enumerate().rev() {
                        tasks.push(DomainDebugTask::Term(child));
                        if index > 0 {
                            tasks.push(DomainDebugTask::Text(", "));
                        }
                    }
                    match &term.payload {
                        Some(payload) => {
                            tasks.push(DomainDebugTask::Text("), children: ["));
                            tasks.push(DomainDebugTask::Domain(payload));
                            write!(
                                formatter,
                                "SymTerm {{ constructor: {:?}, payload: Some(",
                                term.constructor
                            )?;
                        },
                        None => {
                            write!(
                                formatter,
                                "SymTerm {{ constructor: {:?}, payload: None, children: [",
                                term.constructor
                            )?;
                        },
                    }
                },
            }
        }
        Ok(())
    }
}

fn push_domain_debug_list<'domain>(
    tasks: &mut Vec<DomainDebugTask<'domain>>,
    prefix: &'static str,
    values: &'domain [AnyDomain],
    suffix: &'static str,
) {
    tasks.push(DomainDebugTask::Text(suffix));
    for (index, value) in values.iter().enumerate().rev() {
        tasks.push(DomainDebugTask::Domain(value));
        if index > 0 {
            tasks.push(DomainDebugTask::Text(", "));
        }
    }
    tasks.push(DomainDebugTask::Text(prefix));
}

fn take_domain_children(domain: &mut AnyDomain, work: &mut Vec<AnyDomain>) {
    match domain {
        AnyDomain::Product(values) | AnyDomain::List(values) | AnyDomain::Bag(values) => {
            work.append(values);
        },
        AnyDomain::Sum(value) => {
            let payload = std::mem::replace(&mut value.payload, AnyDomain::Int(0));
            work.push(payload);
        },
        AnyDomain::Tree(root) => {
            let root = std::mem::replace(root, Box::new(SymTerm::constant(String::new())));
            let mut terms = vec![*root];
            while let Some(mut term) = terms.pop() {
                if let Some(payload) = term.payload.take() {
                    work.push(payload);
                }
                terms.append(&mut term.children);
            }
        },
        AnyDomain::Map(entries) => {
            for (key, value) in std::mem::take(entries) {
                work.push(key);
                work.push(value);
            }
        },
        AnyDomain::Int(_)
        | AnyDomain::Char(_)
        | AnyDomain::Bool(_)
        | AnyDomain::BigInt(_)
        | AnyDomain::BigRat(_)
        | AnyDomain::Fixed(_)
        | AnyDomain::Float(_)
        | AnyDomain::Str(_) => {},
    }
}

impl Drop for AnyDomain {
    fn drop(&mut self) {
        let mut work = Vec::new();
        take_domain_children(self, &mut work);
        while let Some(mut domain) = work.pop() {
            take_domain_children(&mut domain, &mut work);
        }
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// AnyPred + all structured predicate wrappers
// ══════════════════════════════════════════════════════════════════════════════

#[derive(Clone, Copy)]
enum BoolKind {
    And,
    Or,
}

#[derive(Clone, Copy)]
enum RegexBinaryKind {
    Concat,
    Alt,
    Inter,
}

#[derive(Clone, Copy)]
enum RegexUnaryKind {
    Star,
    Compl,
}

enum PredValue {
    Any(AnyPred),
    Product(NaryProductPred<AnyPred>),
    Sum(SumPred<AnyPred>),
    Regex(RegexPred<AnyPred>),
    Bag(BagPred<AnyPred>),
    Tree(TreePred<AnyPred>),
    Map(MapPred<AnyPred, AnyPred>),
}

impl PredValue {
    fn any(self, context: &str) -> AnyPred {
        match self {
            PredValue::Any(value) => value,
            _ => panic!("{context}: expected AnyPred value"),
        }
    }

    fn product(self, context: &str) -> NaryProductPred<AnyPred> {
        match self {
            PredValue::Product(value) => value,
            _ => panic!("{context}: expected product-predicate value"),
        }
    }

    fn sum(self, context: &str) -> SumPred<AnyPred> {
        match self {
            PredValue::Sum(value) => value,
            _ => panic!("{context}: expected sum-predicate value"),
        }
    }

    fn regex(self, context: &str) -> RegexPred<AnyPred> {
        match self {
            PredValue::Regex(value) => value,
            _ => panic!("{context}: expected regex-predicate value"),
        }
    }

    fn bag(self, context: &str) -> BagPred<AnyPred> {
        match self {
            PredValue::Bag(value) => value,
            _ => panic!("{context}: expected bag-predicate value"),
        }
    }

    fn tree(self, context: &str) -> TreePred<AnyPred> {
        match self {
            PredValue::Tree(value) => value,
            _ => panic!("{context}: expected tree-predicate value"),
        }
    }

    fn map(self, context: &str) -> MapPred<AnyPred, AnyPred> {
        match self {
            PredValue::Map(value) => value,
            _ => panic!("{context}: expected map-predicate value"),
        }
    }
}

enum PredCloneTask<'pred> {
    Any(&'pred AnyPred),
    Product(&'pred NaryProductPred<AnyPred>),
    Sum(&'pred SumPred<AnyPred>),
    Regex(&'pred RegexPred<AnyPred>),
    Bag(&'pred BagPred<AnyPred>),
    Tree(&'pred TreePred<AnyPred>),
    Map(&'pred MapPred<AnyPred, AnyPred>),
    AnyNot,
    AnyBinary(BoolKind),
    WrapProduct,
    WrapSum,
    WrapRegex,
    WrapBag,
    WrapTree,
    WrapMap,
    ProductField(usize),
    ProductNot,
    ProductBinary(BoolKind),
    SumInVariant(usize),
    SumNot,
    SumBinary(BoolKind),
    RegexElem,
    RegexUnary(RegexUnaryKind),
    RegexBinary(RegexBinaryKind),
    BagCount {
        lo: u64,
        hi: Option<u64>,
    },
    BagNot,
    BagBinary(BoolKind),
    TreeNode {
        constructor: String,
        has_payload: bool,
        child_count: usize,
    },
    TreeNot,
    TreeBinary(BoolKind),
    MapCount {
        lo: u64,
        hi: Option<u64>,
    },
    MapNot,
    MapBinary(BoolKind),
}

impl Clone for AnyPred {
    fn clone(&self) -> Self {
        let mut tasks = vec![PredCloneTask::Any(self)];
        let mut values = Vec::new();
        while let Some(task) = tasks.pop() {
            match task {
                PredCloneTask::Any(AnyPred::True) => values.push(PredValue::Any(AnyPred::True)),
                PredCloneTask::Any(AnyPred::False) => values.push(PredValue::Any(AnyPred::False)),
                PredCloneTask::Any(AnyPred::Int(value)) => {
                    values.push(PredValue::Any(AnyPred::Int(value.clone())));
                },
                PredCloneTask::Any(AnyPred::Char(value)) => {
                    values.push(PredValue::Any(AnyPred::Char(value.clone())));
                },
                PredCloneTask::Any(AnyPred::Bool(value)) => {
                    values.push(PredValue::Any(AnyPred::Bool(value.clone())));
                },
                PredCloneTask::Any(AnyPred::BigInt(value)) => {
                    values.push(PredValue::Any(AnyPred::BigInt(value.clone())));
                },
                PredCloneTask::Any(AnyPred::BigRat(value)) => {
                    values.push(PredValue::Any(AnyPred::BigRat(value.clone())));
                },
                PredCloneTask::Any(AnyPred::Fixed(value)) => {
                    values.push(PredValue::Any(AnyPred::Fixed(value.clone())));
                },
                PredCloneTask::Any(AnyPred::Float(value)) => {
                    values.push(PredValue::Any(AnyPred::Float(value.clone())));
                },
                PredCloneTask::Any(AnyPred::Str(value)) => {
                    values.push(PredValue::Any(AnyPred::Str(value.clone())));
                },
                PredCloneTask::Any(AnyPred::Product(value)) => {
                    tasks.push(PredCloneTask::WrapProduct);
                    tasks.push(PredCloneTask::Product(value));
                },
                PredCloneTask::Any(AnyPred::Sum(value)) => {
                    tasks.push(PredCloneTask::WrapSum);
                    tasks.push(PredCloneTask::Sum(value));
                },
                PredCloneTask::Any(AnyPred::List(value)) => {
                    tasks.push(PredCloneTask::WrapRegex);
                    tasks.push(PredCloneTask::Regex(value));
                },
                PredCloneTask::Any(AnyPred::Bag(value)) => {
                    tasks.push(PredCloneTask::WrapBag);
                    tasks.push(PredCloneTask::Bag(value));
                },
                PredCloneTask::Any(AnyPred::Tree(value)) => {
                    tasks.push(PredCloneTask::WrapTree);
                    tasks.push(PredCloneTask::Tree(value));
                },
                PredCloneTask::Any(AnyPred::Map(value)) => {
                    tasks.push(PredCloneTask::WrapMap);
                    tasks.push(PredCloneTask::Map(value));
                },
                PredCloneTask::Any(AnyPred::And(left, right)) => {
                    push_pred_clone_binary(
                        &mut tasks,
                        PredCloneTask::AnyBinary(BoolKind::And),
                        left,
                        right,
                    );
                },
                PredCloneTask::Any(AnyPred::Or(left, right)) => {
                    push_pred_clone_binary(
                        &mut tasks,
                        PredCloneTask::AnyBinary(BoolKind::Or),
                        left,
                        right,
                    );
                },
                PredCloneTask::Any(AnyPred::Not(body)) => {
                    tasks.push(PredCloneTask::AnyNot);
                    tasks.push(PredCloneTask::Any(body));
                },

                PredCloneTask::Product(NaryProductPred::True) => {
                    values.push(PredValue::Product(NaryProductPred::True));
                },
                PredCloneTask::Product(NaryProductPred::False) => {
                    values.push(PredValue::Product(NaryProductPred::False));
                },
                PredCloneTask::Product(NaryProductPred::Field(index, pred)) => {
                    tasks.push(PredCloneTask::ProductField(*index));
                    tasks.push(PredCloneTask::Any(pred));
                },
                PredCloneTask::Product(NaryProductPred::And(left, right)) => {
                    push_wrapper_clone_binary(
                        &mut tasks,
                        PredCloneTask::ProductBinary(BoolKind::And),
                        PredCloneTask::Product,
                        left,
                        right,
                    );
                },
                PredCloneTask::Product(NaryProductPred::Or(left, right)) => {
                    push_wrapper_clone_binary(
                        &mut tasks,
                        PredCloneTask::ProductBinary(BoolKind::Or),
                        PredCloneTask::Product,
                        left,
                        right,
                    );
                },
                PredCloneTask::Product(NaryProductPred::Not(body)) => {
                    tasks.push(PredCloneTask::ProductNot);
                    tasks.push(PredCloneTask::Product(body));
                },

                PredCloneTask::Sum(SumPred::True) => values.push(PredValue::Sum(SumPred::True)),
                PredCloneTask::Sum(SumPred::False) => values.push(PredValue::Sum(SumPred::False)),
                PredCloneTask::Sum(SumPred::InVariant(index, pred)) => {
                    tasks.push(PredCloneTask::SumInVariant(*index));
                    tasks.push(PredCloneTask::Any(pred));
                },
                PredCloneTask::Sum(SumPred::TagIs(index)) => {
                    values.push(PredValue::Sum(SumPred::TagIs(*index)));
                },
                PredCloneTask::Sum(SumPred::And(left, right)) => {
                    push_wrapper_clone_binary(
                        &mut tasks,
                        PredCloneTask::SumBinary(BoolKind::And),
                        PredCloneTask::Sum,
                        left,
                        right,
                    );
                },
                PredCloneTask::Sum(SumPred::Or(left, right)) => {
                    push_wrapper_clone_binary(
                        &mut tasks,
                        PredCloneTask::SumBinary(BoolKind::Or),
                        PredCloneTask::Sum,
                        left,
                        right,
                    );
                },
                PredCloneTask::Sum(SumPred::Not(body)) => {
                    tasks.push(PredCloneTask::SumNot);
                    tasks.push(PredCloneTask::Sum(body));
                },

                PredCloneTask::Regex(RegexPred::Empty) => {
                    values.push(PredValue::Regex(RegexPred::Empty));
                },
                PredCloneTask::Regex(RegexPred::Epsilon) => {
                    values.push(PredValue::Regex(RegexPred::Epsilon));
                },
                PredCloneTask::Regex(RegexPred::Elem(pred)) => {
                    tasks.push(PredCloneTask::RegexElem);
                    tasks.push(PredCloneTask::Any(pred));
                },
                PredCloneTask::Regex(RegexPred::Length(lo, hi)) => {
                    values.push(PredValue::Regex(RegexPred::Length(*lo, *hi)));
                },
                PredCloneTask::Regex(RegexPred::Concat(left, right)) => {
                    push_regex_clone_binary(&mut tasks, RegexBinaryKind::Concat, left, right)
                },
                PredCloneTask::Regex(RegexPred::Alt(left, right)) => {
                    push_regex_clone_binary(&mut tasks, RegexBinaryKind::Alt, left, right)
                },
                PredCloneTask::Regex(RegexPred::Inter(left, right)) => {
                    push_regex_clone_binary(&mut tasks, RegexBinaryKind::Inter, left, right)
                },
                PredCloneTask::Regex(RegexPred::Star(body)) => {
                    tasks.push(PredCloneTask::RegexUnary(RegexUnaryKind::Star));
                    tasks.push(PredCloneTask::Regex(body));
                },
                PredCloneTask::Regex(RegexPred::Compl(body)) => {
                    tasks.push(PredCloneTask::RegexUnary(RegexUnaryKind::Compl));
                    tasks.push(PredCloneTask::Regex(body));
                },

                PredCloneTask::Bag(BagPred::True) => values.push(PredValue::Bag(BagPred::True)),
                PredCloneTask::Bag(BagPred::False) => values.push(PredValue::Bag(BagPred::False)),
                PredCloneTask::Bag(BagPred::Count { class, lo, hi }) => {
                    tasks.push(PredCloneTask::BagCount { lo: *lo, hi: *hi });
                    tasks.push(PredCloneTask::Any(class));
                },
                PredCloneTask::Bag(BagPred::And(left, right)) => {
                    push_wrapper_clone_binary(
                        &mut tasks,
                        PredCloneTask::BagBinary(BoolKind::And),
                        PredCloneTask::Bag,
                        left,
                        right,
                    );
                },
                PredCloneTask::Bag(BagPred::Or(left, right)) => {
                    push_wrapper_clone_binary(
                        &mut tasks,
                        PredCloneTask::BagBinary(BoolKind::Or),
                        PredCloneTask::Bag,
                        left,
                        right,
                    );
                },
                PredCloneTask::Bag(BagPred::Not(body)) => {
                    tasks.push(PredCloneTask::BagNot);
                    tasks.push(PredCloneTask::Bag(body));
                },

                PredCloneTask::Tree(TreePred::True) => values.push(PredValue::Tree(TreePred::True)),
                PredCloneTask::Tree(TreePred::False) => {
                    values.push(PredValue::Tree(TreePred::False))
                },
                PredCloneTask::Tree(TreePred::Wild) => values.push(PredValue::Tree(TreePred::Wild)),
                PredCloneTask::Tree(TreePred::Node { constructor, payload_guard, children }) => {
                    tasks.push(PredCloneTask::TreeNode {
                        constructor: constructor.clone(),
                        has_payload: payload_guard.is_some(),
                        child_count: children.len(),
                    });
                    for child in children.iter().rev() {
                        tasks.push(PredCloneTask::Tree(child));
                    }
                    if let Some(payload) = payload_guard {
                        tasks.push(PredCloneTask::Any(payload));
                    }
                },
                PredCloneTask::Tree(TreePred::And(left, right)) => {
                    push_wrapper_clone_binary(
                        &mut tasks,
                        PredCloneTask::TreeBinary(BoolKind::And),
                        PredCloneTask::Tree,
                        left,
                        right,
                    );
                },
                PredCloneTask::Tree(TreePred::Or(left, right)) => {
                    push_wrapper_clone_binary(
                        &mut tasks,
                        PredCloneTask::TreeBinary(BoolKind::Or),
                        PredCloneTask::Tree,
                        left,
                        right,
                    );
                },
                PredCloneTask::Tree(TreePred::Not(body)) => {
                    tasks.push(PredCloneTask::TreeNot);
                    tasks.push(PredCloneTask::Tree(body));
                },

                PredCloneTask::Map(MapPred::True) => values.push(PredValue::Map(MapPred::True)),
                PredCloneTask::Map(MapPred::False) => values.push(PredValue::Map(MapPred::False)),
                PredCloneTask::Map(MapPred::CountEntries { key_class, val_class, lo, hi }) => {
                    tasks.push(PredCloneTask::MapCount { lo: *lo, hi: *hi });
                    tasks.push(PredCloneTask::Any(val_class));
                    tasks.push(PredCloneTask::Any(key_class));
                },
                PredCloneTask::Map(MapPred::And(left, right)) => {
                    push_wrapper_clone_binary(
                        &mut tasks,
                        PredCloneTask::MapBinary(BoolKind::And),
                        PredCloneTask::Map,
                        left,
                        right,
                    );
                },
                PredCloneTask::Map(MapPred::Or(left, right)) => {
                    push_wrapper_clone_binary(
                        &mut tasks,
                        PredCloneTask::MapBinary(BoolKind::Or),
                        PredCloneTask::Map,
                        left,
                        right,
                    );
                },
                PredCloneTask::Map(MapPred::Not(body)) => {
                    tasks.push(PredCloneTask::MapNot);
                    tasks.push(PredCloneTask::Map(body));
                },

                build => reduce_pred_clone(build, &mut values),
            }
        }
        debug_assert_eq!(values.len(), 1);
        values
            .pop()
            .expect("AnyPred clone produced no value")
            .any("AnyPred clone root")
    }
}

fn push_pred_clone_binary<'pred>(
    tasks: &mut Vec<PredCloneTask<'pred>>,
    build: PredCloneTask<'pred>,
    left: &'pred AnyPred,
    right: &'pred AnyPred,
) {
    tasks.push(build);
    tasks.push(PredCloneTask::Any(right));
    tasks.push(PredCloneTask::Any(left));
}

fn push_wrapper_clone_binary<'pred, P>(
    tasks: &mut Vec<PredCloneTask<'pred>>,
    build: PredCloneTask<'pred>,
    visit: fn(&'pred P) -> PredCloneTask<'pred>,
    left: &'pred P,
    right: &'pred P,
) {
    tasks.push(build);
    tasks.push(visit(right));
    tasks.push(visit(left));
}

fn push_regex_clone_binary<'pred>(
    tasks: &mut Vec<PredCloneTask<'pred>>,
    kind: RegexBinaryKind,
    left: &'pred RegexPred<AnyPred>,
    right: &'pred RegexPred<AnyPred>,
) {
    tasks.push(PredCloneTask::RegexBinary(kind));
    tasks.push(PredCloneTask::Regex(right));
    tasks.push(PredCloneTask::Regex(left));
}

fn reduce_pred_clone(task: PredCloneTask<'_>, values: &mut Vec<PredValue>) {
    let pop = |values: &mut Vec<PredValue>, context| {
        values
            .pop()
            .unwrap_or_else(|| panic!("{context}: clone PDA value stack underflow"))
    };
    match task {
        PredCloneTask::AnyNot => {
            let body = pop(values, "AnyPred Not").any("AnyPred Not");
            values.push(PredValue::Any(AnyPred::Not(Box::new(body))));
        },
        PredCloneTask::AnyBinary(kind) => {
            let right = pop(values, "AnyPred binary RHS").any("AnyPred binary RHS");
            let left = pop(values, "AnyPred binary LHS").any("AnyPred binary LHS");
            values.push(PredValue::Any(match kind {
                BoolKind::And => AnyPred::And(Box::new(left), Box::new(right)),
                BoolKind::Or => AnyPred::Or(Box::new(left), Box::new(right)),
            }));
        },
        PredCloneTask::WrapProduct => {
            let pred = pop(values, "AnyPred Product").product("AnyPred Product");
            values.push(PredValue::Any(AnyPred::Product(Box::new(pred))));
        },
        PredCloneTask::WrapSum => {
            let pred = pop(values, "AnyPred Sum").sum("AnyPred Sum");
            values.push(PredValue::Any(AnyPred::Sum(Box::new(pred))));
        },
        PredCloneTask::WrapRegex => {
            let pred = pop(values, "AnyPred List").regex("AnyPred List");
            values.push(PredValue::Any(AnyPred::List(Box::new(pred))));
        },
        PredCloneTask::WrapBag => {
            let pred = pop(values, "AnyPred Bag").bag("AnyPred Bag");
            values.push(PredValue::Any(AnyPred::Bag(Box::new(pred))));
        },
        PredCloneTask::WrapTree => {
            let pred = pop(values, "AnyPred Tree").tree("AnyPred Tree");
            values.push(PredValue::Any(AnyPred::Tree(Box::new(pred))));
        },
        PredCloneTask::WrapMap => {
            let pred = pop(values, "AnyPred Map").map("AnyPred Map");
            values.push(PredValue::Any(AnyPred::Map(Box::new(pred))));
        },
        PredCloneTask::ProductField(index) => {
            let pred = pop(values, "product Field").any("product Field");
            values.push(PredValue::Product(NaryProductPred::Field(index, pred)));
        },
        PredCloneTask::ProductNot => reduce_wrapper_unary(
            values,
            "product Not",
            |body| NaryProductPred::Not(Box::new(body)),
            PredValue::product,
            PredValue::Product,
        ),
        PredCloneTask::ProductBinary(kind) => reduce_wrapper_binary(
            values,
            kind,
            "product binary",
            |l, r| NaryProductPred::And(Box::new(l), Box::new(r)),
            |l, r| NaryProductPred::Or(Box::new(l), Box::new(r)),
            PredValue::product,
            PredValue::Product,
        ),
        PredCloneTask::SumInVariant(index) => {
            let pred = pop(values, "sum InVariant").any("sum InVariant");
            values.push(PredValue::Sum(SumPred::InVariant(index, pred)));
        },
        PredCloneTask::SumNot => reduce_wrapper_unary(
            values,
            "sum Not",
            |body| SumPred::Not(Box::new(body)),
            PredValue::sum,
            PredValue::Sum,
        ),
        PredCloneTask::SumBinary(kind) => reduce_wrapper_binary(
            values,
            kind,
            "sum binary",
            |l, r| SumPred::And(Box::new(l), Box::new(r)),
            |l, r| SumPred::Or(Box::new(l), Box::new(r)),
            PredValue::sum,
            PredValue::Sum,
        ),
        PredCloneTask::RegexElem => {
            let pred = pop(values, "regex Elem").any("regex Elem");
            values.push(PredValue::Regex(RegexPred::Elem(pred)));
        },
        PredCloneTask::RegexUnary(kind) => {
            let body = pop(values, "regex unary").regex("regex unary");
            values.push(PredValue::Regex(match kind {
                RegexUnaryKind::Star => RegexPred::Star(Box::new(body)),
                RegexUnaryKind::Compl => RegexPred::Compl(Box::new(body)),
            }));
        },
        PredCloneTask::RegexBinary(kind) => {
            let right = pop(values, "regex binary RHS").regex("regex binary RHS");
            let left = pop(values, "regex binary LHS").regex("regex binary LHS");
            values.push(PredValue::Regex(match kind {
                RegexBinaryKind::Concat => RegexPred::Concat(Box::new(left), Box::new(right)),
                RegexBinaryKind::Alt => RegexPred::Alt(Box::new(left), Box::new(right)),
                RegexBinaryKind::Inter => RegexPred::Inter(Box::new(left), Box::new(right)),
            }));
        },
        PredCloneTask::BagCount { lo, hi } => {
            let class = pop(values, "bag Count").any("bag Count");
            values.push(PredValue::Bag(BagPred::Count { class, lo, hi }));
        },
        PredCloneTask::BagNot => reduce_wrapper_unary(
            values,
            "bag Not",
            |body| BagPred::Not(Box::new(body)),
            PredValue::bag,
            PredValue::Bag,
        ),
        PredCloneTask::BagBinary(kind) => reduce_wrapper_binary(
            values,
            kind,
            "bag binary",
            |l, r| BagPred::And(Box::new(l), Box::new(r)),
            |l, r| BagPred::Or(Box::new(l), Box::new(r)),
            PredValue::bag,
            PredValue::Bag,
        ),
        PredCloneTask::TreeNode { constructor, has_payload, child_count } => {
            let start = values
                .len()
                .checked_sub(child_count)
                .expect("tree Node lost children");
            let children = values
                .drain(start..)
                .map(|value| value.tree("tree Node child"))
                .collect();
            let payload_guard =
                has_payload.then(|| pop(values, "tree Node payload").any("tree Node payload"));
            values.push(PredValue::Tree(TreePred::Node { constructor, payload_guard, children }));
        },
        PredCloneTask::TreeNot => reduce_wrapper_unary(
            values,
            "tree Not",
            |body| TreePred::Not(Box::new(body)),
            PredValue::tree,
            PredValue::Tree,
        ),
        PredCloneTask::TreeBinary(kind) => reduce_wrapper_binary(
            values,
            kind,
            "tree binary",
            |l, r| TreePred::And(Box::new(l), Box::new(r)),
            |l, r| TreePred::Or(Box::new(l), Box::new(r)),
            PredValue::tree,
            PredValue::Tree,
        ),
        PredCloneTask::MapCount { lo, hi } => {
            let val_class = pop(values, "map CountEntries value").any("map CountEntries value");
            let key_class = pop(values, "map CountEntries key").any("map CountEntries key");
            values.push(PredValue::Map(MapPred::CountEntries { key_class, val_class, lo, hi }));
        },
        PredCloneTask::MapNot => reduce_wrapper_unary(
            values,
            "map Not",
            |body| MapPred::Not(Box::new(body)),
            PredValue::map,
            PredValue::Map,
        ),
        PredCloneTask::MapBinary(kind) => reduce_wrapper_binary(
            values,
            kind,
            "map binary",
            |l, r| MapPred::And(Box::new(l), Box::new(r)),
            |l, r| MapPred::Or(Box::new(l), Box::new(r)),
            PredValue::map,
            PredValue::Map,
        ),
        PredCloneTask::Any(_)
        | PredCloneTask::Product(_)
        | PredCloneTask::Sum(_)
        | PredCloneTask::Regex(_)
        | PredCloneTask::Bag(_)
        | PredCloneTask::Tree(_)
        | PredCloneTask::Map(_) => unreachable!("visits are reduced in the main clone loop"),
    }
}

fn reduce_wrapper_unary<T>(
    values: &mut Vec<PredValue>,
    context: &str,
    build: impl FnOnce(T) -> T,
    extract: fn(PredValue, &str) -> T,
    wrap: fn(T) -> PredValue,
) {
    let body = extract(
        values
            .pop()
            .unwrap_or_else(|| panic!("{context}: missing body")),
        context,
    );
    values.push(wrap(build(body)));
}

fn reduce_wrapper_binary<T>(
    values: &mut Vec<PredValue>,
    kind: BoolKind,
    context: &str,
    and: impl FnOnce(T, T) -> T,
    or: impl FnOnce(T, T) -> T,
    extract: fn(PredValue, &str) -> T,
    wrap: fn(T) -> PredValue,
) {
    let right = extract(
        values
            .pop()
            .unwrap_or_else(|| panic!("{context}: missing RHS")),
        context,
    );
    let left = extract(
        values
            .pop()
            .unwrap_or_else(|| panic!("{context}: missing LHS")),
        context,
    );
    values.push(wrap(match kind {
        BoolKind::And => and(left, right),
        BoolKind::Or => or(left, right),
    }));
}

enum PredPair<'pred> {
    Any(&'pred AnyPred, &'pred AnyPred),
    Product(&'pred NaryProductPred<AnyPred>, &'pred NaryProductPred<AnyPred>),
    Sum(&'pred SumPred<AnyPred>, &'pred SumPred<AnyPred>),
    Regex(&'pred RegexPred<AnyPred>, &'pred RegexPred<AnyPred>),
    Bag(&'pred BagPred<AnyPred>, &'pred BagPred<AnyPred>),
    Tree(&'pred TreePred<AnyPred>, &'pred TreePred<AnyPred>),
    Map(&'pred MapPred<AnyPred, AnyPred>, &'pred MapPred<AnyPred, AnyPred>),
}

impl PartialEq for AnyPred {
    fn eq(&self, other: &Self) -> bool {
        let mut work = vec![PredPair::Any(self, other)];
        while let Some(pair) = work.pop() {
            let equal = match pair {
                PredPair::Any(left, right) => match (left, right) {
                    (AnyPred::True, AnyPred::True) | (AnyPred::False, AnyPred::False) => true,
                    (AnyPred::Int(a), AnyPred::Int(b)) => a == b,
                    (AnyPred::Char(a), AnyPred::Char(b)) => a == b,
                    (AnyPred::Bool(a), AnyPred::Bool(b)) => a == b,
                    (AnyPred::BigInt(a), AnyPred::BigInt(b)) => a == b,
                    (AnyPred::BigRat(a), AnyPred::BigRat(b)) => a == b,
                    (AnyPred::Fixed(a), AnyPred::Fixed(b)) => a == b,
                    (AnyPred::Float(a), AnyPred::Float(b)) => a == b,
                    (AnyPred::Str(a), AnyPred::Str(b)) => a == b,
                    (AnyPred::Product(a), AnyPred::Product(b)) => {
                        work.push(PredPair::Product(a, b));
                        true
                    },
                    (AnyPred::Sum(a), AnyPred::Sum(b)) => {
                        work.push(PredPair::Sum(a, b));
                        true
                    },
                    (AnyPred::List(a), AnyPred::List(b)) => {
                        work.push(PredPair::Regex(a, b));
                        true
                    },
                    (AnyPred::Bag(a), AnyPred::Bag(b)) => {
                        work.push(PredPair::Bag(a, b));
                        true
                    },
                    (AnyPred::Tree(a), AnyPred::Tree(b)) => {
                        work.push(PredPair::Tree(a, b));
                        true
                    },
                    (AnyPred::Map(a), AnyPred::Map(b)) => {
                        work.push(PredPair::Map(a, b));
                        true
                    },
                    (AnyPred::And(al, ar), AnyPred::And(bl, br))
                    | (AnyPred::Or(al, ar), AnyPred::Or(bl, br)) => {
                        work.push(PredPair::Any(ar, br));
                        work.push(PredPair::Any(al, bl));
                        true
                    },
                    (AnyPred::Not(a), AnyPred::Not(b)) => {
                        work.push(PredPair::Any(a, b));
                        true
                    },
                    _ => false,
                },
                PredPair::Product(left, right) => match (left, right) {
                    (NaryProductPred::True, NaryProductPred::True)
                    | (NaryProductPred::False, NaryProductPred::False) => true,
                    (NaryProductPred::Field(ai, ap), NaryProductPred::Field(bi, bp))
                        if ai == bi =>
                    {
                        work.push(PredPair::Any(ap, bp));
                        true
                    },
                    (NaryProductPred::And(al, ar), NaryProductPred::And(bl, br))
                    | (NaryProductPred::Or(al, ar), NaryProductPred::Or(bl, br)) => {
                        work.push(PredPair::Product(ar, br));
                        work.push(PredPair::Product(al, bl));
                        true
                    },
                    (NaryProductPred::Not(a), NaryProductPred::Not(b)) => {
                        work.push(PredPair::Product(a, b));
                        true
                    },
                    _ => false,
                },
                PredPair::Sum(left, right) => match (left, right) {
                    (SumPred::True, SumPred::True) | (SumPred::False, SumPred::False) => true,
                    (SumPred::InVariant(ai, ap), SumPred::InVariant(bi, bp)) if ai == bi => {
                        work.push(PredPair::Any(ap, bp));
                        true
                    },
                    (SumPred::TagIs(a), SumPred::TagIs(b)) => a == b,
                    (SumPred::And(al, ar), SumPred::And(bl, br))
                    | (SumPred::Or(al, ar), SumPred::Or(bl, br)) => {
                        work.push(PredPair::Sum(ar, br));
                        work.push(PredPair::Sum(al, bl));
                        true
                    },
                    (SumPred::Not(a), SumPred::Not(b)) => {
                        work.push(PredPair::Sum(a, b));
                        true
                    },
                    _ => false,
                },
                PredPair::Regex(left, right) => match (left, right) {
                    (RegexPred::Empty, RegexPred::Empty)
                    | (RegexPred::Epsilon, RegexPred::Epsilon) => true,
                    (RegexPred::Elem(a), RegexPred::Elem(b)) => {
                        work.push(PredPair::Any(a, b));
                        true
                    },
                    (RegexPred::Length(al, ah), RegexPred::Length(bl, bh)) => al == bl && ah == bh,
                    (RegexPred::Concat(al, ar), RegexPred::Concat(bl, br))
                    | (RegexPred::Alt(al, ar), RegexPred::Alt(bl, br))
                    | (RegexPred::Inter(al, ar), RegexPred::Inter(bl, br)) => {
                        work.push(PredPair::Regex(ar, br));
                        work.push(PredPair::Regex(al, bl));
                        true
                    },
                    (RegexPred::Star(a), RegexPred::Star(b))
                    | (RegexPred::Compl(a), RegexPred::Compl(b)) => {
                        work.push(PredPair::Regex(a, b));
                        true
                    },
                    _ => false,
                },
                PredPair::Bag(left, right) => match (left, right) {
                    (BagPred::True, BagPred::True) | (BagPred::False, BagPred::False) => true,
                    (
                        BagPred::Count { class: ac, lo: al, hi: ah },
                        BagPred::Count { class: bc, lo: bl, hi: bh },
                    ) if al == bl && ah == bh => {
                        work.push(PredPair::Any(ac, bc));
                        true
                    },
                    (BagPred::And(al, ar), BagPred::And(bl, br))
                    | (BagPred::Or(al, ar), BagPred::Or(bl, br)) => {
                        work.push(PredPair::Bag(ar, br));
                        work.push(PredPair::Bag(al, bl));
                        true
                    },
                    (BagPred::Not(a), BagPred::Not(b)) => {
                        work.push(PredPair::Bag(a, b));
                        true
                    },
                    _ => false,
                },
                PredPair::Tree(left, right) => match (left, right) {
                    (TreePred::True, TreePred::True)
                    | (TreePred::False, TreePred::False)
                    | (TreePred::Wild, TreePred::Wild) => true,
                    (
                        TreePred::Node {
                            constructor: ac,
                            payload_guard: ap,
                            children: ach,
                        },
                        TreePred::Node {
                            constructor: bc,
                            payload_guard: bp,
                            children: bch,
                        },
                    ) if ac == bc && ap.is_some() == bp.is_some() && ach.len() == bch.len() => {
                        for (a, b) in ach.iter().zip(bch).rev() {
                            work.push(PredPair::Tree(a, b));
                        }
                        if let (Some(a), Some(b)) = (ap, bp) {
                            work.push(PredPair::Any(a, b));
                        }
                        true
                    },
                    (TreePred::And(al, ar), TreePred::And(bl, br))
                    | (TreePred::Or(al, ar), TreePred::Or(bl, br)) => {
                        work.push(PredPair::Tree(ar, br));
                        work.push(PredPair::Tree(al, bl));
                        true
                    },
                    (TreePred::Not(a), TreePred::Not(b)) => {
                        work.push(PredPair::Tree(a, b));
                        true
                    },
                    _ => false,
                },
                PredPair::Map(left, right) => match (left, right) {
                    (MapPred::True, MapPred::True) | (MapPred::False, MapPred::False) => true,
                    (
                        MapPred::CountEntries {
                            key_class: ak,
                            val_class: av,
                            lo: al,
                            hi: ah,
                        },
                        MapPred::CountEntries {
                            key_class: bk,
                            val_class: bv,
                            lo: bl,
                            hi: bh,
                        },
                    ) if al == bl && ah == bh => {
                        work.push(PredPair::Any(av, bv));
                        work.push(PredPair::Any(ak, bk));
                        true
                    },
                    (MapPred::And(al, ar), MapPred::And(bl, br))
                    | (MapPred::Or(al, ar), MapPred::Or(bl, br)) => {
                        work.push(PredPair::Map(ar, br));
                        work.push(PredPair::Map(al, bl));
                        true
                    },
                    (MapPred::Not(a), MapPred::Not(b)) => {
                        work.push(PredPair::Map(a, b));
                        true
                    },
                    _ => false,
                },
            };
            if !equal {
                return false;
            }
        }
        true
    }
}

impl Eq for AnyPred {}

enum PredRef<'pred> {
    Any(&'pred AnyPred),
    Product(&'pred NaryProductPred<AnyPred>),
    Sum(&'pred SumPred<AnyPred>),
    Regex(&'pred RegexPred<AnyPred>),
    Bag(&'pred BagPred<AnyPred>),
    Tree(&'pred TreePred<AnyPred>),
    Map(&'pred MapPred<AnyPred, AnyPred>),
    BagFields(u64, Option<u64>),
    TreeChildren(&'pred [TreePred<AnyPred>]),
    MapFields(u64, Option<u64>),
}

impl Hash for AnyPred {
    fn hash<H: Hasher>(&self, state: &mut H) {
        let mut work = vec![PredRef::Any(self)];
        while let Some(node) = work.pop() {
            match node {
                PredRef::Any(pred) => {
                    std::mem::discriminant(pred).hash(state);
                    match pred {
                        AnyPred::True | AnyPred::False => {},
                        AnyPred::Int(value) => value.hash(state),
                        AnyPred::Char(value) => value.hash(state),
                        AnyPred::Bool(value) => value.hash(state),
                        AnyPred::BigInt(value) => value.hash(state),
                        AnyPred::BigRat(value) => value.hash(state),
                        AnyPred::Fixed(value) => value.hash(state),
                        AnyPred::Float(value) => value.hash(state),
                        AnyPred::Str(value) => value.hash(state),
                        AnyPred::Product(value) => work.push(PredRef::Product(value)),
                        AnyPred::Sum(value) => work.push(PredRef::Sum(value)),
                        AnyPred::List(value) => work.push(PredRef::Regex(value)),
                        AnyPred::Bag(value) => work.push(PredRef::Bag(value)),
                        AnyPred::Tree(value) => work.push(PredRef::Tree(value)),
                        AnyPred::Map(value) => work.push(PredRef::Map(value)),
                        AnyPred::And(left, right) | AnyPred::Or(left, right) => {
                            work.push(PredRef::Any(right));
                            work.push(PredRef::Any(left));
                        },
                        AnyPred::Not(body) => work.push(PredRef::Any(body)),
                    }
                },
                PredRef::Product(pred) => {
                    std::mem::discriminant(pred).hash(state);
                    match pred {
                        NaryProductPred::True | NaryProductPred::False => {},
                        NaryProductPred::Field(index, pred) => {
                            index.hash(state);
                            work.push(PredRef::Any(pred));
                        },
                        NaryProductPred::And(left, right) | NaryProductPred::Or(left, right) => {
                            work.push(PredRef::Product(right));
                            work.push(PredRef::Product(left));
                        },
                        NaryProductPred::Not(body) => work.push(PredRef::Product(body)),
                    }
                },
                PredRef::Sum(pred) => {
                    std::mem::discriminant(pred).hash(state);
                    match pred {
                        SumPred::True | SumPred::False => {},
                        SumPred::InVariant(index, pred) => {
                            index.hash(state);
                            work.push(PredRef::Any(pred));
                        },
                        SumPred::TagIs(index) => index.hash(state),
                        SumPred::And(left, right) | SumPred::Or(left, right) => {
                            work.push(PredRef::Sum(right));
                            work.push(PredRef::Sum(left));
                        },
                        SumPred::Not(body) => work.push(PredRef::Sum(body)),
                    }
                },
                PredRef::Regex(pred) => {
                    std::mem::discriminant(pred).hash(state);
                    match pred {
                        RegexPred::Empty | RegexPred::Epsilon => {},
                        RegexPred::Elem(pred) => work.push(PredRef::Any(pred)),
                        RegexPred::Length(lo, hi) => {
                            lo.hash(state);
                            hi.hash(state);
                        },
                        RegexPred::Concat(left, right)
                        | RegexPred::Alt(left, right)
                        | RegexPred::Inter(left, right) => {
                            work.push(PredRef::Regex(right));
                            work.push(PredRef::Regex(left));
                        },
                        RegexPred::Star(body) | RegexPred::Compl(body) => {
                            work.push(PredRef::Regex(body));
                        },
                    }
                },
                PredRef::Bag(pred) => {
                    std::mem::discriminant(pred).hash(state);
                    match pred {
                        BagPred::True | BagPred::False => {},
                        BagPred::Count { class, lo, hi } => {
                            work.push(PredRef::BagFields(*lo, *hi));
                            work.push(PredRef::Any(class));
                        },
                        BagPred::And(left, right) | BagPred::Or(left, right) => {
                            work.push(PredRef::Bag(right));
                            work.push(PredRef::Bag(left));
                        },
                        BagPred::Not(body) => work.push(PredRef::Bag(body)),
                    }
                },
                PredRef::Tree(pred) => {
                    std::mem::discriminant(pred).hash(state);
                    match pred {
                        TreePred::True | TreePred::False | TreePred::Wild => {},
                        TreePred::Node { constructor, payload_guard, children } => {
                            constructor.hash(state);
                            std::mem::discriminant(payload_guard).hash(state);
                            work.push(PredRef::TreeChildren(children));
                            if let Some(payload) = payload_guard {
                                work.push(PredRef::Any(payload));
                            }
                        },
                        TreePred::And(left, right) | TreePred::Or(left, right) => {
                            work.push(PredRef::Tree(right));
                            work.push(PredRef::Tree(left));
                        },
                        TreePred::Not(body) => work.push(PredRef::Tree(body)),
                    }
                },
                PredRef::Map(pred) => {
                    std::mem::discriminant(pred).hash(state);
                    match pred {
                        MapPred::True | MapPred::False => {},
                        MapPred::CountEntries { key_class, val_class, lo, hi } => {
                            work.push(PredRef::MapFields(*lo, *hi));
                            work.push(PredRef::Any(val_class));
                            work.push(PredRef::Any(key_class));
                        },
                        MapPred::And(left, right) | MapPred::Or(left, right) => {
                            work.push(PredRef::Map(right));
                            work.push(PredRef::Map(left));
                        },
                        MapPred::Not(body) => work.push(PredRef::Map(body)),
                    }
                },
                PredRef::BagFields(lo, hi) | PredRef::MapFields(lo, hi) => {
                    lo.hash(state);
                    hi.hash(state);
                },
                PredRef::TreeChildren(children) => {
                    children.len().hash(state);
                    for child in children.iter().rev() {
                        work.push(PredRef::Tree(child));
                    }
                },
            }
        }
    }
}

enum PredDebugTask<'pred> {
    Any(&'pred AnyPred),
    Product(&'pred NaryProductPred<AnyPred>),
    Sum(&'pred SumPred<AnyPred>),
    Regex(&'pred RegexPred<AnyPred>),
    Bag(&'pred BagPred<AnyPred>),
    Tree(&'pred TreePred<AnyPred>),
    Map(&'pred MapPred<AnyPred, AnyPred>),
    BagFields(u64, Option<u64>),
    MapFields(u64, Option<u64>),
    Text(&'static str),
}

impl fmt::Debug for AnyPred {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut tasks = vec![PredDebugTask::Any(self)];
        while let Some(task) = tasks.pop() {
            match task {
                PredDebugTask::Text(text) => formatter.write_str(text)?,
                PredDebugTask::Any(pred) => match pred {
                    AnyPred::True => formatter.write_str("True")?,
                    AnyPred::False => formatter.write_str("False")?,
                    AnyPred::Int(value) => write!(formatter, "Int({value:?})")?,
                    AnyPred::Char(value) => write!(formatter, "Char({value:?})")?,
                    AnyPred::Bool(value) => write!(formatter, "Bool({value:?})")?,
                    AnyPred::BigInt(value) => write!(formatter, "BigInt({value:?})")?,
                    AnyPred::BigRat(value) => write!(formatter, "BigRat({value:?})")?,
                    AnyPred::Fixed(value) => write!(formatter, "Fixed({value:?})")?,
                    AnyPred::Float(value) => write!(formatter, "Float({value:?})")?,
                    AnyPred::Str(value) => write!(formatter, "Str({value:?})")?,
                    AnyPred::Product(value) => {
                        push_debug_wrapper(&mut tasks, PredDebugTask::Product(value), "Product(");
                    },
                    AnyPred::Sum(value) => {
                        push_debug_wrapper(&mut tasks, PredDebugTask::Sum(value), "Sum(");
                    },
                    AnyPred::List(value) => {
                        push_debug_wrapper(&mut tasks, PredDebugTask::Regex(value), "List(");
                    },
                    AnyPred::Bag(value) => {
                        push_debug_wrapper(&mut tasks, PredDebugTask::Bag(value), "Bag(");
                    },
                    AnyPred::Tree(value) => {
                        push_debug_wrapper(&mut tasks, PredDebugTask::Tree(value), "Tree(");
                    },
                    AnyPred::Map(value) => {
                        push_debug_wrapper(&mut tasks, PredDebugTask::Map(value), "Map(");
                    },
                    AnyPred::And(left, right) => {
                        push_any_debug_binary(&mut tasks, "And(", left, right);
                    },
                    AnyPred::Or(left, right) => {
                        push_any_debug_binary(&mut tasks, "Or(", left, right);
                    },
                    AnyPred::Not(body) => {
                        tasks.push(PredDebugTask::Text(")"));
                        tasks.push(PredDebugTask::Any(body));
                        tasks.push(PredDebugTask::Text("Not("));
                    },
                },
                PredDebugTask::Product(pred) => match pred {
                    NaryProductPred::True => formatter.write_str("True")?,
                    NaryProductPred::False => formatter.write_str("False")?,
                    NaryProductPred::Field(index, pred) => {
                        tasks.push(PredDebugTask::Text(")"));
                        tasks.push(PredDebugTask::Any(pred));
                        write!(formatter, "Field({index:?}, ")?;
                    },
                    NaryProductPred::And(left, right) => {
                        push_product_debug_binary(&mut tasks, "And(", left, right);
                    },
                    NaryProductPred::Or(left, right) => {
                        push_product_debug_binary(&mut tasks, "Or(", left, right);
                    },
                    NaryProductPred::Not(body) => {
                        push_product_debug_unary(&mut tasks, "Not(", body);
                    },
                },
                PredDebugTask::Sum(pred) => match pred {
                    SumPred::True => formatter.write_str("True")?,
                    SumPred::False => formatter.write_str("False")?,
                    SumPred::InVariant(index, pred) => {
                        tasks.push(PredDebugTask::Text(")"));
                        tasks.push(PredDebugTask::Any(pred));
                        write!(formatter, "InVariant({index:?}, ")?;
                    },
                    SumPred::TagIs(index) => write!(formatter, "TagIs({index:?})")?,
                    SumPred::And(left, right) => {
                        push_sum_debug_binary(&mut tasks, "And(", left, right);
                    },
                    SumPred::Or(left, right) => {
                        push_sum_debug_binary(&mut tasks, "Or(", left, right);
                    },
                    SumPred::Not(body) => push_sum_debug_unary(&mut tasks, "Not(", body),
                },
                PredDebugTask::Regex(pred) => match pred {
                    RegexPred::Empty => formatter.write_str("Empty")?,
                    RegexPred::Epsilon => formatter.write_str("Epsilon")?,
                    RegexPred::Elem(pred) => {
                        tasks.push(PredDebugTask::Text(")"));
                        tasks.push(PredDebugTask::Any(pred));
                        formatter.write_str("Elem(")?;
                    },
                    RegexPred::Length(lo, hi) => {
                        write!(formatter, "Length({lo:?}, {hi:?})")?;
                    },
                    RegexPred::Concat(left, right) => {
                        push_regex_debug_binary(&mut tasks, "Concat(", left, right);
                    },
                    RegexPred::Alt(left, right) => {
                        push_regex_debug_binary(&mut tasks, "Alt(", left, right);
                    },
                    RegexPred::Inter(left, right) => {
                        push_regex_debug_binary(&mut tasks, "Inter(", left, right);
                    },
                    RegexPred::Star(body) => push_regex_debug_unary(&mut tasks, "Star(", body),
                    RegexPred::Compl(body) => push_regex_debug_unary(&mut tasks, "Compl(", body),
                },
                PredDebugTask::Bag(pred) => match pred {
                    BagPred::True => formatter.write_str("True")?,
                    BagPred::False => formatter.write_str("False")?,
                    BagPred::Count { class, lo, hi } => {
                        tasks.push(PredDebugTask::Text(" }"));
                        tasks.push(PredDebugTask::BagFields(*lo, *hi));
                        tasks.push(PredDebugTask::Any(class));
                        formatter.write_str("Count { class: ")?;
                    },
                    BagPred::And(left, right) => {
                        push_bag_debug_binary(&mut tasks, "And(", left, right);
                    },
                    BagPred::Or(left, right) => {
                        push_bag_debug_binary(&mut tasks, "Or(", left, right);
                    },
                    BagPred::Not(body) => push_bag_debug_unary(&mut tasks, "Not(", body),
                },
                PredDebugTask::Tree(pred) => match pred {
                    TreePred::True => formatter.write_str("True")?,
                    TreePred::False => formatter.write_str("False")?,
                    TreePred::Wild => formatter.write_str("Wild")?,
                    TreePred::Node { constructor, payload_guard, children } => {
                        tasks.push(PredDebugTask::Text("] }"));
                        for (index, child) in children.iter().enumerate().rev() {
                            tasks.push(PredDebugTask::Tree(child));
                            if index > 0 {
                                tasks.push(PredDebugTask::Text(", "));
                            }
                        }
                        match payload_guard {
                            Some(payload) => {
                                tasks.push(PredDebugTask::Text("), children: ["));
                                tasks.push(PredDebugTask::Any(payload));
                                write!(
                                    formatter,
                                    "Node {{ constructor: {constructor:?}, payload_guard: Some("
                                )?;
                            },
                            None => write!(
                                formatter,
                                "Node {{ constructor: {constructor:?}, payload_guard: None, children: ["
                            )?,
                        }
                    },
                    TreePred::And(left, right) => {
                        push_tree_debug_binary(&mut tasks, "And(", left, right);
                    },
                    TreePred::Or(left, right) => {
                        push_tree_debug_binary(&mut tasks, "Or(", left, right);
                    },
                    TreePred::Not(body) => push_tree_debug_unary(&mut tasks, "Not(", body),
                },
                PredDebugTask::Map(pred) => match pred {
                    MapPred::True => formatter.write_str("True")?,
                    MapPred::False => formatter.write_str("False")?,
                    MapPred::CountEntries { key_class, val_class, lo, hi } => {
                        tasks.push(PredDebugTask::Text(" }"));
                        tasks.push(PredDebugTask::MapFields(*lo, *hi));
                        tasks.push(PredDebugTask::Any(val_class));
                        tasks.push(PredDebugTask::Text(", val_class: "));
                        tasks.push(PredDebugTask::Any(key_class));
                        formatter.write_str("CountEntries { key_class: ")?;
                    },
                    MapPred::And(left, right) => {
                        push_map_debug_binary(&mut tasks, "And(", left, right);
                    },
                    MapPred::Or(left, right) => {
                        push_map_debug_binary(&mut tasks, "Or(", left, right);
                    },
                    MapPred::Not(body) => push_map_debug_unary(&mut tasks, "Not(", body),
                },
                PredDebugTask::BagFields(lo, hi) => write!(formatter, ", lo: {lo:?}, hi: {hi:?}")?,
                PredDebugTask::MapFields(lo, hi) => write!(formatter, ", lo: {lo:?}, hi: {hi:?}")?,
            }
        }
        Ok(())
    }
}

fn push_debug_wrapper<'pred>(
    tasks: &mut Vec<PredDebugTask<'pred>>,
    node: PredDebugTask<'pred>,
    prefix: &'static str,
) {
    tasks.push(PredDebugTask::Text(")"));
    tasks.push(node);
    tasks.push(PredDebugTask::Text(prefix));
}

fn push_any_debug_binary<'pred>(
    tasks: &mut Vec<PredDebugTask<'pred>>,
    prefix: &'static str,
    left: &'pred AnyPred,
    right: &'pred AnyPred,
) {
    tasks.push(PredDebugTask::Text(")"));
    tasks.push(PredDebugTask::Any(right));
    tasks.push(PredDebugTask::Text(", "));
    tasks.push(PredDebugTask::Any(left));
    tasks.push(PredDebugTask::Text(prefix));
}

macro_rules! debug_helpers {
    ($unary:ident, $binary:ident, $variant:ident, $ty:ty) => {
        fn $unary<'pred>(
            tasks: &mut Vec<PredDebugTask<'pred>>,
            prefix: &'static str,
            body: &'pred $ty,
        ) {
            tasks.push(PredDebugTask::Text(")"));
            tasks.push(PredDebugTask::$variant(body));
            tasks.push(PredDebugTask::Text(prefix));
        }

        fn $binary<'pred>(
            tasks: &mut Vec<PredDebugTask<'pred>>,
            prefix: &'static str,
            left: &'pred $ty,
            right: &'pred $ty,
        ) {
            tasks.push(PredDebugTask::Text(")"));
            tasks.push(PredDebugTask::$variant(right));
            tasks.push(PredDebugTask::Text(", "));
            tasks.push(PredDebugTask::$variant(left));
            tasks.push(PredDebugTask::Text(prefix));
        }
    };
}

debug_helpers!(
    push_product_debug_unary,
    push_product_debug_binary,
    Product,
    NaryProductPred<AnyPred>
);
debug_helpers!(push_sum_debug_unary, push_sum_debug_binary, Sum, SumPred<AnyPred>);
debug_helpers!(push_regex_debug_unary, push_regex_debug_binary, Regex, RegexPred<AnyPred>);
debug_helpers!(push_bag_debug_unary, push_bag_debug_binary, Bag, BagPred<AnyPred>);
debug_helpers!(push_tree_debug_unary, push_tree_debug_binary, Tree, TreePred<AnyPred>);
debug_helpers!(
    push_map_debug_unary,
    push_map_debug_binary,
    Map,
    MapPred<AnyPred, AnyPred>
);

fn take_any_box(child: &mut Box<AnyPred>) -> AnyPred {
    *std::mem::replace(child, Box::new(AnyPred::True))
}

fn take_any_pred_children(pred: &mut AnyPred, work: &mut Vec<PredValue>) {
    match pred {
        AnyPred::Product(wrapper) => {
            let wrapper = std::mem::replace(wrapper, Box::new(NaryProductPred::True));
            work.push(PredValue::Product(*wrapper));
        },
        AnyPred::Sum(wrapper) => {
            let wrapper = std::mem::replace(wrapper, Box::new(SumPred::True));
            work.push(PredValue::Sum(*wrapper));
        },
        AnyPred::List(wrapper) => {
            let wrapper = std::mem::replace(wrapper, Box::new(RegexPred::Empty));
            work.push(PredValue::Regex(*wrapper));
        },
        AnyPred::Bag(wrapper) => {
            let wrapper = std::mem::replace(wrapper, Box::new(BagPred::True));
            work.push(PredValue::Bag(*wrapper));
        },
        AnyPred::Tree(wrapper) => {
            let wrapper = std::mem::replace(wrapper, Box::new(TreePred::True));
            work.push(PredValue::Tree(*wrapper));
        },
        AnyPred::Map(wrapper) => {
            let wrapper = std::mem::replace(wrapper, Box::new(MapPred::True));
            work.push(PredValue::Map(*wrapper));
        },
        AnyPred::And(left, right) | AnyPred::Or(left, right) => {
            work.push(PredValue::Any(take_any_box(left)));
            work.push(PredValue::Any(take_any_box(right)));
        },
        AnyPred::Not(body) => work.push(PredValue::Any(take_any_box(body))),
        AnyPred::True
        | AnyPred::False
        | AnyPred::Int(_)
        | AnyPred::Char(_)
        | AnyPred::Bool(_)
        | AnyPred::BigInt(_)
        | AnyPred::BigRat(_)
        | AnyPred::Fixed(_)
        | AnyPred::Float(_)
        | AnyPred::Str(_) => {},
    }
}

fn take_pred_value_children(value: &mut PredValue, work: &mut Vec<PredValue>) {
    match value {
        PredValue::Any(pred) => take_any_pred_children(pred, work),
        PredValue::Product(pred) => match pred {
            NaryProductPred::Field(_, inner) => {
                work.push(PredValue::Any(std::mem::replace(inner, AnyPred::True)));
            },
            NaryProductPred::And(left, right) | NaryProductPred::Or(left, right) => {
                work.push(PredValue::Product(*std::mem::replace(
                    left,
                    Box::new(NaryProductPred::True),
                )));
                work.push(PredValue::Product(*std::mem::replace(
                    right,
                    Box::new(NaryProductPred::True),
                )));
            },
            NaryProductPred::Not(body) => work.push(PredValue::Product(*std::mem::replace(
                body,
                Box::new(NaryProductPred::True),
            ))),
            NaryProductPred::True | NaryProductPred::False => {},
        },
        PredValue::Sum(pred) => match pred {
            SumPred::InVariant(_, inner) => {
                work.push(PredValue::Any(std::mem::replace(inner, AnyPred::True)));
            },
            SumPred::And(left, right) | SumPred::Or(left, right) => {
                work.push(PredValue::Sum(*std::mem::replace(left, Box::new(SumPred::True))));
                work.push(PredValue::Sum(*std::mem::replace(right, Box::new(SumPred::True))));
            },
            SumPred::Not(body) => {
                work.push(PredValue::Sum(*std::mem::replace(body, Box::new(SumPred::True))));
            },
            SumPred::True | SumPred::False | SumPred::TagIs(_) => {},
        },
        PredValue::Regex(pred) => match pred {
            RegexPred::Elem(inner) => {
                work.push(PredValue::Any(std::mem::replace(inner, AnyPred::True)));
            },
            RegexPred::Concat(left, right)
            | RegexPred::Alt(left, right)
            | RegexPred::Inter(left, right) => {
                work.push(PredValue::Regex(*std::mem::replace(left, Box::new(RegexPred::Empty))));
                work.push(PredValue::Regex(*std::mem::replace(right, Box::new(RegexPred::Empty))));
            },
            RegexPred::Star(body) | RegexPred::Compl(body) => {
                work.push(PredValue::Regex(*std::mem::replace(body, Box::new(RegexPred::Empty))));
            },
            RegexPred::Empty | RegexPred::Epsilon | RegexPred::Length(_, _) => {},
        },
        PredValue::Bag(pred) => match pred {
            BagPred::Count { class, .. } => {
                work.push(PredValue::Any(std::mem::replace(class, AnyPred::True)));
            },
            BagPred::And(left, right) | BagPred::Or(left, right) => {
                work.push(PredValue::Bag(*std::mem::replace(left, Box::new(BagPred::True))));
                work.push(PredValue::Bag(*std::mem::replace(right, Box::new(BagPred::True))));
            },
            BagPred::Not(body) => {
                work.push(PredValue::Bag(*std::mem::replace(body, Box::new(BagPred::True))));
            },
            BagPred::True | BagPred::False => {},
        },
        PredValue::Tree(pred) => match pred {
            TreePred::Node { payload_guard, children, .. } => {
                if let Some(payload) = payload_guard.take() {
                    work.push(PredValue::Any(payload));
                }
                work.extend(std::mem::take(children).into_iter().map(PredValue::Tree));
            },
            TreePred::And(left, right) | TreePred::Or(left, right) => {
                work.push(PredValue::Tree(*std::mem::replace(left, Box::new(TreePred::True))));
                work.push(PredValue::Tree(*std::mem::replace(right, Box::new(TreePred::True))));
            },
            TreePred::Not(body) => {
                work.push(PredValue::Tree(*std::mem::replace(body, Box::new(TreePred::True))));
            },
            TreePred::True | TreePred::False | TreePred::Wild => {},
        },
        PredValue::Map(pred) => match pred {
            MapPred::CountEntries { key_class, val_class, .. } => {
                work.push(PredValue::Any(std::mem::replace(key_class, AnyPred::True)));
                work.push(PredValue::Any(std::mem::replace(val_class, AnyPred::True)));
            },
            MapPred::And(left, right) | MapPred::Or(left, right) => {
                work.push(PredValue::Map(*std::mem::replace(left, Box::new(MapPred::True))));
                work.push(PredValue::Map(*std::mem::replace(right, Box::new(MapPred::True))));
            },
            MapPred::Not(body) => {
                work.push(PredValue::Map(*std::mem::replace(body, Box::new(MapPred::True))));
            },
            MapPred::True | MapPred::False => {},
        },
    }
}

impl Drop for AnyPred {
    fn drop(&mut self) {
        let mut work = Vec::new();
        take_any_pred_children(self, &mut work);
        while let Some(mut value) = work.pop() {
            take_pred_value_children(&mut value, &mut work);
        }
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// AnyAlgebra + embedded structured algebras
// ══════════════════════════════════════════════════════════════════════════════

enum AlgebraCloneTask<'algebra> {
    Visit(&'algebra AnyAlgebra),
    Product(usize),
    Sum(usize),
    List,
    Bag,
    Tree {
        arities: std::collections::HashMap<String, usize>,
        payloaded: std::collections::HashSet<String>,
    },
    Map,
}

impl Clone for AnyAlgebra {
    fn clone(&self) -> Self {
        let mut tasks = vec![AlgebraCloneTask::Visit(self)];
        let mut values = Vec::new();
        while let Some(task) = tasks.pop() {
            match task {
                AlgebraCloneTask::Visit(AnyAlgebra::Int(value)) => {
                    values.push(AnyAlgebra::Int(value.clone()));
                },
                AlgebraCloneTask::Visit(AnyAlgebra::Char(value)) => {
                    values.push(AnyAlgebra::Char(value.clone()));
                },
                AlgebraCloneTask::Visit(AnyAlgebra::Bool(value)) => {
                    values.push(AnyAlgebra::Bool(value.clone()));
                },
                AlgebraCloneTask::Visit(AnyAlgebra::BigInt(value)) => {
                    values.push(AnyAlgebra::BigInt(value.clone()));
                },
                AlgebraCloneTask::Visit(AnyAlgebra::BigRat(value)) => {
                    values.push(AnyAlgebra::BigRat(value.clone()));
                },
                AlgebraCloneTask::Visit(AnyAlgebra::Fixed(value)) => {
                    values.push(AnyAlgebra::Fixed(value.clone()));
                },
                AlgebraCloneTask::Visit(AnyAlgebra::Float(value)) => {
                    values.push(AnyAlgebra::Float(value.clone()));
                },
                AlgebraCloneTask::Visit(AnyAlgebra::Str(value)) => {
                    values.push(AnyAlgebra::Str(value.clone()));
                },
                AlgebraCloneTask::Visit(AnyAlgebra::Product(algebra)) => {
                    push_algebra_sequence(
                        &mut tasks,
                        AlgebraCloneTask::Product(algebra.fields.len()),
                        &algebra.fields,
                    );
                },
                AlgebraCloneTask::Visit(AnyAlgebra::Sum(algebra)) => {
                    push_algebra_sequence(
                        &mut tasks,
                        AlgebraCloneTask::Sum(algebra.variants.len()),
                        &algebra.variants,
                    );
                },
                AlgebraCloneTask::Visit(AnyAlgebra::List(algebra)) => {
                    tasks.push(AlgebraCloneTask::List);
                    tasks.push(AlgebraCloneTask::Visit(&algebra.elem));
                },
                AlgebraCloneTask::Visit(AnyAlgebra::Bag(algebra)) => {
                    tasks.push(AlgebraCloneTask::Bag);
                    tasks.push(AlgebraCloneTask::Visit(&algebra.elem));
                },
                AlgebraCloneTask::Visit(AnyAlgebra::Tree(algebra)) => {
                    tasks.push(AlgebraCloneTask::Tree {
                        arities: algebra.arities.clone(),
                        payloaded: algebra.payloaded.clone(),
                    });
                    tasks.push(AlgebraCloneTask::Visit(&algebra.elem));
                },
                AlgebraCloneTask::Visit(AnyAlgebra::Map(algebra)) => {
                    tasks.push(AlgebraCloneTask::Map);
                    tasks.push(AlgebraCloneTask::Visit(&algebra.val));
                    tasks.push(AlgebraCloneTask::Visit(&algebra.key));
                },
                AlgebraCloneTask::Product(count) => {
                    let fields = take_algebra_values(&mut values, count);
                    values.push(AnyAlgebra::Product(Box::new(NaryProductAlgebra { fields })));
                },
                AlgebraCloneTask::Sum(count) => {
                    let variants = take_algebra_values(&mut values, count);
                    values.push(AnyAlgebra::Sum(Box::new(SumAlgebra { variants })));
                },
                AlgebraCloneTask::List => {
                    let elem = values.pop().expect("AnyAlgebra clone lost list element");
                    values.push(AnyAlgebra::List(Box::new(RegexAlgebra { elem })));
                },
                AlgebraCloneTask::Bag => {
                    let elem = values.pop().expect("AnyAlgebra clone lost bag element");
                    values.push(AnyAlgebra::Bag(Box::new(BagAlgebra { elem })));
                },
                AlgebraCloneTask::Tree { arities, payloaded } => {
                    let elem = values.pop().expect("AnyAlgebra clone lost tree element");
                    values.push(AnyAlgebra::Tree(Box::new(TreeAlgebra {
                        elem,
                        arities,
                        payloaded,
                    })));
                },
                AlgebraCloneTask::Map => {
                    let val = values
                        .pop()
                        .expect("AnyAlgebra clone lost map value algebra");
                    let key = values.pop().expect("AnyAlgebra clone lost map key algebra");
                    values.push(AnyAlgebra::Map(Box::new(MapAlgebra { key, val })));
                },
            }
        }
        debug_assert_eq!(values.len(), 1);
        values.pop().expect("AnyAlgebra clone produced no value")
    }
}

fn push_algebra_sequence<'algebra>(
    tasks: &mut Vec<AlgebraCloneTask<'algebra>>,
    build: AlgebraCloneTask<'algebra>,
    values: &'algebra [AnyAlgebra],
) {
    tasks.push(build);
    for value in values.iter().rev() {
        tasks.push(AlgebraCloneTask::Visit(value));
    }
}

fn take_algebra_values(values: &mut Vec<AnyAlgebra>, count: usize) -> Vec<AnyAlgebra> {
    let start = values
        .len()
        .checked_sub(count)
        .expect("AnyAlgebra clone lost structured elements");
    values.split_off(start)
}

enum AlgebraDebugTask<'algebra> {
    Visit(&'algebra AnyAlgebra),
    Text(&'static str),
    TreeSuffix(&'algebra TreeAlgebra<AnyAlgebra>),
}

impl fmt::Debug for AnyAlgebra {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut tasks = vec![AlgebraDebugTask::Visit(self)];
        while let Some(task) = tasks.pop() {
            match task {
                AlgebraDebugTask::Text(text) => f.write_str(text)?,
                AlgebraDebugTask::TreeSuffix(algebra) => write!(
                    f,
                    ", arities: {:?}, payloaded: {:?} }})",
                    algebra.arities, algebra.payloaded
                )?,
                AlgebraDebugTask::Visit(AnyAlgebra::Int(value)) => {
                    write!(f, "Int({value:?})")?;
                },
                AlgebraDebugTask::Visit(AnyAlgebra::Char(value)) => {
                    write!(f, "Char({value:?})")?;
                },
                AlgebraDebugTask::Visit(AnyAlgebra::Bool(value)) => {
                    write!(f, "Bool({value:?})")?;
                },
                AlgebraDebugTask::Visit(AnyAlgebra::BigInt(value)) => {
                    write!(f, "BigInt({value:?})")?;
                },
                AlgebraDebugTask::Visit(AnyAlgebra::BigRat(value)) => {
                    write!(f, "BigRat({value:?})")?;
                },
                AlgebraDebugTask::Visit(AnyAlgebra::Fixed(value)) => {
                    write!(f, "Fixed({value:?})")?;
                },
                AlgebraDebugTask::Visit(AnyAlgebra::Float(value)) => {
                    write!(f, "Float({value:?})")?;
                },
                AlgebraDebugTask::Visit(AnyAlgebra::Str(value)) => {
                    write!(f, "Str({value:?})")?;
                },
                AlgebraDebugTask::Visit(AnyAlgebra::Product(algebra)) => {
                    f.write_str("Product(NaryProductAlgebra { fields: [")?;
                    push_algebra_debug_sequence(&mut tasks, &algebra.fields, "] })");
                },
                AlgebraDebugTask::Visit(AnyAlgebra::Sum(algebra)) => {
                    f.write_str("Sum(SumAlgebra { variants: [")?;
                    push_algebra_debug_sequence(&mut tasks, &algebra.variants, "] })");
                },
                AlgebraDebugTask::Visit(AnyAlgebra::List(algebra)) => {
                    f.write_str("List(RegexAlgebra { elem: ")?;
                    tasks.push(AlgebraDebugTask::Text(" })"));
                    tasks.push(AlgebraDebugTask::Visit(&algebra.elem));
                },
                AlgebraDebugTask::Visit(AnyAlgebra::Bag(algebra)) => {
                    f.write_str("Bag(BagAlgebra { elem: ")?;
                    tasks.push(AlgebraDebugTask::Text(" })"));
                    tasks.push(AlgebraDebugTask::Visit(&algebra.elem));
                },
                AlgebraDebugTask::Visit(AnyAlgebra::Tree(algebra)) => {
                    f.write_str("Tree(TreeAlgebra { elem: ")?;
                    tasks.push(AlgebraDebugTask::TreeSuffix(algebra));
                    tasks.push(AlgebraDebugTask::Visit(&algebra.elem));
                },
                AlgebraDebugTask::Visit(AnyAlgebra::Map(algebra)) => {
                    f.write_str("Map(MapAlgebra { key: ")?;
                    tasks.push(AlgebraDebugTask::Text(" })"));
                    tasks.push(AlgebraDebugTask::Visit(&algebra.val));
                    tasks.push(AlgebraDebugTask::Text(", val: "));
                    tasks.push(AlgebraDebugTask::Visit(&algebra.key));
                },
            }
        }
        Ok(())
    }
}

fn push_algebra_debug_sequence<'algebra>(
    tasks: &mut Vec<AlgebraDebugTask<'algebra>>,
    values: &'algebra [AnyAlgebra],
    suffix: &'static str,
) {
    tasks.push(AlgebraDebugTask::Text(suffix));
    for (index, value) in values.iter().enumerate().rev() {
        tasks.push(AlgebraDebugTask::Visit(value));
        if index > 0 {
            tasks.push(AlgebraDebugTask::Text(", "));
        }
    }
}

fn placeholder_algebra() -> AnyAlgebra {
    AnyAlgebra::Int(IntervalAlgebra::new(0, 1))
}

fn take_any_algebra_children(algebra: &mut AnyAlgebra, work: &mut Vec<AnyAlgebra>) {
    match algebra {
        AnyAlgebra::Product(algebra) => work.append(&mut algebra.fields),
        AnyAlgebra::Sum(algebra) => work.append(&mut algebra.variants),
        AnyAlgebra::List(algebra) => {
            work.push(std::mem::replace(&mut algebra.elem, placeholder_algebra()));
        },
        AnyAlgebra::Bag(algebra) => {
            work.push(std::mem::replace(&mut algebra.elem, placeholder_algebra()));
        },
        AnyAlgebra::Tree(algebra) => {
            work.push(std::mem::replace(&mut algebra.elem, placeholder_algebra()));
        },
        AnyAlgebra::Map(algebra) => {
            work.push(std::mem::replace(&mut algebra.key, placeholder_algebra()));
            work.push(std::mem::replace(&mut algebra.val, placeholder_algebra()));
        },
        AnyAlgebra::Int(_)
        | AnyAlgebra::Char(_)
        | AnyAlgebra::Bool(_)
        | AnyAlgebra::BigInt(_)
        | AnyAlgebra::BigRat(_)
        | AnyAlgebra::Fixed(_)
        | AnyAlgebra::Float(_)
        | AnyAlgebra::Str(_) => {},
    }
}

impl Drop for AnyAlgebra {
    fn drop(&mut self) {
        let mut work = Vec::new();
        take_any_algebra_children(self, &mut work);
        while let Some(mut algebra) = work.pop() {
            take_any_algebra_children(&mut algebra, &mut work);
        }
    }
}
