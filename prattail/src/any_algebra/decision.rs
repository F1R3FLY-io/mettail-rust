use std::collections::HashMap;

use crate::collection_algebra::{BagAlgebra, BagPred, MapAlgebra, MapPred};
use crate::product_nary::{NaryProductAlgebra, NaryProductPred, SumAlgebra, SumPred, SumValue};
use crate::regex_sfa::{RegexAlgebra, RegexPred};
use crate::sym_tree::{SymTerm, TreeAlgebra, TreePred};
use crate::symbolic::BooleanAlgebra;

use super::{AnyAlgebra, AnyDomain, AnyPred};

#[path = "decision/sfa.rs"]
mod sfa;
#[path = "decision/solver.rs"]
mod solver;
#[path = "decision/tree.rs"]
mod tree;

pub(super) fn is_satisfiable(algebra: &AnyAlgebra, predicate: &AnyPred) -> bool {
    solver::is_satisfiable(algebra, predicate)
}

pub(super) fn witness(algebra: &AnyAlgebra, predicate: &AnyPred) -> Option<AnyDomain> {
    solver::witness(algebra, predicate)
}

#[derive(Clone, Copy)]
enum EvalNode<'a> {
    Any {
        algebra: &'a AnyAlgebra,
        predicate: &'a AnyPred,
        element: &'a AnyDomain,
    },
    AnyTrue {
        algebra: &'a AnyAlgebra,
        element: &'a AnyDomain,
    },
    Product {
        algebra: &'a NaryProductAlgebra<AnyAlgebra>,
        predicate: &'a NaryProductPred<AnyPred>,
        element: &'a [AnyDomain],
    },
    Sum {
        algebra: &'a SumAlgebra<AnyAlgebra>,
        predicate: &'a SumPred<AnyPred>,
        element: &'a SumValue<AnyDomain>,
    },
    Bag {
        algebra: &'a BagAlgebra<AnyAlgebra>,
        predicate: &'a BagPred<AnyPred>,
        element: &'a [AnyDomain],
    },
    Map {
        algebra: &'a MapAlgebra<AnyAlgebra, AnyAlgebra>,
        predicate: &'a MapPred<AnyPred, AnyPred>,
        element: &'a [(AnyDomain, AnyDomain)],
    },
    Tree {
        algebra: &'a TreeAlgebra<AnyAlgebra>,
        predicate: &'a TreePred<AnyPred>,
        element: &'a SymTerm<AnyDomain>,
    },
    TreeUniverse {
        algebra: &'a TreeAlgebra<AnyAlgebra>,
        element: &'a SymTerm<AnyDomain>,
    },
}

enum EvalTask<'a> {
    Visit(EvalNode<'a>),
    Not,
    AndRight(EvalNode<'a>),
    OrRight(EvalNode<'a>),
    All(usize),
    TreeNotAfterUniverse {
        algebra: &'a TreeAlgebra<AnyAlgebra>,
        predicate: &'a TreePred<AnyPred>,
        element: &'a SymTerm<AnyDomain>,
    },
    TreeNegate,
    BagCount {
        algebra: &'a AnyAlgebra,
        predicate: &'a AnyPred,
        elements: &'a [AnyDomain],
        index: usize,
        count: u64,
        lo: u64,
        hi: Option<u64>,
    },
    BagCountAfterElement {
        algebra: &'a AnyAlgebra,
        predicate: &'a AnyPred,
        elements: &'a [AnyDomain],
        index: usize,
        count: u64,
        lo: u64,
        hi: Option<u64>,
    },
    MapCount {
        key_algebra: &'a AnyAlgebra,
        value_algebra: &'a AnyAlgebra,
        key_predicate: &'a AnyPred,
        value_predicate: &'a AnyPred,
        elements: &'a [(AnyDomain, AnyDomain)],
        index: usize,
        count: u64,
        lo: u64,
        hi: Option<u64>,
    },
    MapCountAfterKey {
        key_algebra: &'a AnyAlgebra,
        value_algebra: &'a AnyAlgebra,
        key_predicate: &'a AnyPred,
        value_predicate: &'a AnyPred,
        elements: &'a [(AnyDomain, AnyDomain)],
        index: usize,
        count: u64,
        lo: u64,
        hi: Option<u64>,
    },
    MapCountAfterValue {
        key_algebra: &'a AnyAlgebra,
        value_algebra: &'a AnyAlgebra,
        key_predicate: &'a AnyPred,
        value_predicate: &'a AnyPred,
        elements: &'a [(AnyDomain, AnyDomain)],
        index: usize,
        count: u64,
        lo: u64,
        hi: Option<u64>,
    },
    Regex(RegexEvalMachine<'a>),
}

pub(super) fn evaluate(algebra: &AnyAlgebra, predicate: &AnyPred, element: &AnyDomain) -> bool {
    let mut tasks = vec![EvalTask::Visit(EvalNode::Any { algebra, predicate, element })];
    let mut values = Vec::new();
    while let Some(task) = tasks.pop() {
        match task {
            EvalTask::Visit(node) => visit(node, &mut tasks, &mut values),
            EvalTask::Not => {
                let value = values.pop().expect("Any evaluation lost negated value");
                values.push(!value);
            },
            EvalTask::AndRight(right) => {
                let left = values.pop().expect("Any evaluation lost left conjunction");
                if left {
                    tasks.push(EvalTask::Visit(right));
                } else {
                    values.push(false);
                }
            },
            EvalTask::OrRight(right) => {
                let left = values.pop().expect("Any evaluation lost left disjunction");
                if left {
                    values.push(true);
                } else {
                    tasks.push(EvalTask::Visit(right));
                }
            },
            EvalTask::All(count) => {
                let start = values
                    .len()
                    .checked_sub(count)
                    .expect("Any evaluation lost conjunction operands");
                let result = values[start..].iter().all(|value| *value);
                values.truncate(start);
                values.push(result);
            },
            EvalTask::TreeNotAfterUniverse { algebra, predicate, element } => {
                let in_universe = values.pop().expect("tree evaluation lost universe result");
                if in_universe {
                    tasks.push(EvalTask::TreeNegate);
                    tasks.push(EvalTask::Visit(EvalNode::Tree { algebra, predicate, element }));
                } else {
                    values.push(false);
                }
            },
            EvalTask::TreeNegate => {
                let value = values.pop().expect("tree evaluation lost complement body");
                values.push(!value);
            },
            EvalTask::BagCount {
                algebra,
                predicate,
                elements,
                index,
                count,
                lo,
                hi,
            } => {
                if index == elements.len() {
                    values.push(count >= lo && hi.is_none_or(|upper| count <= upper));
                } else {
                    tasks.push(EvalTask::BagCountAfterElement {
                        algebra,
                        predicate,
                        elements,
                        index,
                        count,
                        lo,
                        hi,
                    });
                    tasks.push(EvalTask::Visit(EvalNode::Any {
                        algebra,
                        predicate,
                        element: &elements[index],
                    }));
                }
            },
            EvalTask::BagCountAfterElement {
                algebra,
                predicate,
                elements,
                index,
                count,
                lo,
                hi,
            } => {
                let matches = values.pop().expect("bag evaluation lost element verdict");
                tasks.push(EvalTask::BagCount {
                    algebra,
                    predicate,
                    elements,
                    index: index + 1,
                    count: count + u64::from(matches),
                    lo,
                    hi,
                });
            },
            EvalTask::MapCount {
                key_algebra,
                value_algebra,
                key_predicate,
                value_predicate,
                elements,
                index,
                count,
                lo,
                hi,
            } => {
                if index == elements.len() {
                    values.push(count >= lo && hi.is_none_or(|upper| count <= upper));
                } else {
                    tasks.push(EvalTask::MapCountAfterKey {
                        key_algebra,
                        value_algebra,
                        key_predicate,
                        value_predicate,
                        elements,
                        index,
                        count,
                        lo,
                        hi,
                    });
                    tasks.push(EvalTask::Visit(EvalNode::Any {
                        algebra: key_algebra,
                        predicate: key_predicate,
                        element: &elements[index].0,
                    }));
                }
            },
            EvalTask::MapCountAfterKey {
                key_algebra,
                value_algebra,
                key_predicate,
                value_predicate,
                elements,
                index,
                count,
                lo,
                hi,
            } => {
                let key_matches = values.pop().expect("map evaluation lost key verdict");
                if key_matches {
                    tasks.push(EvalTask::MapCountAfterValue {
                        key_algebra,
                        value_algebra,
                        key_predicate,
                        value_predicate,
                        elements,
                        index,
                        count,
                        lo,
                        hi,
                    });
                    tasks.push(EvalTask::Visit(EvalNode::Any {
                        algebra: value_algebra,
                        predicate: value_predicate,
                        element: &elements[index].1,
                    }));
                } else {
                    tasks.push(EvalTask::MapCount {
                        key_algebra,
                        value_algebra,
                        key_predicate,
                        value_predicate,
                        elements,
                        index: index + 1,
                        count,
                        lo,
                        hi,
                    });
                }
            },
            EvalTask::MapCountAfterValue {
                key_algebra,
                value_algebra,
                key_predicate,
                value_predicate,
                elements,
                index,
                count,
                lo,
                hi,
            } => {
                let value_matches = values.pop().expect("map evaluation lost value verdict");
                tasks.push(EvalTask::MapCount {
                    key_algebra,
                    value_algebra,
                    key_predicate,
                    value_predicate,
                    elements,
                    index: index + 1,
                    count: count + u64::from(value_matches),
                    lo,
                    hi,
                });
            },
            EvalTask::Regex(mut machine) => {
                let resumed = machine
                    .awaiting_query()
                    .then(|| values.pop().expect("regex evaluation lost element verdict"));
                match machine.advance(resumed) {
                    RegexStep::Query(node) => {
                        tasks.push(EvalTask::Regex(machine));
                        tasks.push(EvalTask::Visit(node));
                    },
                    RegexStep::Done(value) => values.push(value),
                }
            },
        }
    }
    debug_assert_eq!(values.len(), 1);
    values.pop().expect("Any evaluation produced no verdict")
}

fn visit<'a>(node: EvalNode<'a>, tasks: &mut Vec<EvalTask<'a>>, values: &mut Vec<bool>) {
    match node {
        EvalNode::Any { algebra, predicate, element } => match predicate {
            _ if algebra.sort() != element.sort() => values.push(false),
            AnyPred::True => tasks.push(EvalTask::Visit(EvalNode::AnyTrue { algebra, element })),
            AnyPred::False => values.push(false),
            AnyPred::And(left, right) => {
                tasks.push(EvalTask::AndRight(EvalNode::Any {
                    algebra,
                    predicate: right,
                    element,
                }));
                tasks.push(EvalTask::Visit(EvalNode::Any { algebra, predicate: left, element }));
            },
            AnyPred::Or(left, right) => {
                tasks.push(EvalTask::OrRight(EvalNode::Any { algebra, predicate: right, element }));
                tasks.push(EvalTask::Visit(EvalNode::Any { algebra, predicate: left, element }));
            },
            AnyPred::Not(body) => {
                tasks.push(EvalTask::Not);
                tasks.push(EvalTask::Visit(EvalNode::Any { algebra, predicate: body, element }));
            },
            _ => visit_any_leaf(algebra, predicate, element, tasks, values),
        },
        EvalNode::AnyTrue { algebra, element } => visit_any_true(algebra, element, tasks, values),
        EvalNode::Product { algebra, predicate, element } => match predicate {
            NaryProductPred::True => values.push(true),
            NaryProductPred::False => values.push(false),
            NaryProductPred::Field(index, predicate) => {
                if let (Some(field), Some(value)) =
                    (algebra.fields.get(*index), element.get(*index))
                {
                    tasks.push(EvalTask::Visit(EvalNode::Any {
                        algebra: field,
                        predicate,
                        element: value,
                    }));
                } else {
                    values.push(false);
                }
            },
            NaryProductPred::And(left, right) => {
                tasks.push(EvalTask::AndRight(EvalNode::Product {
                    algebra,
                    predicate: right,
                    element,
                }));
                tasks.push(EvalTask::Visit(EvalNode::Product {
                    algebra,
                    predicate: left,
                    element,
                }));
            },
            NaryProductPred::Or(left, right) => {
                tasks.push(EvalTask::OrRight(EvalNode::Product {
                    algebra,
                    predicate: right,
                    element,
                }));
                tasks.push(EvalTask::Visit(EvalNode::Product {
                    algebra,
                    predicate: left,
                    element,
                }));
            },
            NaryProductPred::Not(body) => {
                tasks.push(EvalTask::Not);
                tasks.push(EvalTask::Visit(EvalNode::Product {
                    algebra,
                    predicate: body,
                    element,
                }));
            },
        },
        EvalNode::Sum { algebra, predicate, element } => match predicate {
            SumPred::True => values.push(true),
            SumPred::False => values.push(false),
            SumPred::TagIs(tag) => values.push(*tag == element.tag),
            SumPred::InVariant(tag, predicate) => {
                if *tag == element.tag {
                    if let Some(variant) = algebra.variants.get(element.tag) {
                        tasks.push(EvalTask::Visit(EvalNode::Any {
                            algebra: variant,
                            predicate,
                            element: &element.payload,
                        }));
                    } else {
                        values.push(false);
                    }
                } else {
                    values.push(false);
                }
            },
            SumPred::And(left, right) => {
                tasks.push(EvalTask::AndRight(EvalNode::Sum {
                    algebra,
                    predicate: right,
                    element,
                }));
                tasks.push(EvalTask::Visit(EvalNode::Sum { algebra, predicate: left, element }));
            },
            SumPred::Or(left, right) => {
                tasks.push(EvalTask::OrRight(EvalNode::Sum { algebra, predicate: right, element }));
                tasks.push(EvalTask::Visit(EvalNode::Sum { algebra, predicate: left, element }));
            },
            SumPred::Not(body) => {
                tasks.push(EvalTask::Not);
                tasks.push(EvalTask::Visit(EvalNode::Sum { algebra, predicate: body, element }));
            },
        },
        EvalNode::Bag { algebra, predicate, element } => match predicate {
            BagPred::True => values.push(true),
            BagPred::False => values.push(false),
            BagPred::Count { class, lo, hi } => tasks.push(EvalTask::BagCount {
                algebra: &algebra.elem,
                predicate: class,
                elements: element,
                index: 0,
                count: 0,
                lo: *lo,
                hi: *hi,
            }),
            BagPred::And(left, right) => {
                tasks.push(EvalTask::AndRight(EvalNode::Bag {
                    algebra,
                    predicate: right,
                    element,
                }));
                tasks.push(EvalTask::Visit(EvalNode::Bag { algebra, predicate: left, element }));
            },
            BagPred::Or(left, right) => {
                tasks.push(EvalTask::OrRight(EvalNode::Bag { algebra, predicate: right, element }));
                tasks.push(EvalTask::Visit(EvalNode::Bag { algebra, predicate: left, element }));
            },
            BagPred::Not(body) => {
                tasks.push(EvalTask::Not);
                tasks.push(EvalTask::Visit(EvalNode::Bag { algebra, predicate: body, element }));
            },
        },
        EvalNode::Map { algebra, predicate, element } => match predicate {
            MapPred::True => values.push(true),
            MapPred::False => values.push(false),
            MapPred::CountEntries { key_class, val_class, lo, hi } => {
                tasks.push(EvalTask::MapCount {
                    key_algebra: &algebra.key,
                    value_algebra: &algebra.val,
                    key_predicate: key_class,
                    value_predicate: val_class,
                    elements: element,
                    index: 0,
                    count: 0,
                    lo: *lo,
                    hi: *hi,
                });
            },
            MapPred::And(left, right) => {
                tasks.push(EvalTask::AndRight(EvalNode::Map {
                    algebra,
                    predicate: right,
                    element,
                }));
                tasks.push(EvalTask::Visit(EvalNode::Map { algebra, predicate: left, element }));
            },
            MapPred::Or(left, right) => {
                tasks.push(EvalTask::OrRight(EvalNode::Map { algebra, predicate: right, element }));
                tasks.push(EvalTask::Visit(EvalNode::Map { algebra, predicate: left, element }));
            },
            MapPred::Not(body) => {
                tasks.push(EvalTask::Not);
                tasks.push(EvalTask::Visit(EvalNode::Map { algebra, predicate: body, element }));
            },
        },
        EvalNode::Tree { algebra, predicate, element } => match predicate {
            TreePred::True | TreePred::Wild => {
                tasks.push(EvalTask::Visit(EvalNode::TreeUniverse { algebra, element }));
            },
            TreePred::False => values.push(false),
            TreePred::Node { constructor, payload_guard, children } => {
                if constructor != &element.constructor || children.len() != element.children.len() {
                    values.push(false);
                    return;
                }
                let payload_count = usize::from(payload_guard.is_some());
                if payload_guard.is_some() != element.payload.is_some() {
                    values.push(false);
                    return;
                }
                tasks.push(EvalTask::All(children.len() + payload_count));
                if let (Some(predicate), Some(value)) =
                    (payload_guard.as_ref(), element.payload.as_ref())
                {
                    tasks.push(EvalTask::Visit(EvalNode::Any {
                        algebra: &algebra.elem,
                        predicate,
                        element: value,
                    }));
                }
                for (predicate, child) in children.iter().zip(&element.children).rev() {
                    tasks.push(EvalTask::Visit(EvalNode::Tree {
                        algebra,
                        predicate,
                        element: child,
                    }));
                }
            },
            TreePred::And(left, right) => {
                tasks.push(EvalTask::AndRight(EvalNode::Tree {
                    algebra,
                    predicate: right,
                    element,
                }));
                tasks.push(EvalTask::Visit(EvalNode::Tree { algebra, predicate: left, element }));
            },
            TreePred::Or(left, right) => {
                tasks.push(EvalTask::OrRight(EvalNode::Tree {
                    algebra,
                    predicate: right,
                    element,
                }));
                tasks.push(EvalTask::Visit(EvalNode::Tree { algebra, predicate: left, element }));
            },
            TreePred::Not(body) => {
                tasks.push(EvalTask::TreeNotAfterUniverse { algebra, predicate: body, element });
                tasks.push(EvalTask::Visit(EvalNode::TreeUniverse { algebra, element }));
            },
        },
        EvalNode::TreeUniverse { algebra, element } => {
            let Some(arity) = algebra.arities.get(&element.constructor) else {
                values.push(false);
                return;
            };
            if *arity != element.children.len()
                || algebra.payloaded.contains(&element.constructor) != element.payload.is_some()
            {
                values.push(false);
                return;
            }
            let payload_count = usize::from(element.payload.is_some());
            tasks.push(EvalTask::All(element.children.len() + payload_count));
            if let Some(payload) = &element.payload {
                tasks.push(EvalTask::Visit(EvalNode::AnyTrue {
                    algebra: &algebra.elem,
                    element: payload,
                }));
            }
            for child in element.children.iter().rev() {
                tasks.push(EvalTask::Visit(EvalNode::TreeUniverse { algebra, element: child }));
            }
        },
    }
}

fn visit_any_leaf<'a>(
    algebra: &'a AnyAlgebra,
    predicate: &'a AnyPred,
    element: &'a AnyDomain,
    tasks: &mut Vec<EvalTask<'a>>,
    values: &mut Vec<bool>,
) {
    match (algebra, predicate, element) {
        (AnyAlgebra::Int(inner), AnyPred::Int(predicate), AnyDomain::Int(element)) => {
            values.push(inner.evaluate(predicate, element));
        },
        (AnyAlgebra::Char(inner), AnyPred::Char(predicate), AnyDomain::Char(element)) => {
            values.push(inner.evaluate(predicate, element));
        },
        (AnyAlgebra::Bool(inner), AnyPred::Bool(predicate), AnyDomain::Bool(element)) => {
            values.push(inner.evaluate(predicate, element));
        },
        (AnyAlgebra::BigInt(inner), AnyPred::BigInt(predicate), AnyDomain::BigInt(element)) => {
            values.push(inner.evaluate(predicate, element));
        },
        (AnyAlgebra::BigRat(inner), AnyPred::BigRat(predicate), AnyDomain::BigRat(element)) => {
            values.push(inner.evaluate(predicate, element));
        },
        (AnyAlgebra::Fixed(inner), AnyPred::Fixed(predicate), AnyDomain::Fixed(element)) => {
            values.push(inner.evaluate(predicate, element));
        },
        (AnyAlgebra::Float(inner), AnyPred::Float(predicate), AnyDomain::Float(element)) => {
            values.push(inner.evaluate(predicate, element));
        },
        (AnyAlgebra::Str(inner), AnyPred::Str(predicate), AnyDomain::Str(element)) => {
            values.push(inner.evaluate(predicate, element));
        },
        (AnyAlgebra::Product(inner), AnyPred::Product(predicate), AnyDomain::Product(element)) => {
            tasks.push(EvalTask::Visit(EvalNode::Product { algebra: inner, predicate, element }));
        },
        (AnyAlgebra::Sum(inner), AnyPred::Sum(predicate), AnyDomain::Sum(element)) => {
            tasks.push(EvalTask::Visit(EvalNode::Sum { algebra: inner, predicate, element }));
        },
        (AnyAlgebra::List(inner), AnyPred::List(predicate), AnyDomain::List(element)) => {
            tasks.push(EvalTask::Regex(RegexEvalMachine::new(inner, predicate, element)));
        },
        (AnyAlgebra::Bag(inner), AnyPred::Bag(predicate), AnyDomain::Bag(element)) => {
            tasks.push(EvalTask::Visit(EvalNode::Bag { algebra: inner, predicate, element }));
        },
        (AnyAlgebra::Tree(inner), AnyPred::Tree(predicate), AnyDomain::Tree(element)) => {
            tasks.push(EvalTask::Visit(EvalNode::Tree { algebra: inner, predicate, element }));
        },
        (AnyAlgebra::Map(inner), AnyPred::Map(predicate), AnyDomain::Map(element)) => {
            tasks.push(EvalTask::Visit(EvalNode::Map { algebra: inner, predicate, element }));
        },
        _ => values.push(false),
    }
}

fn visit_any_true<'a>(
    algebra: &'a AnyAlgebra,
    element: &'a AnyDomain,
    tasks: &mut Vec<EvalTask<'a>>,
    values: &mut Vec<bool>,
) {
    match (algebra, element) {
        (AnyAlgebra::Int(_), AnyDomain::Int(_))
        | (AnyAlgebra::Char(_), AnyDomain::Char(_))
        | (AnyAlgebra::Bool(_), AnyDomain::Bool(_))
        | (AnyAlgebra::BigInt(_), AnyDomain::BigInt(_))
        | (AnyAlgebra::BigRat(_), AnyDomain::BigRat(_))
        | (AnyAlgebra::Fixed(_), AnyDomain::Fixed(_))
        | (AnyAlgebra::Float(_), AnyDomain::Float(_))
        | (AnyAlgebra::Str(_), AnyDomain::Str(_))
        | (AnyAlgebra::Product(_), AnyDomain::Product(_))
        | (AnyAlgebra::Sum(_), AnyDomain::Sum(_))
        | (AnyAlgebra::List(_), AnyDomain::List(_))
        | (AnyAlgebra::Bag(_), AnyDomain::Bag(_))
        | (AnyAlgebra::Map(_), AnyDomain::Map(_)) => values.push(true),
        (AnyAlgebra::Tree(inner), AnyDomain::Tree(element)) => {
            tasks.push(EvalTask::Visit(EvalNode::TreeUniverse { algebra: inner, element }));
        },
        _ => values.push(false),
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
struct RegexKey {
    predicate: usize,
    start: usize,
    end: usize,
}

enum RegexTask<'a> {
    Visit {
        predicate: &'a RegexPred<AnyPred>,
        start: usize,
        end: usize,
    },
    Store(RegexKey),
    AndRight {
        predicate: &'a RegexPred<AnyPred>,
        start: usize,
        end: usize,
    },
    OrRight {
        predicate: &'a RegexPred<AnyPred>,
        start: usize,
        end: usize,
    },
    ConcatTry {
        left: &'a RegexPred<AnyPred>,
        right: &'a RegexPred<AnyPred>,
        start: usize,
        end: usize,
        split: usize,
    },
    ConcatAfterLeft {
        left: &'a RegexPred<AnyPred>,
        right: &'a RegexPred<AnyPred>,
        start: usize,
        end: usize,
        split: usize,
    },
    ConcatAfterRight {
        left: &'a RegexPred<AnyPred>,
        right: &'a RegexPred<AnyPred>,
        start: usize,
        end: usize,
        next_split: usize,
    },
    StarTry {
        star: &'a RegexPred<AnyPred>,
        body: &'a RegexPred<AnyPred>,
        start: usize,
        end: usize,
        split: usize,
    },
    StarAfterBody {
        star: &'a RegexPred<AnyPred>,
        body: &'a RegexPred<AnyPred>,
        start: usize,
        end: usize,
        split: usize,
    },
    StarAfterSuffix {
        star: &'a RegexPred<AnyPred>,
        body: &'a RegexPred<AnyPred>,
        start: usize,
        end: usize,
        next_split: usize,
    },
    Universe {
        index: usize,
        end: usize,
    },
    UniverseAfter {
        next: usize,
        end: usize,
    },
    ComplAfterUniverse {
        body: &'a RegexPred<AnyPred>,
        start: usize,
        end: usize,
    },
    ComplNegate,
}

struct RegexEvalMachine<'a> {
    algebra: &'a RegexAlgebra<AnyAlgebra>,
    word: &'a [AnyDomain],
    tasks: Vec<RegexTask<'a>>,
    values: Vec<bool>,
    memo: HashMap<RegexKey, bool>,
    awaiting: bool,
}

enum RegexStep<'a> {
    Query(EvalNode<'a>),
    Done(bool),
}

impl<'a> RegexEvalMachine<'a> {
    fn new(
        algebra: &'a RegexAlgebra<AnyAlgebra>,
        predicate: &'a RegexPred<AnyPred>,
        word: &'a [AnyDomain],
    ) -> Self {
        Self {
            algebra,
            word,
            tasks: vec![RegexTask::Visit { predicate, start: 0, end: word.len() }],
            values: Vec::new(),
            memo: HashMap::new(),
            awaiting: false,
        }
    }

    fn awaiting_query(&self) -> bool {
        self.awaiting
    }

    fn advance(&mut self, resumed: Option<bool>) -> RegexStep<'a> {
        if self.awaiting {
            self.values
                .push(resumed.expect("regex machine resumed without a verdict"));
            self.awaiting = false;
        } else {
            debug_assert!(resumed.is_none());
        }
        while let Some(task) = self.tasks.pop() {
            match task {
                RegexTask::Visit { predicate, start, end } => {
                    let key = RegexKey {
                        predicate: predicate as *const RegexPred<AnyPred> as usize,
                        start,
                        end,
                    };
                    if let Some(value) = self.memo.get(&key) {
                        self.values.push(*value);
                        continue;
                    }
                    self.tasks.push(RegexTask::Store(key));
                    match predicate {
                        RegexPred::Empty => self.values.push(false),
                        RegexPred::Epsilon => self.values.push(start == end),
                        RegexPred::Elem(predicate) => {
                            if end == start + 1 {
                                self.awaiting = true;
                                return RegexStep::Query(EvalNode::Any {
                                    algebra: &self.algebra.elem,
                                    predicate,
                                    element: &self.word[start],
                                });
                            }
                            self.values.push(false);
                        },
                        RegexPred::Length(lo, hi) => {
                            let len = end - start;
                            if len < *lo || hi.is_some_and(|upper| len > upper) {
                                self.values.push(false);
                            } else {
                                self.tasks.push(RegexTask::Universe { index: start, end });
                            }
                        },
                        RegexPred::Concat(left, right) => {
                            self.tasks.push(RegexTask::ConcatTry {
                                left,
                                right,
                                start,
                                end,
                                split: start,
                            });
                        },
                        RegexPred::Alt(left, right) => {
                            self.tasks
                                .push(RegexTask::OrRight { predicate: right, start, end });
                            self.tasks
                                .push(RegexTask::Visit { predicate: left, start, end });
                        },
                        RegexPred::Star(body) => {
                            if start == end {
                                self.values.push(true);
                            } else {
                                self.tasks.push(RegexTask::StarTry {
                                    star: predicate,
                                    body,
                                    start,
                                    end,
                                    split: start + 1,
                                });
                            }
                        },
                        RegexPred::Inter(left, right) => {
                            self.tasks
                                .push(RegexTask::AndRight { predicate: right, start, end });
                            self.tasks
                                .push(RegexTask::Visit { predicate: left, start, end });
                        },
                        RegexPred::Compl(body) => {
                            self.tasks
                                .push(RegexTask::ComplAfterUniverse { body, start, end });
                            self.tasks.push(RegexTask::Universe { index: start, end });
                        },
                    }
                },
                RegexTask::Store(key) => {
                    let value = *self.values.last().expect("regex memo lost result");
                    self.memo.insert(key, value);
                },
                RegexTask::AndRight { predicate, start, end } => {
                    let left = self
                        .values
                        .pop()
                        .expect("regex evaluation lost left intersection");
                    if left {
                        self.tasks.push(RegexTask::Visit { predicate, start, end });
                    } else {
                        self.values.push(false);
                    }
                },
                RegexTask::OrRight { predicate, start, end } => {
                    let left = self
                        .values
                        .pop()
                        .expect("regex evaluation lost left alternation");
                    if left {
                        self.values.push(true);
                    } else {
                        self.tasks.push(RegexTask::Visit { predicate, start, end });
                    }
                },
                RegexTask::ConcatTry { left, right, start, end, split } => {
                    if split > end {
                        self.values.push(false);
                    } else {
                        self.tasks.push(RegexTask::ConcatAfterLeft {
                            left,
                            right,
                            start,
                            end,
                            split,
                        });
                        self.tasks
                            .push(RegexTask::Visit { predicate: left, start, end: split });
                    }
                },
                RegexTask::ConcatAfterLeft { left, right, start, end, split } => {
                    let matches = self.values.pop().expect("regex concat lost left verdict");
                    if matches {
                        self.tasks.push(RegexTask::ConcatAfterRight {
                            left,
                            right,
                            start,
                            end,
                            next_split: split + 1,
                        });
                        self.tasks
                            .push(RegexTask::Visit { predicate: right, start: split, end });
                    } else {
                        self.tasks.push(RegexTask::ConcatTry {
                            left,
                            right,
                            start,
                            end,
                            split: split + 1,
                        });
                    }
                },
                RegexTask::ConcatAfterRight { left, right, start, end, next_split } => {
                    let matches = self.values.pop().expect("regex concat lost right verdict");
                    if matches {
                        self.values.push(true);
                    } else {
                        self.tasks.push(RegexTask::ConcatTry {
                            left,
                            right,
                            start,
                            end,
                            split: next_split,
                        });
                    }
                },
                RegexTask::StarTry { star, body, start, end, split } => {
                    if split > end {
                        self.values.push(false);
                    } else {
                        self.tasks
                            .push(RegexTask::StarAfterBody { star, body, start, end, split });
                        self.tasks
                            .push(RegexTask::Visit { predicate: body, start, end: split });
                    }
                },
                RegexTask::StarAfterBody { star, body, start, end, split } => {
                    let matches = self.values.pop().expect("regex star lost body verdict");
                    if matches {
                        self.tasks.push(RegexTask::StarAfterSuffix {
                            star,
                            body,
                            start,
                            end,
                            next_split: split + 1,
                        });
                        self.tasks
                            .push(RegexTask::Visit { predicate: star, start: split, end });
                    } else {
                        self.tasks.push(RegexTask::StarTry {
                            star,
                            body,
                            start,
                            end,
                            split: split + 1,
                        });
                    }
                },
                RegexTask::StarAfterSuffix { star, body, start, end, next_split } => {
                    let matches = self.values.pop().expect("regex star lost suffix verdict");
                    if matches {
                        self.values.push(true);
                    } else {
                        self.tasks.push(RegexTask::StarTry {
                            star,
                            body,
                            start,
                            end,
                            split: next_split,
                        });
                    }
                },
                RegexTask::Universe { index, end } => {
                    if index == end {
                        self.values.push(true);
                    } else {
                        self.tasks
                            .push(RegexTask::UniverseAfter { next: index + 1, end });
                        self.awaiting = true;
                        return RegexStep::Query(EvalNode::AnyTrue {
                            algebra: &self.algebra.elem,
                            element: &self.word[index],
                        });
                    }
                },
                RegexTask::UniverseAfter { next, end } => {
                    let matches = self
                        .values
                        .pop()
                        .expect("regex universe lost element verdict");
                    if matches {
                        self.tasks.push(RegexTask::Universe { index: next, end });
                    } else {
                        self.values.push(false);
                    }
                },
                RegexTask::ComplAfterUniverse { body, start, end } => {
                    let in_universe = self.values.pop().expect("regex complement lost universe");
                    if in_universe {
                        self.tasks.push(RegexTask::ComplNegate);
                        self.tasks
                            .push(RegexTask::Visit { predicate: body, start, end });
                    } else {
                        self.values.push(false);
                    }
                },
                RegexTask::ComplNegate => {
                    let value = self.values.pop().expect("regex complement lost body");
                    self.values.push(!value);
                },
            }
        }
        debug_assert_eq!(self.values.len(), 1);
        RegexStep::Done(
            self.values
                .pop()
                .expect("regex machine produced no verdict"),
        )
    }
}
