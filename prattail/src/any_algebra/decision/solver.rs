use std::cell::{Cell, RefCell};
use std::future::Future;
use std::pin::Pin;
use std::rc::Rc;
use std::task::{Context, Poll, Waker};

use crate::collection_algebra::{
    BagAlgebra, BagNode, BagPred, MapAlgebra, MapNode, MapPred, Singleton,
};
use crate::symbolic::BooleanAlgebra;

use super::super::{AnyAlgebra, AnyDomain, AnyPred, AnyPredNode};

type SatAnswer = Rc<Cell<Option<bool>>>;
type WitnessAnswer = Rc<RefCell<Option<Option<AnyDomain>>>>;

enum Request<'a> {
    Sat {
        algebra: &'a AnyAlgebra,
        predicate: AnyPred,
        answer: SatAnswer,
    },
    Witness {
        algebra: &'a AnyAlgebra,
        predicate: AnyPred,
        answer: WitnessAnswer,
    },
}

#[derive(Clone)]
pub(super) struct DecisionOracle<'a> {
    pending: Rc<RefCell<Option<Request<'a>>>>,
}

impl<'a> DecisionOracle<'a> {
    fn new() -> Self {
        Self { pending: Rc::new(RefCell::new(None)) }
    }

    pub(super) fn sat(&self, algebra: &'a AnyAlgebra, predicate: AnyPred) -> SatQuery<'a> {
        SatQuery {
            pending: Rc::clone(&self.pending),
            algebra,
            predicate: Some(predicate),
            answer: Rc::new(Cell::new(None)),
        }
    }

    pub(super) fn witness(&self, algebra: &'a AnyAlgebra, predicate: AnyPred) -> WitnessQuery<'a> {
        WitnessQuery {
            pending: Rc::clone(&self.pending),
            algebra,
            predicate: Some(predicate),
            answer: Rc::new(RefCell::new(None)),
        }
    }
}

pub(super) struct SatQuery<'a> {
    pending: Rc<RefCell<Option<Request<'a>>>>,
    algebra: &'a AnyAlgebra,
    predicate: Option<AnyPred>,
    answer: SatAnswer,
}

impl Future for SatQuery<'_> {
    type Output = bool;

    fn poll(mut self: Pin<&mut Self>, _cx: &mut Context<'_>) -> Poll<Self::Output> {
        if let Some(answer) = self.answer.take() {
            return Poll::Ready(answer);
        }
        if let Some(predicate) = self.predicate.take() {
            let previous = self.pending.borrow_mut().replace(Request::Sat {
                algebra: self.algebra,
                predicate,
                answer: Rc::clone(&self.answer),
            });
            assert!(previous.is_none(), "decision executor lost a pending SAT query");
        }
        Poll::Pending
    }
}

pub(super) struct WitnessQuery<'a> {
    pending: Rc<RefCell<Option<Request<'a>>>>,
    algebra: &'a AnyAlgebra,
    predicate: Option<AnyPred>,
    answer: WitnessAnswer,
}

impl Future for WitnessQuery<'_> {
    type Output = Option<AnyDomain>;

    fn poll(mut self: Pin<&mut Self>, _cx: &mut Context<'_>) -> Poll<Self::Output> {
        if let Some(answer) = self.answer.borrow_mut().take() {
            return Poll::Ready(answer);
        }
        if let Some(predicate) = self.predicate.take() {
            let previous = self.pending.borrow_mut().replace(Request::Witness {
                algebra: self.algebra,
                predicate,
                answer: Rc::clone(&self.answer),
            });
            assert!(previous.is_none(), "decision executor lost a pending witness query");
        }
        Poll::Pending
    }
}

enum Frame<'a> {
    Sat {
        future: Pin<Box<dyn Future<Output = bool> + 'a>>,
        answer: SatAnswer,
    },
    Witness {
        future: Pin<Box<dyn Future<Output = Option<AnyDomain>> + 'a>>,
        answer: WitnessAnswer,
    },
}

enum FrameStep {
    Completed,
    Pending,
}

fn execute<'a>(root: Frame<'a>, oracle: &DecisionOracle<'a>) {
    let mut frames = vec![root];
    let waker = Waker::noop();
    let mut context = Context::from_waker(waker);
    loop {
        let step = match frames
            .last_mut()
            .expect("decision executor lost its root frame")
        {
            Frame::Sat { future, answer } => match future.as_mut().poll(&mut context) {
                Poll::Ready(value) => {
                    answer.set(Some(value));
                    FrameStep::Completed
                },
                Poll::Pending => FrameStep::Pending,
            },
            Frame::Witness { future, answer } => match future.as_mut().poll(&mut context) {
                Poll::Ready(value) => {
                    *answer.borrow_mut() = Some(value);
                    FrameStep::Completed
                },
                Poll::Pending => FrameStep::Pending,
            },
        };
        match step {
            FrameStep::Completed => {
                frames.pop();
                if frames.is_empty() {
                    return;
                }
            },
            FrameStep::Pending => {
                let request = oracle
                    .pending
                    .borrow_mut()
                    .take()
                    .expect("decision future yielded without an algebra query");
                frames.push(match request {
                    Request::Sat { algebra, predicate, answer } => Frame::Sat {
                        future: Box::pin(decide_sat(oracle.clone(), algebra, predicate)),
                        answer,
                    },
                    Request::Witness { algebra, predicate, answer } => Frame::Witness {
                        future: Box::pin(decide_witness(oracle.clone(), algebra, predicate)),
                        answer,
                    },
                });
            },
        }
    }
}

pub(super) fn is_satisfiable(algebra: &AnyAlgebra, predicate: &AnyPred) -> bool {
    let oracle = DecisionOracle::new();
    let answer = Rc::new(Cell::new(None));
    let root = Frame::Sat {
        future: Box::pin(decide_sat(oracle.clone(), algebra, predicate.clone())),
        answer: Rc::clone(&answer),
    };
    execute(root, &oracle);
    answer.take().expect("SAT executor produced no root result")
}

pub(super) fn witness(algebra: &AnyAlgebra, predicate: &AnyPred) -> Option<AnyDomain> {
    let oracle = DecisionOracle::new();
    let answer = Rc::new(RefCell::new(None));
    let root = Frame::Witness {
        future: Box::pin(decide_witness(oracle.clone(), algebra, predicate.clone())),
        answer: Rc::clone(&answer),
    };
    execute(root, &oracle);
    let result = answer
        .borrow_mut()
        .take()
        .expect("witness executor produced no root result");
    result
}

fn fold_owned<A, F>(algebra: &A, predicate: AnyPred, leaf: F) -> A::Predicate
where
    A: BooleanAlgebra,
    F: Fn(AnyPredNode) -> Option<A::Predicate>,
{
    enum Task {
        Visit(AnyPred),
        And,
        Or,
        Not,
    }
    let mut tasks = vec![Task::Visit(predicate)];
    let mut values = Vec::new();
    while let Some(task) = tasks.pop() {
        match task {
            Task::Visit(predicate) => match predicate.into_node() {
                AnyPredNode::True => values.push(algebra.true_pred()),
                AnyPredNode::False => values.push(algebra.false_pred()),
                AnyPredNode::And(left, right) => {
                    tasks.push(Task::And);
                    tasks.push(Task::Visit(*right));
                    tasks.push(Task::Visit(*left));
                },
                AnyPredNode::Or(left, right) => {
                    tasks.push(Task::Or);
                    tasks.push(Task::Visit(*right));
                    tasks.push(Task::Visit(*left));
                },
                AnyPredNode::Not(body) => {
                    tasks.push(Task::Not);
                    tasks.push(Task::Visit(*body));
                },
                other => values.push(leaf(other).unwrap_or_else(|| algebra.false_pred())),
            },
            Task::And => {
                let right = values
                    .pop()
                    .expect("owned predicate fold lost right operand");
                let left = values
                    .pop()
                    .expect("owned predicate fold lost left operand");
                values.push(algebra.and(&left, &right));
            },
            Task::Or => {
                let right = values
                    .pop()
                    .expect("owned predicate fold lost right operand");
                let left = values
                    .pop()
                    .expect("owned predicate fold lost left operand");
                values.push(algebra.or(&left, &right));
            },
            Task::Not => {
                let body = values
                    .pop()
                    .expect("owned predicate fold lost negated operand");
                values.push(algebra.not(&body));
            },
        }
    }
    values
        .pop()
        .expect("owned predicate fold produced no value")
}

fn project_sum_all(
    algebra: &crate::product_nary::SumAlgebra<AnyAlgebra>,
    predicate: crate::product_nary::SumPred<AnyPred>,
) -> Vec<AnyPred> {
    use crate::product_nary::{SumNode, SumPred};
    enum Task {
        Visit(SumPred<AnyPred>),
        And,
        Or,
        Not,
    }
    let width = algebra.variants.len();
    let false_projection = || {
        (0..width)
            .map(|index| algebra.variants[index].false_pred())
            .collect()
    };
    let mut tasks = vec![Task::Visit(predicate)];
    let mut values: Vec<Vec<AnyPred>> = Vec::new();
    while let Some(task) = tasks.pop() {
        match task {
            Task::Visit(predicate) => match predicate.into_node() {
                SumNode::True => values.push(
                    (0..width)
                        .map(|index| algebra.variants[index].true_pred())
                        .collect(),
                ),
                SumNode::False => values.push(false_projection()),
                SumNode::InVariant(tag, predicate) => {
                    let mut projected = false_projection();
                    if tag < width {
                        projected[tag] = predicate;
                    }
                    values.push(projected);
                },
                SumNode::TagIs(tag) => values.push(
                    (0..width)
                        .map(|index| {
                            if index == tag {
                                algebra.variants[index].true_pred()
                            } else {
                                algebra.variants[index].false_pred()
                            }
                        })
                        .collect(),
                ),
                SumNode::And(left, right) => {
                    tasks.push(Task::And);
                    tasks.push(Task::Visit(*right));
                    tasks.push(Task::Visit(*left));
                },
                SumNode::Or(left, right) => {
                    tasks.push(Task::Or);
                    tasks.push(Task::Visit(*right));
                    tasks.push(Task::Visit(*left));
                },
                SumNode::Not(body) => {
                    tasks.push(Task::Not);
                    tasks.push(Task::Visit(*body));
                },
            },
            Task::And | Task::Or => {
                let conjunction = matches!(task, Task::And);
                let right = values.pop().expect("sum projection lost right operands");
                let left = values.pop().expect("sum projection lost left operands");
                values.push(
                    left.into_iter()
                        .zip(right)
                        .enumerate()
                        .map(|(index, (left, right))| {
                            if conjunction {
                                algebra.variants[index].and(&left, &right)
                            } else {
                                algebra.variants[index].or(&left, &right)
                            }
                        })
                        .collect(),
                );
            },
            Task::Not => {
                let body = values.pop().expect("sum projection lost negated operands");
                values.push(
                    body.into_iter()
                        .enumerate()
                        .map(|(index, predicate)| algebra.variants[index].not(&predicate))
                        .collect(),
                );
            },
        }
    }
    values.pop().expect("sum projection produced no values")
}

async fn decide_sat<'a>(
    oracle: DecisionOracle<'a>,
    algebra: &'a AnyAlgebra,
    predicate: AnyPred,
) -> bool {
    match algebra {
        AnyAlgebra::Int(inner) => {
            inner.is_satisfiable(&fold_owned(inner, predicate, |node| match node {
                AnyPredNode::Int(predicate) => Some(predicate),
                _ => None,
            }))
        },
        AnyAlgebra::Char(inner) => {
            inner.is_satisfiable(&fold_owned(inner, predicate, |node| match node {
                AnyPredNode::Char(predicate) => Some(predicate),
                _ => None,
            }))
        },
        AnyAlgebra::Bool(inner) => {
            inner.is_satisfiable(&fold_owned(inner, predicate, |node| match node {
                AnyPredNode::Bool(predicate) => Some(predicate),
                _ => None,
            }))
        },
        AnyAlgebra::BigInt(inner) => {
            inner.is_satisfiable(&fold_owned(inner, predicate, |node| match node {
                AnyPredNode::BigInt(predicate) => Some(predicate),
                _ => None,
            }))
        },
        AnyAlgebra::BigRat(inner) => {
            inner.is_satisfiable(&fold_owned(inner, predicate, |node| match node {
                AnyPredNode::BigRat(predicate) => Some(predicate),
                _ => None,
            }))
        },
        AnyAlgebra::Fixed(inner) => {
            inner.is_satisfiable(&fold_owned(inner, predicate, |node| match node {
                AnyPredNode::Fixed(predicate) => Some(predicate),
                _ => None,
            }))
        },
        AnyAlgebra::Float(inner) => {
            inner.is_satisfiable(&fold_owned(inner, predicate, |node| match node {
                AnyPredNode::Float(predicate) => Some(predicate),
                _ => None,
            }))
        },
        AnyAlgebra::Str(inner) => {
            inner.is_satisfiable(&fold_owned(inner, predicate, |node| match node {
                AnyPredNode::Str(predicate) => Some(predicate),
                _ => None,
            }))
        },
        AnyAlgebra::Product(inner) => {
            let projected = fold_owned(inner.as_ref(), predicate, |node| match node {
                AnyPredNode::Product(predicate) => Some(*predicate),
                _ => None,
            });
            for disjunct in inner.to_dnf_owned(projected) {
                let Some(constraints) = inner.field_constraints_owned(disjunct) else {
                    continue;
                };
                let mut satisfiable = true;
                for (index, constraint) in constraints.into_iter().enumerate() {
                    let query = constraint.unwrap_or_else(|| inner.fields[index].true_pred());
                    if !oracle.sat(&inner.fields[index], query).await {
                        satisfiable = false;
                        break;
                    }
                }
                if satisfiable {
                    return true;
                }
            }
            false
        },
        AnyAlgebra::Sum(inner) => {
            let projected = fold_owned(inner.as_ref(), predicate, |node| match node {
                AnyPredNode::Sum(predicate) => Some(*predicate),
                _ => None,
            });
            for (tag, predicate) in project_sum_all(inner, projected).into_iter().enumerate() {
                if oracle.sat(&inner.variants[tag], predicate).await {
                    return true;
                }
            }
            false
        },
        AnyAlgebra::List(inner) => {
            let projected = fold_owned(inner.as_ref(), predicate, |node| match node {
                AnyPredNode::List(predicate) => Some(*predicate),
                _ => None,
            });
            let automaton = super::sfa::compile(&oracle, &inner.elem, projected).await;
            !super::sfa::is_empty(&oracle, &inner.elem, automaton).await
        },
        AnyAlgebra::Bag(inner) => {
            let projected = fold_owned(inner.as_ref(), predicate, |node| match node {
                AnyPredNode::Bag(predicate) => Some(*predicate),
                _ => None,
            });
            decide_bag_sat(&oracle, inner, projected).await
        },
        AnyAlgebra::Tree(inner) => {
            let projected = fold_owned(inner.as_ref(), predicate, |node| match node {
                AnyPredNode::Tree(predicate) => Some(*predicate),
                _ => None,
            });
            let automaton = super::tree::compile(&oracle, inner, projected).await;
            !super::tree::is_empty(&oracle, &inner.elem, automaton).await
        },
        AnyAlgebra::Map(inner) => {
            let projected = fold_owned(inner.as_ref(), predicate, |node| match node {
                AnyPredNode::Map(predicate) => Some(*predicate),
                _ => None,
            });
            decide_map_sat(&oracle, inner, projected).await
        },
    }
}

async fn decide_witness<'a>(
    oracle: DecisionOracle<'a>,
    algebra: &'a AnyAlgebra,
    predicate: AnyPred,
) -> Option<AnyDomain> {
    match algebra {
        AnyAlgebra::Int(inner) => inner
            .witness(&fold_owned(inner, predicate, |node| match node {
                AnyPredNode::Int(predicate) => Some(predicate),
                _ => None,
            }))
            .map(AnyDomain::Int),
        AnyAlgebra::Char(inner) => inner
            .witness(&fold_owned(inner, predicate, |node| match node {
                AnyPredNode::Char(predicate) => Some(predicate),
                _ => None,
            }))
            .map(AnyDomain::Char),
        AnyAlgebra::Bool(inner) => inner
            .witness(&fold_owned(inner, predicate, |node| match node {
                AnyPredNode::Bool(predicate) => Some(predicate),
                _ => None,
            }))
            .map(AnyDomain::Bool),
        AnyAlgebra::BigInt(inner) => inner
            .witness(&fold_owned(inner, predicate, |node| match node {
                AnyPredNode::BigInt(predicate) => Some(predicate),
                _ => None,
            }))
            .map(AnyDomain::BigInt),
        AnyAlgebra::BigRat(inner) => inner
            .witness(&fold_owned(inner, predicate, |node| match node {
                AnyPredNode::BigRat(predicate) => Some(predicate),
                _ => None,
            }))
            .map(AnyDomain::BigRat),
        AnyAlgebra::Fixed(inner) => inner
            .witness(&fold_owned(inner, predicate, |node| match node {
                AnyPredNode::Fixed(predicate) => Some(predicate),
                _ => None,
            }))
            .map(AnyDomain::Fixed),
        AnyAlgebra::Float(inner) => inner
            .witness(&fold_owned(inner, predicate, |node| match node {
                AnyPredNode::Float(predicate) => Some(predicate),
                _ => None,
            }))
            .map(AnyDomain::Float),
        AnyAlgebra::Str(inner) => inner
            .witness(&fold_owned(inner, predicate, |node| match node {
                AnyPredNode::Str(predicate) => Some(predicate),
                _ => None,
            }))
            .map(AnyDomain::Str),
        AnyAlgebra::Product(inner) => {
            let projected = fold_owned(inner.as_ref(), predicate, |node| match node {
                AnyPredNode::Product(predicate) => Some(*predicate),
                _ => None,
            });
            for disjunct in inner.to_dnf_owned(projected) {
                let Some(constraints) = inner.field_constraints_owned(disjunct) else {
                    continue;
                };
                let mut tuple = Vec::with_capacity(inner.fields.len());
                let mut complete = true;
                for (index, constraint) in constraints.into_iter().enumerate() {
                    let query = constraint.unwrap_or_else(|| inner.fields[index].true_pred());
                    match oracle.witness(&inner.fields[index], query).await {
                        Some(value) => tuple.push(value),
                        None => {
                            complete = false;
                            break;
                        },
                    }
                }
                if complete {
                    return Some(AnyDomain::Product(tuple));
                }
            }
            None
        },
        AnyAlgebra::Sum(inner) => {
            let projected = fold_owned(inner.as_ref(), predicate, |node| match node {
                AnyPredNode::Sum(predicate) => Some(*predicate),
                _ => None,
            });
            for (tag, predicate) in project_sum_all(inner, projected).into_iter().enumerate() {
                if let Some(payload) = oracle.witness(&inner.variants[tag], predicate).await {
                    return Some(AnyDomain::Sum(Box::new(crate::product_nary::SumValue {
                        tag,
                        payload,
                    })));
                }
            }
            None
        },
        AnyAlgebra::List(inner) => {
            let projected = fold_owned(inner.as_ref(), predicate, |node| match node {
                AnyPredNode::List(predicate) => Some(*predicate),
                _ => None,
            });
            let automaton = super::sfa::compile(&oracle, &inner.elem, projected).await;
            super::sfa::shortest_accepted(&oracle, &inner.elem, automaton)
                .await
                .map(AnyDomain::List)
        },
        AnyAlgebra::Bag(inner) => {
            let projected = fold_owned(inner.as_ref(), predicate, |node| match node {
                AnyPredNode::Bag(predicate) => Some(*predicate),
                _ => None,
            });
            decide_bag_witness(&oracle, inner, projected)
                .await
                .map(AnyDomain::Bag)
        },
        AnyAlgebra::Tree(inner) => {
            let projected = fold_owned(inner.as_ref(), predicate, |node| match node {
                AnyPredNode::Tree(predicate) => Some(*predicate),
                _ => None,
            });
            let automaton = super::tree::compile(&oracle, inner, projected).await;
            super::tree::witness(&oracle, &inner.elem, automaton)
                .await
                .map(|value| AnyDomain::Tree(Box::new(value)))
        },
        AnyAlgebra::Map(inner) => {
            let projected = fold_owned(inner.as_ref(), predicate, |node| match node {
                AnyPredNode::Map(predicate) => Some(*predicate),
                _ => None,
            });
            decide_map_witness(&oracle, inner, projected)
                .await
                .map(AnyDomain::Map)
        },
    }
}

pub(super) struct Minterm {
    pub(super) predicate: AnyPred,
    pub(super) positive: Vec<bool>,
}

pub(super) async fn minterms<'a>(
    oracle: &DecisionOracle<'a>,
    algebra: &'a AnyAlgebra,
    predicates: &[AnyPred],
) -> Vec<Minterm> {
    let mut unique = Vec::new();
    for predicate in predicates {
        if !unique.iter().any(|candidate| candidate == predicate) {
            unique.push(predicate.clone());
        }
    }
    let mut regions = vec![Minterm {
        predicate: algebra.true_pred(),
        positive: Vec::new(),
    }];
    for predicate in &unique {
        let negated = algebra.not(predicate);
        let mut next = Vec::with_capacity(regions.len() * 2);
        for region in regions {
            let positive = algebra.and(&region.predicate, predicate);
            if oracle.sat(algebra, positive.clone()).await {
                let mut signs = region.positive.clone();
                signs.push(true);
                next.push(Minterm { predicate: positive, positive: signs });
            }
            let negative = algebra.and(&region.predicate, &negated);
            if oracle.sat(algebra, negative.clone()).await {
                let mut signs = region.positive;
                signs.push(false);
                next.push(Minterm { predicate: negative, positive: signs });
            }
        }
        regions = next;
    }
    regions
}

enum BagOp {
    True,
    False,
    Count { class: usize, lo: u64, hi: Option<u64> },
    And,
    Or,
    Not,
}

struct BagPlan {
    classes: Vec<AnyPred>,
    operations: Vec<BagOp>,
    cap: u64,
}

fn compile_bag(predicate: BagPred<AnyPred>) -> BagPlan {
    enum Task {
        Visit(BagPred<AnyPred>),
        And,
        Or,
        Not,
    }
    let mut tasks = vec![Task::Visit(predicate)];
    let mut classes = Vec::new();
    let mut operations = Vec::new();
    let mut maximum = 0;
    while let Some(task) = tasks.pop() {
        match task {
            Task::Visit(predicate) => match predicate.into_node() {
                BagNode::True => operations.push(BagOp::True),
                BagNode::False => operations.push(BagOp::False),
                BagNode::Count { class, lo, hi } => {
                    maximum = maximum.max(lo).max(hi.unwrap_or(0));
                    let class = if let Some(index) =
                        classes.iter().position(|candidate| candidate == &class)
                    {
                        index
                    } else {
                        let index = classes.len();
                        classes.push(class);
                        index
                    };
                    operations.push(BagOp::Count { class, lo, hi });
                },
                BagNode::And(left, right) => {
                    tasks.push(Task::And);
                    tasks.push(Task::Visit(*right));
                    tasks.push(Task::Visit(*left));
                },
                BagNode::Or(left, right) => {
                    tasks.push(Task::Or);
                    tasks.push(Task::Visit(*right));
                    tasks.push(Task::Visit(*left));
                },
                BagNode::Not(body) => {
                    tasks.push(Task::Not);
                    tasks.push(Task::Visit(*body));
                },
            },
            Task::And => operations.push(BagOp::And),
            Task::Or => operations.push(BagOp::Or),
            Task::Not => operations.push(BagOp::Not),
        }
    }
    BagPlan { classes, operations, cap: maximum + 1 }
}

fn eval_bag(plan: &BagPlan, counts: &[u64], cover: &[Vec<usize>]) -> bool {
    let mut values = Vec::new();
    for operation in &plan.operations {
        match operation {
            BagOp::True => values.push(true),
            BagOp::False => values.push(false),
            BagOp::Count { class, lo, hi } => {
                let count = cover[*class]
                    .iter()
                    .map(|index| counts[*index])
                    .sum::<u64>();
                values.push(count >= *lo && hi.is_none_or(|upper| count <= upper));
            },
            BagOp::And => {
                let right = values.pop().expect("bag plan lost right conjunction");
                let left = values.pop().expect("bag plan lost left conjunction");
                values.push(left && right);
            },
            BagOp::Or => {
                let right = values.pop().expect("bag plan lost right disjunction");
                let left = values.pop().expect("bag plan lost left disjunction");
                values.push(left || right);
            },
            BagOp::Not => {
                let value = values.pop().expect("bag plan lost negated value");
                values.push(!value);
            },
        }
    }
    values.pop().expect("bag plan produced no value")
}

async fn decide_bag_sat<'a>(
    oracle: &DecisionOracle<'a>,
    algebra: &'a BagAlgebra<AnyAlgebra>,
    predicate: BagPred<AnyPred>,
) -> bool {
    let plan = compile_bag(predicate);
    match plan.operations.as_slice() {
        [BagOp::True] => true,
        [BagOp::False] => false,
        [BagOp::Count { class, lo, hi }] => {
            let (class, lo, hi) = (*class, *lo, *hi);
            if hi.is_some_and(|upper| upper < lo) {
                return false;
            }
            if lo == 0 {
                return true;
            }
            let predicate = plan
                .classes
                .into_iter()
                .nth(class)
                .expect("bag plan references a missing class");
            oracle.sat(&algebra.elem, predicate).await
        },
        _ => feasible_bag_plan(oracle, algebra, plan).await.is_some(),
    }
}

async fn decide_bag_witness<'a>(
    oracle: &DecisionOracle<'a>,
    algebra: &'a BagAlgebra<AnyAlgebra>,
    predicate: BagPred<AnyPred>,
) -> Option<Vec<AnyDomain>> {
    let plan = compile_bag(predicate);
    match plan.operations.as_slice() {
        [BagOp::True] => Some(Vec::new()),
        [BagOp::False] => None,
        [BagOp::Count { class, lo, hi }] => {
            let (class, lo, hi) = (*class, *lo, *hi);
            if hi.is_some_and(|upper| upper < lo) {
                return None;
            }
            if lo == 0 {
                return Some(Vec::new());
            }
            let predicate = plan
                .classes
                .into_iter()
                .nth(class)
                .expect("bag plan references a missing class");
            let value = oracle.witness(&algebra.elem, predicate).await?;
            let count = usize::try_from(lo).ok()?;
            Some(std::iter::repeat_n(value, count).collect())
        },
        _ => {
            let (minterms, counts) = feasible_bag_plan(oracle, algebra, plan).await?;
            let mut bag = Vec::new();
            for (minterm, count) in minterms.into_iter().zip(counts) {
                if count == 0 {
                    continue;
                }
                let value = oracle.witness(&algebra.elem, minterm).await?;
                let count = usize::try_from(count).ok()?;
                bag.extend(std::iter::repeat_n(value, count));
            }
            Some(bag)
        },
    }
}

async fn feasible_bag_plan<'a>(
    oracle: &DecisionOracle<'a>,
    algebra: &'a BagAlgebra<AnyAlgebra>,
    plan: BagPlan,
) -> Option<(Vec<AnyPred>, Vec<u64>)> {
    let regions = minterms(oracle, &algebra.elem, &plan.classes).await;
    let cover: Vec<Vec<usize>> = (0..plan.classes.len())
        .map(|class| {
            regions
                .iter()
                .enumerate()
                .filter_map(|(index, region)| region.positive[class].then_some(index))
                .collect()
        })
        .collect();
    let minterms: Vec<AnyPred> = regions.into_iter().map(|region| region.predicate).collect();
    let mut counts = vec![0; minterms.len()];
    loop {
        if eval_bag(&plan, &counts, &cover) {
            return Some((minterms, counts));
        }
        let mut index = 0;
        loop {
            if index == counts.len() {
                return None;
            }
            if counts[index] < plan.cap {
                counts[index] += 1;
                break;
            }
            counts[index] = 0;
            index += 1;
        }
    }
}

struct FeasibleMap {
    value_minterms: Vec<AnyPred>,
    keys: Vec<Vec<AnyDomain>>,
    counts: Vec<u64>,
    columns: usize,
}

async fn distinct_keys<'a>(
    oracle: &DecisionOracle<'a>,
    algebra: &'a AnyAlgebra,
    minterm: AnyPred,
    cap: u64,
) -> Vec<AnyDomain> {
    let mut keys = Vec::new();
    let mut remaining = minterm;
    for _ in 0..cap {
        let Some(key) = oracle.witness(algebra, remaining.clone()).await else {
            break;
        };
        remaining = algebra.and(&remaining, &algebra.not(&algebra.point(&key)));
        keys.push(key);
    }
    keys
}

enum MapOp {
    True,
    False,
    Count {
        key_class: usize,
        value_class: usize,
        lo: u64,
        hi: Option<u64>,
    },
    And,
    Or,
    Not,
}

struct MapPlan {
    key_classes: Vec<AnyPred>,
    value_classes: Vec<AnyPred>,
    operations: Vec<MapOp>,
    cap: u64,
}

fn intern_predicate(classes: &mut Vec<AnyPred>, predicate: AnyPred) -> usize {
    if let Some(index) = classes.iter().position(|candidate| candidate == &predicate) {
        index
    } else {
        let index = classes.len();
        classes.push(predicate);
        index
    }
}

fn compile_map(predicate: MapPred<AnyPred, AnyPred>) -> MapPlan {
    enum Task {
        Visit(MapPred<AnyPred, AnyPred>),
        And,
        Or,
        Not,
    }

    let mut tasks = vec![Task::Visit(predicate)];
    let mut key_classes = Vec::new();
    let mut value_classes = Vec::new();
    let mut operations = Vec::new();
    let mut maximum = 0;
    while let Some(task) = tasks.pop() {
        match task {
            Task::Visit(predicate) => match predicate.into_node() {
                MapNode::True => operations.push(MapOp::True),
                MapNode::False => operations.push(MapOp::False),
                MapNode::CountEntries { key_class, val_class, lo, hi } => {
                    maximum = maximum.max(lo).max(hi.unwrap_or(0));
                    let key_class = intern_predicate(&mut key_classes, key_class);
                    let value_class = intern_predicate(&mut value_classes, val_class);
                    operations.push(MapOp::Count { key_class, value_class, lo, hi });
                },
                MapNode::And(left, right) => {
                    tasks.push(Task::And);
                    tasks.push(Task::Visit(*right));
                    tasks.push(Task::Visit(*left));
                },
                MapNode::Or(left, right) => {
                    tasks.push(Task::Or);
                    tasks.push(Task::Visit(*right));
                    tasks.push(Task::Visit(*left));
                },
                MapNode::Not(body) => {
                    tasks.push(Task::Not);
                    tasks.push(Task::Visit(*body));
                },
            },
            Task::And => operations.push(MapOp::And),
            Task::Or => operations.push(MapOp::Or),
            Task::Not => operations.push(MapOp::Not),
        }
    }
    MapPlan {
        key_classes,
        value_classes,
        operations,
        cap: maximum + 1,
    }
}

fn eval_map_counts(
    plan: &MapPlan,
    counts: &[u64],
    columns: usize,
    key_cover: &[Vec<usize>],
    value_cover: &[Vec<usize>],
) -> bool {
    let mut values = Vec::new();
    for operation in &plan.operations {
        match operation {
            MapOp::True => values.push(true),
            MapOp::False => values.push(false),
            MapOp::Count { key_class, value_class, lo, hi } => {
                let mut count = 0;
                for &key_index in &key_cover[*key_class] {
                    for &value_index in &value_cover[*value_class] {
                        count += counts[key_index * columns + value_index];
                    }
                }
                values.push(count >= *lo && hi.is_none_or(|upper| count <= upper));
            },
            MapOp::And => {
                let right = values.pop().expect("map plan lost right conjunction");
                let left = values.pop().expect("map plan lost left conjunction");
                values.push(left && right);
            },
            MapOp::Or => {
                let right = values.pop().expect("map plan lost right disjunction");
                let left = values.pop().expect("map plan lost left disjunction");
                values.push(left || right);
            },
            MapOp::Not => {
                let value = values.pop().expect("map feasibility lost negated value");
                values.push(!value);
            },
        }
    }
    values.pop().expect("map feasibility produced no value")
}

async fn decide_map_sat<'a>(
    oracle: &DecisionOracle<'a>,
    algebra: &'a MapAlgebra<AnyAlgebra, AnyAlgebra>,
    predicate: MapPred<AnyPred, AnyPred>,
) -> bool {
    let plan = compile_map(predicate);
    match plan.operations.as_slice() {
        [MapOp::True] => true,
        [MapOp::False] => false,
        [MapOp::Count { key_class, value_class, lo, hi }] => {
            let (key_class, value_class, lo, hi) = (*key_class, *value_class, *lo, *hi);
            if hi.is_some_and(|upper| upper < lo) {
                return false;
            }
            if lo == 0 {
                return true;
            }
            let value_predicate = plan
                .value_classes
                .into_iter()
                .nth(value_class)
                .expect("map plan references a missing value class");
            if !oracle.sat(&algebra.val, value_predicate).await {
                return false;
            }
            let key_predicate = plan
                .key_classes
                .into_iter()
                .nth(key_class)
                .expect("map plan references a missing key class");
            distinct_keys(oracle, &algebra.key, key_predicate, lo)
                .await
                .len()
                == usize::try_from(lo).unwrap_or(usize::MAX)
        },
        _ => feasible_map_plan(oracle, algebra, plan).await.is_some(),
    }
}

async fn decide_map_witness<'a>(
    oracle: &DecisionOracle<'a>,
    algebra: &'a MapAlgebra<AnyAlgebra, AnyAlgebra>,
    predicate: MapPred<AnyPred, AnyPred>,
) -> Option<Vec<(AnyDomain, AnyDomain)>> {
    let plan = compile_map(predicate);
    match plan.operations.as_slice() {
        [MapOp::True] => Some(Vec::new()),
        [MapOp::False] => None,
        [MapOp::Count { key_class, value_class, lo, hi }] => {
            let (key_class, value_class, lo, hi) = (*key_class, *value_class, *lo, *hi);
            if hi.is_some_and(|upper| upper < lo) {
                return None;
            }
            if lo == 0 {
                return Some(Vec::new());
            }
            let value_predicate = plan
                .value_classes
                .into_iter()
                .nth(value_class)
                .expect("map plan references a missing value class");
            let value = oracle.witness(&algebra.val, value_predicate).await?;
            let key_predicate = plan
                .key_classes
                .into_iter()
                .nth(key_class)
                .expect("map plan references a missing key class");
            let keys = distinct_keys(oracle, &algebra.key, key_predicate, lo).await;
            if keys.len() != usize::try_from(lo).ok()? {
                return None;
            }
            let mut keys = keys.into_iter().peekable();
            let mut value = Some(value);
            let mut map = Vec::with_capacity(keys.len());
            while let Some(key) = keys.next() {
                let entry_value = if keys.peek().is_some() {
                    value
                        .as_ref()
                        .expect("map witness lost its shared value")
                        .clone()
                } else {
                    value.take().expect("map witness lost its final value")
                };
                map.push((key, entry_value));
            }
            Some(map)
        },
        _ => {
            let feasible = feasible_map_plan(oracle, algebra, plan).await?;
            materialize_map(oracle, algebra, feasible).await
        },
    }
}

async fn feasible_map_plan<'a>(
    oracle: &DecisionOracle<'a>,
    algebra: &'a MapAlgebra<AnyAlgebra, AnyAlgebra>,
    mut plan: MapPlan,
) -> Option<FeasibleMap> {
    let key_regions = minterms(oracle, &algebra.key, &plan.key_classes).await;
    let value_regions = minterms(oracle, &algebra.val, &plan.value_classes).await;
    let key_cover: Vec<Vec<usize>> = (0..plan.key_classes.len())
        .map(|class_index| {
            key_regions
                .iter()
                .enumerate()
                .filter_map(|(index, region)| region.positive[class_index].then_some(index))
                .collect()
        })
        .collect();
    let value_cover: Vec<Vec<usize>> = (0..plan.value_classes.len())
        .map(|class_index| {
            value_regions
                .iter()
                .enumerate()
                .filter_map(|(index, region)| region.positive[class_index].then_some(index))
                .collect()
        })
        .collect();
    plan.key_classes.clear();
    plan.value_classes.clear();
    let key_minterms: Vec<AnyPred> = key_regions
        .into_iter()
        .map(|region| region.predicate)
        .collect();
    let value_minterms: Vec<AnyPred> = value_regions
        .into_iter()
        .map(|region| region.predicate)
        .collect();
    let mut keys = Vec::with_capacity(key_minterms.len());
    for minterm in key_minterms {
        keys.push(distinct_keys(oracle, &algebra.key, minterm, plan.cap).await);
    }
    let rows = keys.len();
    let columns = value_minterms.len();
    let cells = rows
        .checked_mul(columns)
        .expect("map feasibility matrix exceeds addressable memory");
    let mut flat = vec![0; cells];
    loop {
        let available = (0..rows).all(|row| {
            flat[row * columns..(row + 1) * columns].iter().sum::<u64>() <= keys[row].len() as u64
        });
        if available && eval_map_counts(&plan, &flat, columns, &key_cover, &value_cover) {
            return Some(FeasibleMap {
                value_minterms,
                keys,
                counts: flat,
                columns,
            });
        }
        let mut index = 0;
        loop {
            if index == flat.len() {
                return None;
            }
            if flat[index] < plan.cap {
                flat[index] += 1;
                break;
            }
            flat[index] = 0;
            index += 1;
        }
    }
}

async fn materialize_map<'a>(
    oracle: &DecisionOracle<'a>,
    algebra: &'a MapAlgebra<AnyAlgebra, AnyAlgebra>,
    mut feasible: FeasibleMap,
) -> Option<Vec<(AnyDomain, AnyDomain)>> {
    let mut map = Vec::new();
    let mut values = Vec::with_capacity(feasible.columns);
    for (column, predicate) in feasible.value_minterms.into_iter().enumerate() {
        let used = (0..feasible.keys.len())
            .any(|row| feasible.counts[row * feasible.columns + column] != 0);
        values.push(if used {
            Some(oracle.witness(&algebra.val, predicate).await?)
        } else {
            None
        });
    }
    for row in 0..feasible.keys.len() {
        let mut keys = feasible.keys[row].drain(..);
        for (column, value) in values.iter().enumerate() {
            for _ in 0..feasible.counts[row * feasible.columns + column] {
                let key = keys.next()?;
                map.push((key, value.as_ref()?.clone()));
            }
        }
    }
    Some(map)
}
