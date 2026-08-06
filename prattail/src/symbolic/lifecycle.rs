//! Heap-backed lifecycle machines for symbolic predicate models.

use super::{BooleanAlgebra, CharClassPred, IntervalPred, PredicateExpr, ProductPred};
use std::fmt;
use std::hash::{Hash, Hasher};

macro_rules! impl_range_pred_lifecycle {
    ($name:ident) => {
        impl Clone for $name {
            fn clone(&self) -> Self {
                enum Task<'pred> {
                    Visit(&'pred $name),
                    Not,
                }

                let mut tasks = vec![Task::Visit(self)];
                let mut values = Vec::new();
                while let Some(task) = tasks.pop() {
                    match task {
                        Task::Visit($name::True) => values.push($name::True),
                        Task::Visit($name::False) => values.push($name::False),
                        Task::Visit($name::Range(lower, upper)) => {
                            values.push($name::Range(*lower, *upper));
                        },
                        Task::Visit($name::Union(ranges)) => {
                            values.push($name::Union(ranges.clone()));
                        },
                        Task::Visit($name::Not(body)) => {
                            tasks.push(Task::Not);
                            tasks.push(Task::Visit(body));
                        },
                        Task::Not => {
                            let body = values
                                .pop()
                                .expect(concat!(stringify!($name), " clone lost not body"));
                            values.push($name::Not(Box::new(body)));
                        },
                    }
                }
                debug_assert_eq!(values.len(), 1);
                values
                    .pop()
                    .expect(concat!(stringify!($name), " clone produced no value"))
            }
        }

        impl PartialEq for $name {
            fn eq(&self, other: &Self) -> bool {
                let mut left = self;
                let mut right = other;
                loop {
                    match (left, right) {
                        ($name::True, $name::True) | ($name::False, $name::False) => return true,
                        ($name::Range(al, au), $name::Range(bl, bu)) => {
                            return al == bl && au == bu;
                        },
                        ($name::Union(a), $name::Union(b)) => return a == b,
                        ($name::Not(a), $name::Not(b)) => {
                            left = a;
                            right = b;
                        },
                        _ => return false,
                    }
                }
            }
        }

        impl Eq for $name {}

        impl Hash for $name {
            fn hash<H: Hasher>(&self, state: &mut H) {
                let mut cursor = self;
                loop {
                    std::mem::discriminant(cursor).hash(state);
                    match cursor {
                        $name::True | $name::False => return,
                        $name::Range(lower, upper) => {
                            lower.hash(state);
                            upper.hash(state);
                            return;
                        },
                        $name::Union(ranges) => {
                            ranges.hash(state);
                            return;
                        },
                        $name::Not(body) => cursor = body,
                    }
                }
            }
        }

        impl fmt::Debug for $name {
            fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
                let mut cursor = self;
                let mut closing = 0usize;
                loop {
                    match cursor {
                        $name::True => {
                            formatter.write_str("True")?;
                            break;
                        },
                        $name::False => {
                            formatter.write_str("False")?;
                            break;
                        },
                        $name::Range(lower, upper) => {
                            write!(formatter, "Range({lower:?}, {upper:?})")?;
                            break;
                        },
                        $name::Union(ranges) => {
                            write!(formatter, "Union({ranges:?})")?;
                            break;
                        },
                        $name::Not(body) => {
                            formatter.write_str("Not(")?;
                            closing += 1;
                            cursor = body;
                        },
                    }
                }
                for _ in 0..closing {
                    formatter.write_str(")")?;
                }
                Ok(())
            }
        }
    };
}

impl_range_pred_lifecycle!(IntervalPred);
impl_range_pred_lifecycle!(CharClassPred);

macro_rules! drain_range_pred_drop {
    ($this:ident, $name:ident) => {{
        let mut work = Vec::new();
        if let $name::Not(body) = $this {
            work.push(*std::mem::replace(body, Box::new($name::True)));
        }
        while let Some(mut predicate) = work.pop() {
            if let $name::Not(body) = &mut predicate {
                work.push(*std::mem::replace(body, Box::new($name::True)));
            }
        }
    }};
}

// These impl blocks remain explicit so the source-derived recursion census can
// verify that implicit recursive destruction has not returned. The shared body
// keeps the two isomorphic lifecycle machines in lockstep.
impl Drop for IntervalPred {
    fn drop(&mut self) {
        drain_range_pred_drop!(self, IntervalPred);
    }
}

impl Drop for CharClassPred {
    fn drop(&mut self) {
        drain_range_pred_drop!(self, CharClassPred);
    }
}

#[derive(Clone, Copy)]
enum PredicateUnaryKind {
    Not,
    ForallFinite,
    ExistsFinite,
    ForallInfinite,
    ExistsInfinite,
    Bounded,
}

#[derive(Clone, Copy)]
enum PredicateBinaryKind {
    And,
    Or,
}

enum PredicateCloneTask<'expr> {
    Visit(&'expr PredicateExpr),
    Unary {
        kind: PredicateUnaryKind,
        var: Option<&'expr str>,
        domain: Option<&'expr [String]>,
        bound: u64,
    },
    Binary(PredicateBinaryKind),
}

impl Clone for PredicateExpr {
    fn clone(&self) -> Self {
        let mut tasks = vec![PredicateCloneTask::Visit(self)];
        let mut values = Vec::new();
        while let Some(task) = tasks.pop() {
            match task {
                PredicateCloneTask::Visit(PredicateExpr::True) => {
                    values.push(PredicateExpr::True);
                },
                PredicateCloneTask::Visit(PredicateExpr::False) => {
                    values.push(PredicateExpr::False);
                },
                PredicateCloneTask::Visit(PredicateExpr::Atom(name)) => {
                    values.push(PredicateExpr::Atom(name.clone()));
                },
                PredicateCloneTask::Visit(PredicateExpr::Relation { name, args }) => {
                    values.push(PredicateExpr::Relation { name: name.clone(), args: args.clone() });
                },
                PredicateCloneTask::Visit(PredicateExpr::Not(body)) => {
                    push_predicate_unary(&mut tasks, PredicateUnaryKind::Not, None, None, 0, body);
                },
                PredicateCloneTask::Visit(PredicateExpr::ForallFinite { var, domain, body }) => {
                    push_predicate_unary(
                        &mut tasks,
                        PredicateUnaryKind::ForallFinite,
                        Some(var),
                        Some(domain),
                        0,
                        body,
                    );
                },
                PredicateCloneTask::Visit(PredicateExpr::ExistsFinite { var, domain, body }) => {
                    push_predicate_unary(
                        &mut tasks,
                        PredicateUnaryKind::ExistsFinite,
                        Some(var),
                        Some(domain),
                        0,
                        body,
                    );
                },
                PredicateCloneTask::Visit(PredicateExpr::ForallInfinite { var, body }) => {
                    push_predicate_unary(
                        &mut tasks,
                        PredicateUnaryKind::ForallInfinite,
                        Some(var),
                        None,
                        0,
                        body,
                    );
                },
                PredicateCloneTask::Visit(PredicateExpr::ExistsInfinite { var, body }) => {
                    push_predicate_unary(
                        &mut tasks,
                        PredicateUnaryKind::ExistsInfinite,
                        Some(var),
                        None,
                        0,
                        body,
                    );
                },
                PredicateCloneTask::Visit(PredicateExpr::Bounded { body, bound }) => {
                    push_predicate_unary(
                        &mut tasks,
                        PredicateUnaryKind::Bounded,
                        None,
                        None,
                        *bound,
                        body,
                    );
                },
                PredicateCloneTask::Visit(PredicateExpr::And(left, right)) => {
                    push_predicate_binary(&mut tasks, PredicateBinaryKind::And, left, right);
                },
                PredicateCloneTask::Visit(PredicateExpr::Or(left, right)) => {
                    push_predicate_binary(&mut tasks, PredicateBinaryKind::Or, left, right);
                },
                PredicateCloneTask::Unary { kind, var, domain, bound } => {
                    let body = Box::new(values.pop().expect("PredicateExpr clone lost unary body"));
                    let var = || {
                        var.expect("PredicateExpr clone lost quantifier variable")
                            .to_string()
                    };
                    let domain = || {
                        domain
                            .expect("PredicateExpr clone lost finite domain")
                            .to_vec()
                    };
                    values.push(match kind {
                        PredicateUnaryKind::Not => PredicateExpr::Not(body),
                        PredicateUnaryKind::ForallFinite => {
                            PredicateExpr::ForallFinite { var: var(), domain: domain(), body }
                        },
                        PredicateUnaryKind::ExistsFinite => {
                            PredicateExpr::ExistsFinite { var: var(), domain: domain(), body }
                        },
                        PredicateUnaryKind::ForallInfinite => {
                            PredicateExpr::ForallInfinite { var: var(), body }
                        },
                        PredicateUnaryKind::ExistsInfinite => {
                            PredicateExpr::ExistsInfinite { var: var(), body }
                        },
                        PredicateUnaryKind::Bounded => PredicateExpr::Bounded { body, bound },
                    });
                },
                PredicateCloneTask::Binary(kind) => {
                    let right =
                        Box::new(values.pop().expect("PredicateExpr clone lost right body"));
                    let left = Box::new(values.pop().expect("PredicateExpr clone lost left body"));
                    values.push(match kind {
                        PredicateBinaryKind::And => PredicateExpr::And(left, right),
                        PredicateBinaryKind::Or => PredicateExpr::Or(left, right),
                    });
                },
            }
        }
        debug_assert_eq!(values.len(), 1);
        values.pop().expect("PredicateExpr clone produced no value")
    }
}

fn push_predicate_unary<'expr>(
    tasks: &mut Vec<PredicateCloneTask<'expr>>,
    kind: PredicateUnaryKind,
    var: Option<&'expr str>,
    domain: Option<&'expr [String]>,
    bound: u64,
    body: &'expr PredicateExpr,
) {
    tasks.push(PredicateCloneTask::Unary { kind, var, domain, bound });
    tasks.push(PredicateCloneTask::Visit(body));
}

fn push_predicate_binary<'expr>(
    tasks: &mut Vec<PredicateCloneTask<'expr>>,
    kind: PredicateBinaryKind,
    left: &'expr PredicateExpr,
    right: &'expr PredicateExpr,
) {
    tasks.push(PredicateCloneTask::Binary(kind));
    tasks.push(PredicateCloneTask::Visit(right));
    tasks.push(PredicateCloneTask::Visit(left));
}

impl PartialEq for PredicateExpr {
    fn eq(&self, other: &Self) -> bool {
        let mut work = vec![(self, other)];
        while let Some((left, right)) = work.pop() {
            match (left, right) {
                (PredicateExpr::True, PredicateExpr::True)
                | (PredicateExpr::False, PredicateExpr::False) => {},
                (PredicateExpr::Atom(a), PredicateExpr::Atom(b)) if a == b => {},
                (
                    PredicateExpr::Relation { name: an, args: aa },
                    PredicateExpr::Relation { name: bn, args: ba },
                ) if an == bn && aa == ba => {},
                (PredicateExpr::Not(a), PredicateExpr::Not(b)) => work.push((a, b)),
                (PredicateExpr::And(al, ar), PredicateExpr::And(bl, br))
                | (PredicateExpr::Or(al, ar), PredicateExpr::Or(bl, br)) => {
                    work.push((ar, br));
                    work.push((al, bl));
                },
                (
                    PredicateExpr::ForallFinite { var: av, domain: ad, body: ab },
                    PredicateExpr::ForallFinite { var: bv, domain: bd, body: bb },
                )
                | (
                    PredicateExpr::ExistsFinite { var: av, domain: ad, body: ab },
                    PredicateExpr::ExistsFinite { var: bv, domain: bd, body: bb },
                ) if av == bv && ad == bd => work.push((ab, bb)),
                (
                    PredicateExpr::ForallInfinite { var: av, body: ab },
                    PredicateExpr::ForallInfinite { var: bv, body: bb },
                )
                | (
                    PredicateExpr::ExistsInfinite { var: av, body: ab },
                    PredicateExpr::ExistsInfinite { var: bv, body: bb },
                ) if av == bv => work.push((ab, bb)),
                (
                    PredicateExpr::Bounded { body: ab, bound: an },
                    PredicateExpr::Bounded { body: bb, bound: bn },
                ) if an == bn => work.push((ab, bb)),
                _ => return false,
            }
        }
        true
    }
}

impl Eq for PredicateExpr {}

impl Hash for PredicateExpr {
    fn hash<H: Hasher>(&self, state: &mut H) {
        enum Task<'expr> {
            Visit(&'expr PredicateExpr),
            Bound(u64),
        }

        let mut work = vec![Task::Visit(self)];
        while let Some(task) = work.pop() {
            let expr = match task {
                Task::Visit(expr) => expr,
                Task::Bound(bound) => {
                    bound.hash(state);
                    continue;
                },
            };
            std::mem::discriminant(expr).hash(state);
            match expr {
                PredicateExpr::True | PredicateExpr::False => {},
                PredicateExpr::Atom(name) => name.hash(state),
                PredicateExpr::Relation { name, args } => {
                    name.hash(state);
                    args.hash(state);
                },
                PredicateExpr::Not(body) => work.push(Task::Visit(body)),
                PredicateExpr::And(left, right) | PredicateExpr::Or(left, right) => {
                    work.push(Task::Visit(right));
                    work.push(Task::Visit(left));
                },
                PredicateExpr::ForallFinite { var, domain, body }
                | PredicateExpr::ExistsFinite { var, domain, body } => {
                    var.hash(state);
                    domain.hash(state);
                    work.push(Task::Visit(body));
                },
                PredicateExpr::ForallInfinite { var, body }
                | PredicateExpr::ExistsInfinite { var, body } => {
                    var.hash(state);
                    work.push(Task::Visit(body));
                },
                PredicateExpr::Bounded { body, bound } => {
                    work.push(Task::Bound(*bound));
                    work.push(Task::Visit(body));
                },
            }
        }
    }
}

fn take_predicate_children(expr: &mut PredicateExpr, work: &mut Vec<PredicateExpr>) {
    let take =
        |child: &mut Box<PredicateExpr>| *std::mem::replace(child, Box::new(PredicateExpr::True));
    match expr {
        PredicateExpr::Not(body)
        | PredicateExpr::ForallFinite { body, .. }
        | PredicateExpr::ExistsFinite { body, .. }
        | PredicateExpr::ForallInfinite { body, .. }
        | PredicateExpr::ExistsInfinite { body, .. }
        | PredicateExpr::Bounded { body, .. } => work.push(take(body)),
        PredicateExpr::And(left, right) | PredicateExpr::Or(left, right) => {
            work.push(take(left));
            work.push(take(right));
        },
        PredicateExpr::True
        | PredicateExpr::False
        | PredicateExpr::Atom(_)
        | PredicateExpr::Relation { .. } => {},
    }
}

impl Drop for PredicateExpr {
    fn drop(&mut self) {
        let mut work = Vec::new();
        take_predicate_children(self, &mut work);
        while let Some(mut expr) = work.pop() {
            take_predicate_children(&mut expr, &mut work);
        }
    }
}

enum PredicateDebugTask<'expr> {
    Visit(&'expr PredicateExpr),
    Text(&'static str),
    Bound(u64),
}

impl fmt::Debug for PredicateExpr {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut tasks = vec![PredicateDebugTask::Visit(self)];
        while let Some(task) = tasks.pop() {
            match task {
                PredicateDebugTask::Text(text) => formatter.write_str(text)?,
                PredicateDebugTask::Bound(bound) => {
                    write!(formatter, ", bound: {bound:?} }}")?;
                },
                PredicateDebugTask::Visit(PredicateExpr::True) => formatter.write_str("True")?,
                PredicateDebugTask::Visit(PredicateExpr::False) => formatter.write_str("False")?,
                PredicateDebugTask::Visit(PredicateExpr::Atom(name)) => {
                    write!(formatter, "Atom({name:?})")?;
                },
                PredicateDebugTask::Visit(PredicateExpr::Relation { name, args }) => {
                    write!(formatter, "Relation {{ name: {name:?}, args: {args:?} }}")?;
                },
                PredicateDebugTask::Visit(PredicateExpr::Not(body)) => {
                    push_predicate_debug_unary(&mut tasks, "Not(", ")", body);
                },
                PredicateDebugTask::Visit(PredicateExpr::And(left, right)) => {
                    push_predicate_debug_binary(&mut tasks, "And(", left, right);
                },
                PredicateDebugTask::Visit(PredicateExpr::Or(left, right)) => {
                    push_predicate_debug_binary(&mut tasks, "Or(", left, right);
                },
                PredicateDebugTask::Visit(PredicateExpr::ForallFinite { var, domain, body }) => {
                    tasks.push(PredicateDebugTask::Text(" }"));
                    tasks.push(PredicateDebugTask::Visit(body));
                    write!(formatter, "ForallFinite {{ var: {var:?}, domain: {domain:?}, body: ")?;
                },
                PredicateDebugTask::Visit(PredicateExpr::ExistsFinite { var, domain, body }) => {
                    tasks.push(PredicateDebugTask::Text(" }"));
                    tasks.push(PredicateDebugTask::Visit(body));
                    write!(formatter, "ExistsFinite {{ var: {var:?}, domain: {domain:?}, body: ")?;
                },
                PredicateDebugTask::Visit(PredicateExpr::ForallInfinite { var, body }) => {
                    tasks.push(PredicateDebugTask::Text(" }"));
                    tasks.push(PredicateDebugTask::Visit(body));
                    write!(formatter, "ForallInfinite {{ var: {var:?}, body: ")?;
                },
                PredicateDebugTask::Visit(PredicateExpr::ExistsInfinite { var, body }) => {
                    tasks.push(PredicateDebugTask::Text(" }"));
                    tasks.push(PredicateDebugTask::Visit(body));
                    write!(formatter, "ExistsInfinite {{ var: {var:?}, body: ")?;
                },
                PredicateDebugTask::Visit(PredicateExpr::Bounded { body, bound }) => {
                    tasks.push(PredicateDebugTask::Bound(*bound));
                    tasks.push(PredicateDebugTask::Visit(body));
                    write!(formatter, "Bounded {{ body: ")?;
                },
            }
        }
        Ok(())
    }
}

fn push_predicate_debug_unary<'expr>(
    tasks: &mut Vec<PredicateDebugTask<'expr>>,
    prefix: &'static str,
    suffix: &'static str,
    body: &'expr PredicateExpr,
) {
    tasks.push(PredicateDebugTask::Text(suffix));
    tasks.push(PredicateDebugTask::Visit(body));
    tasks.push(PredicateDebugTask::Text(prefix));
}

fn push_predicate_debug_binary<'expr>(
    tasks: &mut Vec<PredicateDebugTask<'expr>>,
    prefix: &'static str,
    left: &'expr PredicateExpr,
    right: &'expr PredicateExpr,
) {
    tasks.push(PredicateDebugTask::Text(")"));
    tasks.push(PredicateDebugTask::Visit(right));
    tasks.push(PredicateDebugTask::Text(", "));
    tasks.push(PredicateDebugTask::Visit(left));
    tasks.push(PredicateDebugTask::Text(prefix));
}

#[derive(Clone, Copy)]
enum ProductBinaryKind {
    And,
    Or,
}

enum ProductCloneTask<'pred, A: BooleanAlgebra, B: BooleanAlgebra> {
    Visit(&'pred ProductPred<A, B>),
    Binary(ProductBinaryKind),
    Not,
}

impl<A: BooleanAlgebra, B: BooleanAlgebra> Clone for ProductPred<A, B> {
    fn clone(&self) -> Self {
        let mut tasks = vec![ProductCloneTask::Visit(self)];
        let mut values = Vec::new();
        while let Some(task) = tasks.pop() {
            match task {
                ProductCloneTask::Visit(ProductPred::True) => values.push(ProductPred::True),
                ProductCloneTask::Visit(ProductPred::False) => values.push(ProductPred::False),
                ProductCloneTask::Visit(ProductPred::Both(left, right)) => {
                    values.push(ProductPred::Both(left.clone(), right.clone()));
                },
                ProductCloneTask::Visit(ProductPred::LeftOnly(left)) => {
                    values.push(ProductPred::LeftOnly(left.clone()));
                },
                ProductCloneTask::Visit(ProductPred::RightOnly(right)) => {
                    values.push(ProductPred::RightOnly(right.clone()));
                },
                ProductCloneTask::Visit(ProductPred::Not(body)) => {
                    tasks.push(ProductCloneTask::Not);
                    tasks.push(ProductCloneTask::Visit(body));
                },
                ProductCloneTask::Visit(ProductPred::And(left, right)) => {
                    push_product_clone_binary(&mut tasks, ProductBinaryKind::And, left, right);
                },
                ProductCloneTask::Visit(ProductPred::Or(left, right)) => {
                    push_product_clone_binary(&mut tasks, ProductBinaryKind::Or, left, right);
                },
                ProductCloneTask::Not => {
                    let body = values.pop().expect("ProductPred clone lost negated body");
                    values.push(ProductPred::Not(Box::new(body)));
                },
                ProductCloneTask::Binary(kind) => {
                    let right = values.pop().expect("ProductPred clone lost right body");
                    let left = values.pop().expect("ProductPred clone lost left body");
                    values.push(match kind {
                        ProductBinaryKind::And => ProductPred::And(Box::new(left), Box::new(right)),
                        ProductBinaryKind::Or => ProductPred::Or(Box::new(left), Box::new(right)),
                    });
                },
            }
        }
        debug_assert_eq!(values.len(), 1);
        values.pop().expect("ProductPred clone produced no value")
    }
}

fn push_product_clone_binary<'pred, A: BooleanAlgebra, B: BooleanAlgebra>(
    tasks: &mut Vec<ProductCloneTask<'pred, A, B>>,
    kind: ProductBinaryKind,
    left: &'pred ProductPred<A, B>,
    right: &'pred ProductPred<A, B>,
) {
    tasks.push(ProductCloneTask::Binary(kind));
    tasks.push(ProductCloneTask::Visit(right));
    tasks.push(ProductCloneTask::Visit(left));
}

impl<A: BooleanAlgebra, B: BooleanAlgebra> PartialEq for ProductPred<A, B> {
    fn eq(&self, other: &Self) -> bool {
        let mut work = vec![(self, other)];
        while let Some((left, right)) = work.pop() {
            match (left, right) {
                (ProductPred::True, ProductPred::True)
                | (ProductPred::False, ProductPred::False) => {},
                (ProductPred::Both(al, ar), ProductPred::Both(bl, br)) if al == bl && ar == br => {
                },
                (ProductPred::LeftOnly(a), ProductPred::LeftOnly(b)) if a == b => {},
                (ProductPred::RightOnly(a), ProductPred::RightOnly(b)) if a == b => {},
                (ProductPred::Not(a), ProductPred::Not(b)) => work.push((a, b)),
                (ProductPred::And(al, ar), ProductPred::And(bl, br))
                | (ProductPred::Or(al, ar), ProductPred::Or(bl, br)) => {
                    work.push((ar, br));
                    work.push((al, bl));
                },
                _ => return false,
            }
        }
        true
    }
}

impl<A: BooleanAlgebra, B: BooleanAlgebra> Eq for ProductPred<A, B> {}

impl<A: BooleanAlgebra, B: BooleanAlgebra> Hash for ProductPred<A, B> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        let mut work = vec![self];
        while let Some(predicate) = work.pop() {
            std::mem::discriminant(predicate).hash(state);
            match predicate {
                ProductPred::True | ProductPred::False => {},
                ProductPred::Both(left, right) => {
                    left.hash(state);
                    right.hash(state);
                },
                ProductPred::LeftOnly(left) => left.hash(state),
                ProductPred::RightOnly(right) => right.hash(state),
                ProductPred::Not(body) => work.push(body),
                ProductPred::And(left, right) | ProductPred::Or(left, right) => {
                    work.push(right);
                    work.push(left);
                },
            }
        }
    }
}

fn take_product_children<A: BooleanAlgebra, B: BooleanAlgebra>(
    predicate: &mut ProductPred<A, B>,
    work: &mut Vec<ProductPred<A, B>>,
) {
    let take =
        |child: &mut Box<ProductPred<A, B>>| *std::mem::replace(child, Box::new(ProductPred::True));
    match predicate {
        ProductPred::Not(body) => work.push(take(body)),
        ProductPred::And(left, right) | ProductPred::Or(left, right) => {
            work.push(take(left));
            work.push(take(right));
        },
        ProductPred::True
        | ProductPred::False
        | ProductPred::Both(_, _)
        | ProductPred::LeftOnly(_)
        | ProductPred::RightOnly(_) => {},
    }
}

impl<A: BooleanAlgebra, B: BooleanAlgebra> Drop for ProductPred<A, B> {
    fn drop(&mut self) {
        let mut work = Vec::new();
        take_product_children(self, &mut work);
        while let Some(mut predicate) = work.pop() {
            take_product_children(&mut predicate, &mut work);
        }
    }
}

enum ProductDebugTask<'pred, A: BooleanAlgebra, B: BooleanAlgebra> {
    Visit(&'pred ProductPred<A, B>),
    Text(&'static str),
}

impl<A: BooleanAlgebra, B: BooleanAlgebra> fmt::Debug for ProductPred<A, B> {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut tasks = vec![ProductDebugTask::Visit(self)];
        while let Some(task) = tasks.pop() {
            match task {
                ProductDebugTask::Text(text) => formatter.write_str(text)?,
                ProductDebugTask::Visit(ProductPred::True) => formatter.write_str("True")?,
                ProductDebugTask::Visit(ProductPred::False) => formatter.write_str("False")?,
                ProductDebugTask::Visit(ProductPred::Both(left, right)) => {
                    write!(formatter, "Both({left:?}, {right:?})")?;
                },
                ProductDebugTask::Visit(ProductPred::LeftOnly(left)) => {
                    write!(formatter, "LeftOnly({left:?})")?;
                },
                ProductDebugTask::Visit(ProductPred::RightOnly(right)) => {
                    write!(formatter, "RightOnly({right:?})")?;
                },
                ProductDebugTask::Visit(ProductPred::Not(body)) => {
                    push_product_debug_unary(&mut tasks, "Not(", body);
                },
                ProductDebugTask::Visit(ProductPred::And(left, right)) => {
                    push_product_debug_binary(&mut tasks, "And(", left, right);
                },
                ProductDebugTask::Visit(ProductPred::Or(left, right)) => {
                    push_product_debug_binary(&mut tasks, "Or(", left, right);
                },
            }
        }
        Ok(())
    }
}

fn push_product_debug_unary<'pred, A: BooleanAlgebra, B: BooleanAlgebra>(
    tasks: &mut Vec<ProductDebugTask<'pred, A, B>>,
    prefix: &'static str,
    body: &'pred ProductPred<A, B>,
) {
    tasks.push(ProductDebugTask::Text(")"));
    tasks.push(ProductDebugTask::Visit(body));
    tasks.push(ProductDebugTask::Text(prefix));
}

fn push_product_debug_binary<'pred, A: BooleanAlgebra, B: BooleanAlgebra>(
    tasks: &mut Vec<ProductDebugTask<'pred, A, B>>,
    prefix: &'static str,
    left: &'pred ProductPred<A, B>,
    right: &'pred ProductPred<A, B>,
) {
    tasks.push(ProductDebugTask::Text(")"));
    tasks.push(ProductDebugTask::Visit(right));
    tasks.push(ProductDebugTask::Text(", "));
    tasks.push(ProductDebugTask::Visit(left));
    tasks.push(ProductDebugTask::Text(prefix));
}
