//! Heap-backed lifecycle machines for N-ary product and sum predicates.

use super::{NaryProductPred, SumPred};
use std::fmt;
use std::hash::{Hash, Hasher};

#[derive(Clone, Copy)]
enum BinaryKind {
    And,
    Or,
}

enum ProductCloneTask<'pred, P> {
    Visit(&'pred NaryProductPred<P>),
    Binary(BinaryKind),
    Not,
}

impl<P: Clone> Clone for NaryProductPred<P> {
    fn clone(&self) -> Self {
        let mut tasks = vec![ProductCloneTask::Visit(self)];
        let mut values = Vec::new();
        while let Some(task) = tasks.pop() {
            match task {
                ProductCloneTask::Visit(NaryProductPred::True) => {
                    values.push(NaryProductPred::True);
                },
                ProductCloneTask::Visit(NaryProductPred::False) => {
                    values.push(NaryProductPred::False);
                },
                ProductCloneTask::Visit(NaryProductPred::Field(index, predicate)) => {
                    values.push(NaryProductPred::Field(*index, predicate.clone()));
                },
                ProductCloneTask::Visit(NaryProductPred::Not(body)) => {
                    tasks.push(ProductCloneTask::Not);
                    tasks.push(ProductCloneTask::Visit(body));
                },
                ProductCloneTask::Visit(NaryProductPred::And(left, right)) => {
                    push_product_clone_binary(&mut tasks, BinaryKind::And, left, right);
                },
                ProductCloneTask::Visit(NaryProductPred::Or(left, right)) => {
                    push_product_clone_binary(&mut tasks, BinaryKind::Or, left, right);
                },
                ProductCloneTask::Not => {
                    let body = values
                        .pop()
                        .expect("NaryProductPred clone lost negated body");
                    values.push(NaryProductPred::Not(Box::new(body)));
                },
                ProductCloneTask::Binary(kind) => {
                    let right = values.pop().expect("NaryProductPred clone lost right body");
                    let left = values.pop().expect("NaryProductPred clone lost left body");
                    values.push(match kind {
                        BinaryKind::And => NaryProductPred::And(Box::new(left), Box::new(right)),
                        BinaryKind::Or => NaryProductPred::Or(Box::new(left), Box::new(right)),
                    });
                },
            }
        }
        debug_assert_eq!(values.len(), 1);
        values
            .pop()
            .expect("NaryProductPred clone produced no value")
    }
}

fn push_product_clone_binary<'pred, P>(
    tasks: &mut Vec<ProductCloneTask<'pred, P>>,
    kind: BinaryKind,
    left: &'pred NaryProductPred<P>,
    right: &'pred NaryProductPred<P>,
) {
    tasks.push(ProductCloneTask::Binary(kind));
    tasks.push(ProductCloneTask::Visit(right));
    tasks.push(ProductCloneTask::Visit(left));
}

impl<P: PartialEq> PartialEq for NaryProductPred<P> {
    fn eq(&self, other: &Self) -> bool {
        let mut work = vec![(self, other)];
        while let Some((left, right)) = work.pop() {
            match (left, right) {
                (NaryProductPred::True, NaryProductPred::True)
                | (NaryProductPred::False, NaryProductPred::False) => {},
                (NaryProductPred::Field(ai, ap), NaryProductPred::Field(bi, bp))
                    if ai == bi && ap == bp => {},
                (NaryProductPred::Not(a), NaryProductPred::Not(b)) => work.push((a, b)),
                (NaryProductPred::And(al, ar), NaryProductPred::And(bl, br))
                | (NaryProductPred::Or(al, ar), NaryProductPred::Or(bl, br)) => {
                    work.push((ar, br));
                    work.push((al, bl));
                },
                _ => return false,
            }
        }
        true
    }
}

impl<P: Eq> Eq for NaryProductPred<P> {}

impl<P: Hash> Hash for NaryProductPred<P> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        let mut work = vec![self];
        while let Some(predicate) = work.pop() {
            std::mem::discriminant(predicate).hash(state);
            match predicate {
                NaryProductPred::True | NaryProductPred::False => {},
                NaryProductPred::Field(index, field) => {
                    index.hash(state);
                    field.hash(state);
                },
                NaryProductPred::Not(body) => work.push(body),
                NaryProductPred::And(left, right) | NaryProductPred::Or(left, right) => {
                    work.push(right);
                    work.push(left);
                },
            }
        }
    }
}

fn take_product_children<P>(
    predicate: &mut NaryProductPred<P>,
    work: &mut Vec<NaryProductPred<P>>,
) {
    let take = |child: &mut Box<NaryProductPred<P>>| {
        *std::mem::replace(child, Box::new(NaryProductPred::True))
    };
    match predicate {
        NaryProductPred::Not(body) => work.push(take(body)),
        NaryProductPred::And(left, right) | NaryProductPred::Or(left, right) => {
            work.push(take(left));
            work.push(take(right));
        },
        NaryProductPred::True | NaryProductPred::False | NaryProductPred::Field(_, _) => {},
    }
}

impl<P> Drop for NaryProductPred<P> {
    fn drop(&mut self) {
        let mut work = Vec::new();
        take_product_children(self, &mut work);
        while let Some(mut predicate) = work.pop() {
            take_product_children(&mut predicate, &mut work);
        }
    }
}

enum ProductDebugTask<'pred, P> {
    Visit(&'pred NaryProductPred<P>),
    Text(&'static str),
}

impl<P: fmt::Debug> fmt::Debug for NaryProductPred<P> {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut tasks = vec![ProductDebugTask::Visit(self)];
        while let Some(task) = tasks.pop() {
            match task {
                ProductDebugTask::Text(text) => formatter.write_str(text)?,
                ProductDebugTask::Visit(NaryProductPred::True) => formatter.write_str("True")?,
                ProductDebugTask::Visit(NaryProductPred::False) => formatter.write_str("False")?,
                ProductDebugTask::Visit(NaryProductPred::Field(index, predicate)) => {
                    write!(formatter, "Field({index:?}, {predicate:?})")?;
                },
                ProductDebugTask::Visit(NaryProductPred::Not(body)) => {
                    push_product_debug_unary(&mut tasks, "Not(", body);
                },
                ProductDebugTask::Visit(NaryProductPred::And(left, right)) => {
                    push_product_debug_binary(&mut tasks, "And(", left, right);
                },
                ProductDebugTask::Visit(NaryProductPred::Or(left, right)) => {
                    push_product_debug_binary(&mut tasks, "Or(", left, right);
                },
            }
        }
        Ok(())
    }
}

fn push_product_debug_unary<'pred, P>(
    tasks: &mut Vec<ProductDebugTask<'pred, P>>,
    prefix: &'static str,
    body: &'pred NaryProductPred<P>,
) {
    tasks.push(ProductDebugTask::Text(")"));
    tasks.push(ProductDebugTask::Visit(body));
    tasks.push(ProductDebugTask::Text(prefix));
}

fn push_product_debug_binary<'pred, P>(
    tasks: &mut Vec<ProductDebugTask<'pred, P>>,
    prefix: &'static str,
    left: &'pred NaryProductPred<P>,
    right: &'pred NaryProductPred<P>,
) {
    tasks.push(ProductDebugTask::Text(")"));
    tasks.push(ProductDebugTask::Visit(right));
    tasks.push(ProductDebugTask::Text(", "));
    tasks.push(ProductDebugTask::Visit(left));
    tasks.push(ProductDebugTask::Text(prefix));
}

enum SumCloneTask<'pred, P> {
    Visit(&'pred SumPred<P>),
    Binary(BinaryKind),
    Not,
}

impl<P: Clone> Clone for SumPred<P> {
    fn clone(&self) -> Self {
        let mut tasks = vec![SumCloneTask::Visit(self)];
        let mut values = Vec::new();
        while let Some(task) = tasks.pop() {
            match task {
                SumCloneTask::Visit(SumPred::True) => values.push(SumPred::True),
                SumCloneTask::Visit(SumPred::False) => values.push(SumPred::False),
                SumCloneTask::Visit(SumPred::InVariant(index, predicate)) => {
                    values.push(SumPred::InVariant(*index, predicate.clone()));
                },
                SumCloneTask::Visit(SumPred::TagIs(index)) => {
                    values.push(SumPred::TagIs(*index));
                },
                SumCloneTask::Visit(SumPred::Not(body)) => {
                    tasks.push(SumCloneTask::Not);
                    tasks.push(SumCloneTask::Visit(body));
                },
                SumCloneTask::Visit(SumPred::And(left, right)) => {
                    push_sum_clone_binary(&mut tasks, BinaryKind::And, left, right);
                },
                SumCloneTask::Visit(SumPred::Or(left, right)) => {
                    push_sum_clone_binary(&mut tasks, BinaryKind::Or, left, right);
                },
                SumCloneTask::Not => {
                    let body = values.pop().expect("SumPred clone lost negated body");
                    values.push(SumPred::Not(Box::new(body)));
                },
                SumCloneTask::Binary(kind) => {
                    let right = values.pop().expect("SumPred clone lost right body");
                    let left = values.pop().expect("SumPred clone lost left body");
                    values.push(match kind {
                        BinaryKind::And => SumPred::And(Box::new(left), Box::new(right)),
                        BinaryKind::Or => SumPred::Or(Box::new(left), Box::new(right)),
                    });
                },
            }
        }
        debug_assert_eq!(values.len(), 1);
        values.pop().expect("SumPred clone produced no value")
    }
}

fn push_sum_clone_binary<'pred, P>(
    tasks: &mut Vec<SumCloneTask<'pred, P>>,
    kind: BinaryKind,
    left: &'pred SumPred<P>,
    right: &'pred SumPred<P>,
) {
    tasks.push(SumCloneTask::Binary(kind));
    tasks.push(SumCloneTask::Visit(right));
    tasks.push(SumCloneTask::Visit(left));
}

impl<P: PartialEq> PartialEq for SumPred<P> {
    fn eq(&self, other: &Self) -> bool {
        let mut work = vec![(self, other)];
        while let Some((left, right)) = work.pop() {
            match (left, right) {
                (SumPred::True, SumPred::True) | (SumPred::False, SumPred::False) => {},
                (SumPred::InVariant(ai, ap), SumPred::InVariant(bi, bp))
                    if ai == bi && ap == bp => {},
                (SumPred::TagIs(a), SumPred::TagIs(b)) if a == b => {},
                (SumPred::Not(a), SumPred::Not(b)) => work.push((a, b)),
                (SumPred::And(al, ar), SumPred::And(bl, br))
                | (SumPred::Or(al, ar), SumPred::Or(bl, br)) => {
                    work.push((ar, br));
                    work.push((al, bl));
                },
                _ => return false,
            }
        }
        true
    }
}

impl<P: Eq> Eq for SumPred<P> {}

impl<P: Hash> Hash for SumPred<P> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        let mut work = vec![self];
        while let Some(predicate) = work.pop() {
            std::mem::discriminant(predicate).hash(state);
            match predicate {
                SumPred::True | SumPred::False => {},
                SumPred::InVariant(index, variant) => {
                    index.hash(state);
                    variant.hash(state);
                },
                SumPred::TagIs(index) => index.hash(state),
                SumPred::Not(body) => work.push(body),
                SumPred::And(left, right) | SumPred::Or(left, right) => {
                    work.push(right);
                    work.push(left);
                },
            }
        }
    }
}

fn take_sum_children<P>(predicate: &mut SumPred<P>, work: &mut Vec<SumPred<P>>) {
    let take = |child: &mut Box<SumPred<P>>| *std::mem::replace(child, Box::new(SumPred::True));
    match predicate {
        SumPred::Not(body) => work.push(take(body)),
        SumPred::And(left, right) | SumPred::Or(left, right) => {
            work.push(take(left));
            work.push(take(right));
        },
        SumPred::True | SumPred::False | SumPred::InVariant(_, _) | SumPred::TagIs(_) => {},
    }
}

impl<P> Drop for SumPred<P> {
    fn drop(&mut self) {
        let mut work = Vec::new();
        take_sum_children(self, &mut work);
        while let Some(mut predicate) = work.pop() {
            take_sum_children(&mut predicate, &mut work);
        }
    }
}

enum SumDebugTask<'pred, P> {
    Visit(&'pred SumPred<P>),
    Text(&'static str),
}

impl<P: fmt::Debug> fmt::Debug for SumPred<P> {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut tasks = vec![SumDebugTask::Visit(self)];
        while let Some(task) = tasks.pop() {
            match task {
                SumDebugTask::Text(text) => formatter.write_str(text)?,
                SumDebugTask::Visit(SumPred::True) => formatter.write_str("True")?,
                SumDebugTask::Visit(SumPred::False) => formatter.write_str("False")?,
                SumDebugTask::Visit(SumPred::InVariant(index, predicate)) => {
                    write!(formatter, "InVariant({index:?}, {predicate:?})")?;
                },
                SumDebugTask::Visit(SumPred::TagIs(index)) => {
                    write!(formatter, "TagIs({index:?})")?;
                },
                SumDebugTask::Visit(SumPred::Not(body)) => {
                    push_sum_debug_unary(&mut tasks, "Not(", body);
                },
                SumDebugTask::Visit(SumPred::And(left, right)) => {
                    push_sum_debug_binary(&mut tasks, "And(", left, right);
                },
                SumDebugTask::Visit(SumPred::Or(left, right)) => {
                    push_sum_debug_binary(&mut tasks, "Or(", left, right);
                },
            }
        }
        Ok(())
    }
}

fn push_sum_debug_unary<'pred, P>(
    tasks: &mut Vec<SumDebugTask<'pred, P>>,
    prefix: &'static str,
    body: &'pred SumPred<P>,
) {
    tasks.push(SumDebugTask::Text(")"));
    tasks.push(SumDebugTask::Visit(body));
    tasks.push(SumDebugTask::Text(prefix));
}

fn push_sum_debug_binary<'pred, P>(
    tasks: &mut Vec<SumDebugTask<'pred, P>>,
    prefix: &'static str,
    left: &'pred SumPred<P>,
    right: &'pred SumPred<P>,
) {
    tasks.push(SumDebugTask::Text(")"));
    tasks.push(SumDebugTask::Visit(right));
    tasks.push(SumDebugTask::Text(", "));
    tasks.push(SumDebugTask::Visit(left));
    tasks.push(SumDebugTask::Text(prefix));
}
