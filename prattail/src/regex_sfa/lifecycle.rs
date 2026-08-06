//! Heap-backed lifecycle machines for symbolic regular expressions.

use super::RegexPred;
use std::fmt;
use std::hash::{Hash, Hasher};

#[derive(Clone, Copy)]
enum BinaryKind {
    Concat,
    Alt,
    Inter,
}

#[derive(Clone, Copy)]
enum UnaryKind {
    Star,
    Compl,
}

enum CloneTask<'pred, P> {
    Visit(&'pred RegexPred<P>),
    Binary(BinaryKind),
    Unary(UnaryKind),
}

impl<P: Clone> Clone for RegexPred<P> {
    fn clone(&self) -> Self {
        let mut tasks = vec![CloneTask::Visit(self)];
        let mut values = Vec::new();
        while let Some(task) = tasks.pop() {
            match task {
                CloneTask::Visit(RegexPred::Empty) => values.push(RegexPred::Empty),
                CloneTask::Visit(RegexPred::Epsilon) => values.push(RegexPred::Epsilon),
                CloneTask::Visit(RegexPred::Elem(class)) => {
                    values.push(RegexPred::Elem(class.clone()));
                },
                CloneTask::Visit(RegexPred::Length(lower, upper)) => {
                    values.push(RegexPred::Length(*lower, *upper));
                },
                CloneTask::Visit(RegexPred::Concat(left, right)) => {
                    push_clone_binary(&mut tasks, BinaryKind::Concat, left, right);
                },
                CloneTask::Visit(RegexPred::Alt(left, right)) => {
                    push_clone_binary(&mut tasks, BinaryKind::Alt, left, right);
                },
                CloneTask::Visit(RegexPred::Inter(left, right)) => {
                    push_clone_binary(&mut tasks, BinaryKind::Inter, left, right);
                },
                CloneTask::Visit(RegexPred::Star(body)) => {
                    push_clone_unary(&mut tasks, UnaryKind::Star, body);
                },
                CloneTask::Visit(RegexPred::Compl(body)) => {
                    push_clone_unary(&mut tasks, UnaryKind::Compl, body);
                },
                CloneTask::Binary(kind) => {
                    let right = values.pop().expect("RegexPred clone lost right body");
                    let left = values.pop().expect("RegexPred clone lost left body");
                    values.push(match kind {
                        BinaryKind::Concat => RegexPred::Concat(Box::new(left), Box::new(right)),
                        BinaryKind::Alt => RegexPred::Alt(Box::new(left), Box::new(right)),
                        BinaryKind::Inter => RegexPred::Inter(Box::new(left), Box::new(right)),
                    });
                },
                CloneTask::Unary(kind) => {
                    let body = values.pop().expect("RegexPred clone lost unary body");
                    values.push(match kind {
                        UnaryKind::Star => RegexPred::Star(Box::new(body)),
                        UnaryKind::Compl => RegexPred::Compl(Box::new(body)),
                    });
                },
            }
        }
        debug_assert_eq!(values.len(), 1);
        values.pop().expect("RegexPred clone produced no value")
    }
}

fn push_clone_binary<'pred, P>(
    tasks: &mut Vec<CloneTask<'pred, P>>,
    kind: BinaryKind,
    left: &'pred RegexPred<P>,
    right: &'pred RegexPred<P>,
) {
    tasks.push(CloneTask::Binary(kind));
    tasks.push(CloneTask::Visit(right));
    tasks.push(CloneTask::Visit(left));
}

fn push_clone_unary<'pred, P>(
    tasks: &mut Vec<CloneTask<'pred, P>>,
    kind: UnaryKind,
    body: &'pred RegexPred<P>,
) {
    tasks.push(CloneTask::Unary(kind));
    tasks.push(CloneTask::Visit(body));
}

impl<P: PartialEq> PartialEq for RegexPred<P> {
    fn eq(&self, other: &Self) -> bool {
        let mut work = vec![(self, other)];
        while let Some((left, right)) = work.pop() {
            match (left, right) {
                (RegexPred::Empty, RegexPred::Empty) | (RegexPred::Epsilon, RegexPred::Epsilon) => {
                },
                (RegexPred::Elem(a), RegexPred::Elem(b)) if a == b => {},
                (RegexPred::Length(al, au), RegexPred::Length(bl, bu)) if al == bl && au == bu => {
                },
                (RegexPred::Star(a), RegexPred::Star(b))
                | (RegexPred::Compl(a), RegexPred::Compl(b)) => work.push((a, b)),
                (RegexPred::Concat(al, ar), RegexPred::Concat(bl, br))
                | (RegexPred::Alt(al, ar), RegexPred::Alt(bl, br))
                | (RegexPred::Inter(al, ar), RegexPred::Inter(bl, br)) => {
                    work.push((ar, br));
                    work.push((al, bl));
                },
                _ => return false,
            }
        }
        true
    }
}

impl<P: Eq> Eq for RegexPred<P> {}

impl<P: Hash> Hash for RegexPred<P> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        let mut work = vec![self];
        while let Some(predicate) = work.pop() {
            std::mem::discriminant(predicate).hash(state);
            match predicate {
                RegexPred::Empty | RegexPred::Epsilon => {},
                RegexPred::Elem(class) => class.hash(state),
                RegexPred::Length(lower, upper) => {
                    lower.hash(state);
                    upper.hash(state);
                },
                RegexPred::Star(body) | RegexPred::Compl(body) => work.push(body),
                RegexPred::Concat(left, right)
                | RegexPred::Alt(left, right)
                | RegexPred::Inter(left, right) => {
                    work.push(right);
                    work.push(left);
                },
            }
        }
    }
}

fn take_children<P>(predicate: &mut RegexPred<P>, work: &mut Vec<RegexPred<P>>) {
    let take =
        |child: &mut Box<RegexPred<P>>| *std::mem::replace(child, Box::new(RegexPred::Empty));
    match predicate {
        RegexPred::Star(body) | RegexPred::Compl(body) => work.push(take(body)),
        RegexPred::Concat(left, right)
        | RegexPred::Alt(left, right)
        | RegexPred::Inter(left, right) => {
            work.push(take(left));
            work.push(take(right));
        },
        RegexPred::Empty | RegexPred::Epsilon | RegexPred::Elem(_) | RegexPred::Length(_, _) => {},
    }
}

impl<P> Drop for RegexPred<P> {
    fn drop(&mut self) {
        let mut work = Vec::new();
        take_children(self, &mut work);
        while let Some(mut predicate) = work.pop() {
            take_children(&mut predicate, &mut work);
        }
    }
}

enum DebugTask<'pred, P> {
    Visit(&'pred RegexPred<P>),
    Text(&'static str),
}

impl<P: fmt::Debug> fmt::Debug for RegexPred<P> {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut tasks = vec![DebugTask::Visit(self)];
        while let Some(task) = tasks.pop() {
            match task {
                DebugTask::Text(text) => formatter.write_str(text)?,
                DebugTask::Visit(RegexPred::Empty) => formatter.write_str("Empty")?,
                DebugTask::Visit(RegexPred::Epsilon) => formatter.write_str("Epsilon")?,
                DebugTask::Visit(RegexPred::Elem(class)) => {
                    write!(formatter, "Elem({class:?})")?;
                },
                DebugTask::Visit(RegexPred::Length(lower, upper)) => {
                    write!(formatter, "Length({lower:?}, {upper:?})")?;
                },
                DebugTask::Visit(RegexPred::Star(body)) => {
                    push_debug_unary(&mut tasks, "Star(", body);
                },
                DebugTask::Visit(RegexPred::Compl(body)) => {
                    push_debug_unary(&mut tasks, "Compl(", body);
                },
                DebugTask::Visit(RegexPred::Concat(left, right)) => {
                    push_debug_binary(&mut tasks, "Concat(", left, right);
                },
                DebugTask::Visit(RegexPred::Alt(left, right)) => {
                    push_debug_binary(&mut tasks, "Alt(", left, right);
                },
                DebugTask::Visit(RegexPred::Inter(left, right)) => {
                    push_debug_binary(&mut tasks, "Inter(", left, right);
                },
            }
        }
        Ok(())
    }
}

fn push_debug_unary<'pred, P>(
    tasks: &mut Vec<DebugTask<'pred, P>>,
    prefix: &'static str,
    body: &'pred RegexPred<P>,
) {
    tasks.push(DebugTask::Text(")"));
    tasks.push(DebugTask::Visit(body));
    tasks.push(DebugTask::Text(prefix));
}

fn push_debug_binary<'pred, P>(
    tasks: &mut Vec<DebugTask<'pred, P>>,
    prefix: &'static str,
    left: &'pred RegexPred<P>,
    right: &'pred RegexPred<P>,
) {
    tasks.push(DebugTask::Text(")"));
    tasks.push(DebugTask::Visit(right));
    tasks.push(DebugTask::Text(", "));
    tasks.push(DebugTask::Visit(left));
    tasks.push(DebugTask::Text(prefix));
}
