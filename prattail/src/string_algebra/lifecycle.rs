//! Heap-backed lifecycle machines for string predicates.

use super::StrPred;
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

enum CloneTask<'pred> {
    Visit(&'pred StrPred),
    Binary(BinaryKind),
    Unary(UnaryKind),
}

impl Clone for StrPred {
    fn clone(&self) -> Self {
        let mut tasks = vec![CloneTask::Visit(self)];
        let mut values = Vec::new();
        while let Some(task) = tasks.pop() {
            match task {
                CloneTask::Visit(StrPred::Empty) => values.push(StrPred::Empty),
                CloneTask::Visit(StrPred::Epsilon) => values.push(StrPred::Epsilon),
                CloneTask::Visit(StrPred::Class(class)) => {
                    values.push(StrPred::Class(class.clone()));
                },
                CloneTask::Visit(StrPred::Literal(literal)) => {
                    values.push(StrPred::Literal(literal.clone()));
                },
                CloneTask::Visit(StrPred::Length(lower, upper)) => {
                    values.push(StrPred::Length(*lower, *upper));
                },
                CloneTask::Visit(StrPred::Concat(left, right)) => {
                    push_clone_binary(&mut tasks, BinaryKind::Concat, left, right);
                },
                CloneTask::Visit(StrPred::Alt(left, right)) => {
                    push_clone_binary(&mut tasks, BinaryKind::Alt, left, right);
                },
                CloneTask::Visit(StrPred::Inter(left, right)) => {
                    push_clone_binary(&mut tasks, BinaryKind::Inter, left, right);
                },
                CloneTask::Visit(StrPred::Star(body)) => {
                    push_clone_unary(&mut tasks, UnaryKind::Star, body);
                },
                CloneTask::Visit(StrPred::Compl(body)) => {
                    push_clone_unary(&mut tasks, UnaryKind::Compl, body);
                },
                CloneTask::Binary(kind) => {
                    let right = values.pop().expect("StrPred clone lost right body");
                    let left = values.pop().expect("StrPred clone lost left body");
                    values.push(match kind {
                        BinaryKind::Concat => StrPred::Concat(Box::new(left), Box::new(right)),
                        BinaryKind::Alt => StrPred::Alt(Box::new(left), Box::new(right)),
                        BinaryKind::Inter => StrPred::Inter(Box::new(left), Box::new(right)),
                    });
                },
                CloneTask::Unary(kind) => {
                    let body = values.pop().expect("StrPred clone lost unary body");
                    values.push(match kind {
                        UnaryKind::Star => StrPred::Star(Box::new(body)),
                        UnaryKind::Compl => StrPred::Compl(Box::new(body)),
                    });
                },
            }
        }
        debug_assert_eq!(values.len(), 1);
        values.pop().expect("StrPred clone produced no value")
    }
}

fn push_clone_binary<'pred>(
    tasks: &mut Vec<CloneTask<'pred>>,
    kind: BinaryKind,
    left: &'pred StrPred,
    right: &'pred StrPred,
) {
    tasks.push(CloneTask::Binary(kind));
    tasks.push(CloneTask::Visit(right));
    tasks.push(CloneTask::Visit(left));
}

fn push_clone_unary<'pred>(
    tasks: &mut Vec<CloneTask<'pred>>,
    kind: UnaryKind,
    body: &'pred StrPred,
) {
    tasks.push(CloneTask::Unary(kind));
    tasks.push(CloneTask::Visit(body));
}

impl PartialEq for StrPred {
    fn eq(&self, other: &Self) -> bool {
        let mut work = vec![(self, other)];
        while let Some((left, right)) = work.pop() {
            match (left, right) {
                (StrPred::Empty, StrPred::Empty) | (StrPred::Epsilon, StrPred::Epsilon) => {},
                (StrPred::Class(a), StrPred::Class(b)) if a == b => {},
                (StrPred::Literal(a), StrPred::Literal(b)) if a == b => {},
                (StrPred::Length(al, au), StrPred::Length(bl, bu)) if al == bl && au == bu => {},
                (StrPred::Star(a), StrPred::Star(b)) | (StrPred::Compl(a), StrPred::Compl(b)) => {
                    work.push((a, b));
                },
                (StrPred::Concat(al, ar), StrPred::Concat(bl, br))
                | (StrPred::Alt(al, ar), StrPred::Alt(bl, br))
                | (StrPred::Inter(al, ar), StrPred::Inter(bl, br)) => {
                    work.push((ar, br));
                    work.push((al, bl));
                },
                _ => return false,
            }
        }
        true
    }
}

impl Eq for StrPred {}

impl Hash for StrPred {
    fn hash<H: Hasher>(&self, state: &mut H) {
        let mut work = vec![self];
        while let Some(predicate) = work.pop() {
            std::mem::discriminant(predicate).hash(state);
            match predicate {
                StrPred::Empty | StrPred::Epsilon => {},
                StrPred::Class(class) => class.hash(state),
                StrPred::Literal(literal) => literal.hash(state),
                StrPred::Length(lower, upper) => {
                    lower.hash(state);
                    upper.hash(state);
                },
                StrPred::Star(body) | StrPred::Compl(body) => work.push(body),
                StrPred::Concat(left, right)
                | StrPred::Alt(left, right)
                | StrPred::Inter(left, right) => {
                    work.push(right);
                    work.push(left);
                },
            }
        }
    }
}

fn take_children(predicate: &mut StrPred, work: &mut Vec<StrPred>) {
    let take = |child: &mut Box<StrPred>| *std::mem::replace(child, Box::new(StrPred::Empty));
    match predicate {
        StrPred::Star(body) | StrPred::Compl(body) => work.push(take(body)),
        StrPred::Concat(left, right) | StrPred::Alt(left, right) | StrPred::Inter(left, right) => {
            work.push(take(left));
            work.push(take(right));
        },
        StrPred::Empty
        | StrPred::Epsilon
        | StrPred::Class(_)
        | StrPred::Literal(_)
        | StrPred::Length(_, _) => {},
    }
}

impl Drop for StrPred {
    fn drop(&mut self) {
        let mut work = Vec::new();
        take_children(self, &mut work);
        while let Some(mut predicate) = work.pop() {
            take_children(&mut predicate, &mut work);
        }
    }
}

enum DebugTask<'pred> {
    Visit(&'pred StrPred),
    Text(&'static str),
}

impl fmt::Debug for StrPred {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut tasks = vec![DebugTask::Visit(self)];
        while let Some(task) = tasks.pop() {
            match task {
                DebugTask::Text(text) => formatter.write_str(text)?,
                DebugTask::Visit(StrPred::Empty) => formatter.write_str("Empty")?,
                DebugTask::Visit(StrPred::Epsilon) => formatter.write_str("Epsilon")?,
                DebugTask::Visit(StrPred::Class(class)) => {
                    write!(formatter, "Class({class:?})")?;
                },
                DebugTask::Visit(StrPred::Literal(literal)) => {
                    write!(formatter, "Literal({literal:?})")?;
                },
                DebugTask::Visit(StrPred::Length(lower, upper)) => {
                    write!(formatter, "Length({lower:?}, {upper:?})")?;
                },
                DebugTask::Visit(StrPred::Star(body)) => {
                    push_debug_unary(&mut tasks, "Star(", body);
                },
                DebugTask::Visit(StrPred::Compl(body)) => {
                    push_debug_unary(&mut tasks, "Compl(", body);
                },
                DebugTask::Visit(StrPred::Concat(left, right)) => {
                    push_debug_binary(&mut tasks, "Concat(", left, right);
                },
                DebugTask::Visit(StrPred::Alt(left, right)) => {
                    push_debug_binary(&mut tasks, "Alt(", left, right);
                },
                DebugTask::Visit(StrPred::Inter(left, right)) => {
                    push_debug_binary(&mut tasks, "Inter(", left, right);
                },
            }
        }
        Ok(())
    }
}

fn push_debug_unary<'pred>(
    tasks: &mut Vec<DebugTask<'pred>>,
    prefix: &'static str,
    body: &'pred StrPred,
) {
    tasks.push(DebugTask::Text(")"));
    tasks.push(DebugTask::Visit(body));
    tasks.push(DebugTask::Text(prefix));
}

fn push_debug_binary<'pred>(
    tasks: &mut Vec<DebugTask<'pred>>,
    prefix: &'static str,
    left: &'pred StrPred,
    right: &'pred StrPred,
) {
    tasks.push(DebugTask::Text(")"));
    tasks.push(DebugTask::Visit(right));
    tasks.push(DebugTask::Text(", "));
    tasks.push(DebugTask::Visit(left));
    tasks.push(DebugTask::Text(prefix));
}
