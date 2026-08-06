//! Heap-backed lifecycle and debug-formatting machines for Presburger formulas.

use super::PresburgerPred;
use std::fmt;
use std::hash::{Hash, Hasher};

#[derive(Clone, Copy)]
enum BinaryKind {
    And,
    Or,
}

enum CloneTask<'pred> {
    Visit(&'pred PresburgerPred),
    Not,
    Exists(usize),
    Binary(BinaryKind),
}

impl Clone for PresburgerPred {
    fn clone(&self) -> Self {
        let mut tasks = vec![CloneTask::Visit(self)];
        let mut values = Vec::new();
        while let Some(task) = tasks.pop() {
            match task {
                CloneTask::Visit(PresburgerPred::True) => values.push(PresburgerPred::True),
                CloneTask::Visit(PresburgerPred::False) => values.push(PresburgerPred::False),
                CloneTask::Visit(PresburgerPred::Atom(constraint)) => {
                    values.push(PresburgerPred::Atom(constraint.clone()));
                },
                CloneTask::Visit(PresburgerPred::Not(body)) => {
                    tasks.push(CloneTask::Not);
                    tasks.push(CloneTask::Visit(body));
                },
                CloneTask::Visit(PresburgerPred::Exists { var, body }) => {
                    tasks.push(CloneTask::Exists(*var));
                    tasks.push(CloneTask::Visit(body));
                },
                CloneTask::Visit(PresburgerPred::And(left, right)) => {
                    push_binary(&mut tasks, BinaryKind::And, left, right);
                },
                CloneTask::Visit(PresburgerPred::Or(left, right)) => {
                    push_binary(&mut tasks, BinaryKind::Or, left, right);
                },
                CloneTask::Not => {
                    let body = Box::new(values.pop().expect("Presburger clone lost not body"));
                    values.push(PresburgerPred::Not(body));
                },
                CloneTask::Exists(var) => {
                    let body = Box::new(values.pop().expect("Presburger clone lost exists body"));
                    values.push(PresburgerPred::Exists { var, body });
                },
                CloneTask::Binary(kind) => {
                    let right = Box::new(values.pop().expect("Presburger clone lost right body"));
                    let left = Box::new(values.pop().expect("Presburger clone lost left body"));
                    values.push(match kind {
                        BinaryKind::And => PresburgerPred::And(left, right),
                        BinaryKind::Or => PresburgerPred::Or(left, right),
                    });
                },
            }
        }
        debug_assert_eq!(values.len(), 1);
        values.pop().expect("Presburger clone produced no value")
    }
}

fn push_binary<'pred>(
    tasks: &mut Vec<CloneTask<'pred>>,
    kind: BinaryKind,
    left: &'pred PresburgerPred,
    right: &'pred PresburgerPred,
) {
    tasks.push(CloneTask::Binary(kind));
    tasks.push(CloneTask::Visit(right));
    tasks.push(CloneTask::Visit(left));
}

impl PartialEq for PresburgerPred {
    fn eq(&self, other: &Self) -> bool {
        let mut work = vec![(self, other)];
        while let Some((left, right)) = work.pop() {
            match (left, right) {
                (PresburgerPred::True, PresburgerPred::True)
                | (PresburgerPred::False, PresburgerPred::False) => {},
                (PresburgerPred::Atom(a), PresburgerPred::Atom(b)) if a == b => {},
                (PresburgerPred::Not(a), PresburgerPred::Not(b)) => work.push((a, b)),
                (
                    PresburgerPred::Exists { var: av, body: ab },
                    PresburgerPred::Exists { var: bv, body: bb },
                ) if av == bv => work.push((ab, bb)),
                (PresburgerPred::And(al, ar), PresburgerPred::And(bl, br))
                | (PresburgerPred::Or(al, ar), PresburgerPred::Or(bl, br)) => {
                    work.push((ar, br));
                    work.push((al, bl));
                },
                _ => return false,
            }
        }
        true
    }
}

impl Eq for PresburgerPred {}

impl Hash for PresburgerPred {
    fn hash<H: Hasher>(&self, state: &mut H) {
        let mut work = vec![self];
        while let Some(pred) = work.pop() {
            std::mem::discriminant(pred).hash(state);
            match pred {
                PresburgerPred::True | PresburgerPred::False => {},
                PresburgerPred::Atom(constraint) => constraint.hash(state),
                PresburgerPred::Not(body) => work.push(body),
                PresburgerPred::Exists { var, body } => {
                    var.hash(state);
                    work.push(body);
                },
                PresburgerPred::And(left, right) | PresburgerPred::Or(left, right) => {
                    work.push(right);
                    work.push(left);
                },
            }
        }
    }
}

fn take_children(pred: &mut PresburgerPred, work: &mut Vec<PresburgerPred>) {
    let take =
        |child: &mut Box<PresburgerPred>| *std::mem::replace(child, Box::new(PresburgerPred::True));
    match pred {
        PresburgerPred::Not(body) | PresburgerPred::Exists { body, .. } => work.push(take(body)),
        PresburgerPred::And(left, right) | PresburgerPred::Or(left, right) => {
            work.push(take(left));
            work.push(take(right));
        },
        PresburgerPred::True | PresburgerPred::False | PresburgerPred::Atom(_) => {},
    }
}

impl Drop for PresburgerPred {
    fn drop(&mut self) {
        let mut work = Vec::new();
        take_children(self, &mut work);
        while let Some(mut pred) = work.pop() {
            take_children(&mut pred, &mut work);
        }
    }
}

enum DebugTask<'pred> {
    Visit(&'pred PresburgerPred),
    Text(&'static str),
}

impl fmt::Debug for PresburgerPred {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut tasks = vec![DebugTask::Visit(self)];
        while let Some(task) = tasks.pop() {
            match task {
                DebugTask::Text(text) => formatter.write_str(text)?,
                DebugTask::Visit(PresburgerPred::True) => formatter.write_str("True")?,
                DebugTask::Visit(PresburgerPred::False) => formatter.write_str("False")?,
                DebugTask::Visit(PresburgerPred::Atom(constraint)) => {
                    write!(formatter, "Atom({constraint:?})")?;
                },
                DebugTask::Visit(PresburgerPred::Not(body)) => {
                    push_unary_debug(&mut tasks, "Not(", body);
                },
                DebugTask::Visit(PresburgerPred::And(left, right)) => {
                    push_binary_debug(&mut tasks, "And(", left, right);
                },
                DebugTask::Visit(PresburgerPred::Or(left, right)) => {
                    push_binary_debug(&mut tasks, "Or(", left, right);
                },
                DebugTask::Visit(PresburgerPred::Exists { var, body }) => {
                    tasks.push(DebugTask::Text(" }"));
                    tasks.push(DebugTask::Visit(body));
                    write!(formatter, "Exists {{ var: {var:?}, body: ")?;
                },
            }
        }
        Ok(())
    }
}

fn push_unary_debug<'pred>(
    tasks: &mut Vec<DebugTask<'pred>>,
    prefix: &'static str,
    body: &'pred PresburgerPred,
) {
    tasks.push(DebugTask::Text(")"));
    tasks.push(DebugTask::Visit(body));
    tasks.push(DebugTask::Text(prefix));
}

fn push_binary_debug<'pred>(
    tasks: &mut Vec<DebugTask<'pred>>,
    prefix: &'static str,
    left: &'pred PresburgerPred,
    right: &'pred PresburgerPred,
) {
    tasks.push(DebugTask::Text(")"));
    tasks.push(DebugTask::Visit(right));
    tasks.push(DebugTask::Text(", "));
    tasks.push(DebugTask::Visit(left));
    tasks.push(DebugTask::Text(prefix));
}
