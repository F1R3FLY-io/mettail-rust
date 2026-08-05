//! Heap-backed lifecycle and formatting PDAs for LTL formula trees.

use super::LtlFormula;
use std::fmt;
use std::hash::{Hash, Hasher};

enum CloneTask<'a> {
    Visit(&'a LtlFormula),
    Unary(UnaryKind, usize),
    Binary(BinaryKind, usize),
}

#[derive(Clone, Copy)]
enum UnaryKind {
    Not,
    Next,
    Eventually,
    Always,
}

#[derive(Clone, Copy)]
enum BinaryKind {
    And,
    Or,
    Implies,
    Until,
    Release,
    WeakUntil,
}

impl Clone for LtlFormula {
    fn clone(&self) -> Self {
        let mut tasks = vec![CloneTask::Visit(self)];
        let mut values = Vec::new();
        while let Some(task) = tasks.pop() {
            match task {
                CloneTask::Visit(LtlFormula::True) => values.push(LtlFormula::True),
                CloneTask::Visit(LtlFormula::False) => values.push(LtlFormula::False),
                CloneTask::Visit(LtlFormula::Atom(name)) => {
                    values.push(LtlFormula::Atom(name.clone()));
                },
                CloneTask::Visit(LtlFormula::Not(body)) => {
                    push_unary(&mut tasks, values.len(), UnaryKind::Not, body)
                },
                CloneTask::Visit(LtlFormula::Next(body)) => {
                    push_unary(&mut tasks, values.len(), UnaryKind::Next, body)
                },
                CloneTask::Visit(LtlFormula::Eventually(body)) => {
                    push_unary(&mut tasks, values.len(), UnaryKind::Eventually, body)
                },
                CloneTask::Visit(LtlFormula::Always(body)) => {
                    push_unary(&mut tasks, values.len(), UnaryKind::Always, body)
                },
                CloneTask::Visit(LtlFormula::And(left, right)) => {
                    push_binary(&mut tasks, values.len(), BinaryKind::And, left, right)
                },
                CloneTask::Visit(LtlFormula::Or(left, right)) => {
                    push_binary(&mut tasks, values.len(), BinaryKind::Or, left, right)
                },
                CloneTask::Visit(LtlFormula::Implies(left, right)) => {
                    push_binary(&mut tasks, values.len(), BinaryKind::Implies, left, right)
                },
                CloneTask::Visit(LtlFormula::Until(left, right)) => {
                    push_binary(&mut tasks, values.len(), BinaryKind::Until, left, right)
                },
                CloneTask::Visit(LtlFormula::Release(left, right)) => {
                    push_binary(&mut tasks, values.len(), BinaryKind::Release, left, right)
                },
                CloneTask::Visit(LtlFormula::WeakUntil(left, right)) => {
                    push_binary(&mut tasks, values.len(), BinaryKind::WeakUntil, left, right)
                },
                CloneTask::Unary(kind, base) => {
                    let body = values.pop().expect("LTL clone PDA lost a unary body");
                    values.truncate(base);
                    values.push(match kind {
                        UnaryKind::Not => LtlFormula::Not(Box::new(body)),
                        UnaryKind::Next => LtlFormula::Next(Box::new(body)),
                        UnaryKind::Eventually => LtlFormula::Eventually(Box::new(body)),
                        UnaryKind::Always => LtlFormula::Always(Box::new(body)),
                    });
                },
                CloneTask::Binary(kind, base) => {
                    let right = values.pop().expect("LTL clone PDA lost a right operand");
                    let left = values.pop().expect("LTL clone PDA lost a left operand");
                    values.truncate(base);
                    values.push(match kind {
                        BinaryKind::And => LtlFormula::And(Box::new(left), Box::new(right)),
                        BinaryKind::Or => LtlFormula::Or(Box::new(left), Box::new(right)),
                        BinaryKind::Implies => LtlFormula::Implies(Box::new(left), Box::new(right)),
                        BinaryKind::Until => LtlFormula::Until(Box::new(left), Box::new(right)),
                        BinaryKind::Release => LtlFormula::Release(Box::new(left), Box::new(right)),
                        BinaryKind::WeakUntil => {
                            LtlFormula::WeakUntil(Box::new(left), Box::new(right))
                        },
                    });
                },
            }
        }
        debug_assert_eq!(values.len(), 1);
        values.pop().expect("LTL clone PDA produced no result")
    }
}

fn push_unary<'a>(
    tasks: &mut Vec<CloneTask<'a>>,
    base: usize,
    kind: UnaryKind,
    body: &'a LtlFormula,
) {
    tasks.push(CloneTask::Unary(kind, base));
    tasks.push(CloneTask::Visit(body));
}

fn push_binary<'a>(
    tasks: &mut Vec<CloneTask<'a>>,
    base: usize,
    kind: BinaryKind,
    left: &'a LtlFormula,
    right: &'a LtlFormula,
) {
    tasks.push(CloneTask::Binary(kind, base));
    tasks.push(CloneTask::Visit(right));
    tasks.push(CloneTask::Visit(left));
}

impl PartialEq for LtlFormula {
    fn eq(&self, other: &Self) -> bool {
        let mut work = vec![(self, other)];
        while let Some((left, right)) = work.pop() {
            match (left, right) {
                (LtlFormula::True, LtlFormula::True) | (LtlFormula::False, LtlFormula::False) => {},
                (LtlFormula::Atom(a), LtlFormula::Atom(b)) if a == b => {},
                (LtlFormula::Not(a), LtlFormula::Not(b))
                | (LtlFormula::Next(a), LtlFormula::Next(b))
                | (LtlFormula::Eventually(a), LtlFormula::Eventually(b))
                | (LtlFormula::Always(a), LtlFormula::Always(b)) => work.push((a, b)),
                (LtlFormula::And(al, ar), LtlFormula::And(bl, br))
                | (LtlFormula::Or(al, ar), LtlFormula::Or(bl, br))
                | (LtlFormula::Implies(al, ar), LtlFormula::Implies(bl, br))
                | (LtlFormula::Until(al, ar), LtlFormula::Until(bl, br))
                | (LtlFormula::Release(al, ar), LtlFormula::Release(bl, br))
                | (LtlFormula::WeakUntil(al, ar), LtlFormula::WeakUntil(bl, br)) => {
                    work.push((ar, br));
                    work.push((al, bl));
                },
                _ => return false,
            }
        }
        true
    }
}

impl Eq for LtlFormula {}

impl Hash for LtlFormula {
    fn hash<H: Hasher>(&self, state: &mut H) {
        let mut work = vec![self];
        while let Some(formula) = work.pop() {
            std::mem::discriminant(formula).hash(state);
            match formula {
                LtlFormula::True | LtlFormula::False => {},
                LtlFormula::Atom(name) => name.hash(state),
                LtlFormula::Not(body)
                | LtlFormula::Next(body)
                | LtlFormula::Eventually(body)
                | LtlFormula::Always(body) => work.push(body),
                LtlFormula::And(left, right)
                | LtlFormula::Or(left, right)
                | LtlFormula::Implies(left, right)
                | LtlFormula::Until(left, right)
                | LtlFormula::Release(left, right)
                | LtlFormula::WeakUntil(left, right) => {
                    work.push(right);
                    work.push(left);
                },
            }
        }
    }
}

fn take_children(formula: &mut LtlFormula, work: &mut Vec<LtlFormula>) {
    let take = |child: &mut Box<LtlFormula>| *std::mem::replace(child, Box::new(LtlFormula::True));
    match formula {
        LtlFormula::Not(body)
        | LtlFormula::Next(body)
        | LtlFormula::Eventually(body)
        | LtlFormula::Always(body) => work.push(take(body)),
        LtlFormula::And(left, right)
        | LtlFormula::Or(left, right)
        | LtlFormula::Implies(left, right)
        | LtlFormula::Until(left, right)
        | LtlFormula::Release(left, right)
        | LtlFormula::WeakUntil(left, right) => {
            work.push(take(left));
            work.push(take(right));
        },
        LtlFormula::True | LtlFormula::False | LtlFormula::Atom(_) => {},
    }
}

impl Drop for LtlFormula {
    fn drop(&mut self) {
        let mut work = Vec::new();
        take_children(self, &mut work);
        while let Some(mut formula) = work.pop() {
            take_children(&mut formula, &mut work);
        }
    }
}

enum FormatTask<'a> {
    Visit(&'a LtlFormula),
    Text(&'static str),
}

impl fmt::Debug for LtlFormula {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut tasks = vec![FormatTask::Visit(self)];
        while let Some(task) = tasks.pop() {
            match task {
                FormatTask::Text(text) => formatter.write_str(text)?,
                FormatTask::Visit(LtlFormula::True) => formatter.write_str("True")?,
                FormatTask::Visit(LtlFormula::False) => formatter.write_str("False")?,
                FormatTask::Visit(LtlFormula::Atom(name)) => write!(formatter, "Atom({name:?})")?,
                FormatTask::Visit(LtlFormula::Not(body)) => {
                    push_format_unary(&mut tasks, "Not(", body)
                },
                FormatTask::Visit(LtlFormula::Next(body)) => {
                    push_format_unary(&mut tasks, "Next(", body)
                },
                FormatTask::Visit(LtlFormula::Eventually(body)) => {
                    push_format_unary(&mut tasks, "Eventually(", body)
                },
                FormatTask::Visit(LtlFormula::Always(body)) => {
                    push_format_unary(&mut tasks, "Always(", body)
                },
                FormatTask::Visit(LtlFormula::And(left, right)) => {
                    push_format_binary(&mut tasks, "And(", left, right)
                },
                FormatTask::Visit(LtlFormula::Or(left, right)) => {
                    push_format_binary(&mut tasks, "Or(", left, right)
                },
                FormatTask::Visit(LtlFormula::Implies(left, right)) => {
                    push_format_binary(&mut tasks, "Implies(", left, right)
                },
                FormatTask::Visit(LtlFormula::Until(left, right)) => {
                    push_format_binary(&mut tasks, "Until(", left, right)
                },
                FormatTask::Visit(LtlFormula::Release(left, right)) => {
                    push_format_binary(&mut tasks, "Release(", left, right)
                },
                FormatTask::Visit(LtlFormula::WeakUntil(left, right)) => {
                    push_format_binary(&mut tasks, "WeakUntil(", left, right)
                },
            }
        }
        Ok(())
    }
}

fn push_format_unary<'a>(
    tasks: &mut Vec<FormatTask<'a>>,
    open: &'static str,
    body: &'a LtlFormula,
) {
    tasks.push(FormatTask::Text(")"));
    tasks.push(FormatTask::Visit(body));
    tasks.push(FormatTask::Text(open));
}

fn push_format_binary<'a>(
    tasks: &mut Vec<FormatTask<'a>>,
    open: &'static str,
    left: &'a LtlFormula,
    right: &'a LtlFormula,
) {
    tasks.push(FormatTask::Text(")"));
    tasks.push(FormatTask::Visit(right));
    tasks.push(FormatTask::Text(", "));
    tasks.push(FormatTask::Visit(left));
    tasks.push(FormatTask::Text(open));
}

impl fmt::Display for LtlFormula {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut tasks = vec![FormatTask::Visit(self)];
        while let Some(task) = tasks.pop() {
            match task {
                FormatTask::Text(text) => formatter.write_str(text)?,
                FormatTask::Visit(LtlFormula::True) => formatter.write_str("true")?,
                FormatTask::Visit(LtlFormula::False) => formatter.write_str("false")?,
                FormatTask::Visit(LtlFormula::Atom(name)) => formatter.write_str(name)?,
                FormatTask::Visit(LtlFormula::Not(body)) => {
                    tasks.push(FormatTask::Visit(body));
                    tasks.push(FormatTask::Text("!"));
                },
                FormatTask::Visit(LtlFormula::Next(body)) => {
                    tasks.push(FormatTask::Visit(body));
                    tasks.push(FormatTask::Text("X"));
                },
                FormatTask::Visit(LtlFormula::Eventually(body)) => {
                    tasks.push(FormatTask::Visit(body));
                    tasks.push(FormatTask::Text("F"));
                },
                FormatTask::Visit(LtlFormula::Always(body)) => {
                    tasks.push(FormatTask::Visit(body));
                    tasks.push(FormatTask::Text("G"));
                },
                FormatTask::Visit(LtlFormula::And(left, right)) => {
                    push_display_binary(&mut tasks, " & ", left, right)
                },
                FormatTask::Visit(LtlFormula::Or(left, right)) => {
                    push_display_binary(&mut tasks, " | ", left, right)
                },
                FormatTask::Visit(LtlFormula::Implies(left, right)) => {
                    push_display_binary(&mut tasks, " -> ", left, right)
                },
                FormatTask::Visit(LtlFormula::Until(left, right)) => {
                    push_display_binary(&mut tasks, " U ", left, right)
                },
                FormatTask::Visit(LtlFormula::Release(left, right)) => {
                    push_display_binary(&mut tasks, " R ", left, right)
                },
                FormatTask::Visit(LtlFormula::WeakUntil(left, right)) => {
                    push_display_binary(&mut tasks, " W ", left, right)
                },
            }
        }
        Ok(())
    }
}

fn push_display_binary<'a>(
    tasks: &mut Vec<FormatTask<'a>>,
    separator: &'static str,
    left: &'a LtlFormula,
    right: &'a LtlFormula,
) {
    tasks.push(FormatTask::Text(")"));
    tasks.push(FormatTask::Visit(right));
    tasks.push(FormatTask::Text(separator));
    tasks.push(FormatTask::Visit(left));
    tasks.push(FormatTask::Text("("));
}
