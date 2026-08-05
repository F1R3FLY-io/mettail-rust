//! Heap-backed lifecycle and formatting PDAs for modal mu-calculus formulas.

use super::MuCalculusFormula;
use std::fmt;
use std::hash::{Hash, Hasher};

enum CloneTask<'a> {
    Visit(&'a MuCalculusFormula),
    Not(usize),
    And(usize),
    Or(usize),
    Diamond(usize, usize),
    Box(usize, usize),
    Mu(&'a str, usize),
    Nu(&'a str, usize),
}

impl Clone for MuCalculusFormula {
    fn clone(&self) -> Self {
        let mut tasks = vec![CloneTask::Visit(self)];
        let mut values = Vec::new();
        while let Some(task) = tasks.pop() {
            match task {
                CloneTask::Visit(MuCalculusFormula::Var(var)) => {
                    values.push(MuCalculusFormula::Var(var.clone()))
                },
                CloneTask::Visit(MuCalculusFormula::True) => values.push(MuCalculusFormula::True),
                CloneTask::Visit(MuCalculusFormula::False) => values.push(MuCalculusFormula::False),
                CloneTask::Visit(MuCalculusFormula::Atom(atom)) => {
                    values.push(MuCalculusFormula::Atom(atom.clone()))
                },
                CloneTask::Visit(MuCalculusFormula::Not(body)) => {
                    push_unary(&mut tasks, values.len(), CloneTask::Not, body)
                },
                CloneTask::Visit(MuCalculusFormula::And(left, right)) => {
                    push_binary(&mut tasks, values.len(), CloneTask::And, left, right)
                },
                CloneTask::Visit(MuCalculusFormula::Or(left, right)) => {
                    push_binary(&mut tasks, values.len(), CloneTask::Or, left, right)
                },
                CloneTask::Visit(MuCalculusFormula::Diamond { child_idx, body }) => {
                    let child_idx = *child_idx;
                    push_unary(
                        &mut tasks,
                        values.len(),
                        |base| CloneTask::Diamond(child_idx, base),
                        body,
                    )
                },
                CloneTask::Visit(MuCalculusFormula::Box { child_idx, body }) => {
                    let child_idx = *child_idx;
                    push_unary(
                        &mut tasks,
                        values.len(),
                        |base| CloneTask::Box(child_idx, base),
                        body,
                    )
                },
                CloneTask::Visit(MuCalculusFormula::Mu { var, body }) => {
                    push_unary(&mut tasks, values.len(), |base| CloneTask::Mu(var, base), body)
                },
                CloneTask::Visit(MuCalculusFormula::Nu { var, body }) => {
                    push_unary(&mut tasks, values.len(), |base| CloneTask::Nu(var, base), body)
                },
                CloneTask::Not(base) => {
                    finish_unary(&mut values, base, |body| MuCalculusFormula::Not(Box::new(body)))
                },
                CloneTask::And(base) => finish_binary(&mut values, base, |left, right| {
                    MuCalculusFormula::And(Box::new(left), Box::new(right))
                }),
                CloneTask::Or(base) => finish_binary(&mut values, base, |left, right| {
                    MuCalculusFormula::Or(Box::new(left), Box::new(right))
                }),
                CloneTask::Diamond(child_idx, base) => finish_unary(&mut values, base, |body| {
                    MuCalculusFormula::Diamond { child_idx, body: Box::new(body) }
                }),
                CloneTask::Box(child_idx, base) => finish_unary(&mut values, base, |body| {
                    MuCalculusFormula::Box { child_idx, body: Box::new(body) }
                }),
                CloneTask::Mu(var, base) => {
                    finish_unary(&mut values, base, |body| MuCalculusFormula::Mu {
                        var: var.to_owned(),
                        body: Box::new(body),
                    })
                },
                CloneTask::Nu(var, base) => {
                    finish_unary(&mut values, base, |body| MuCalculusFormula::Nu {
                        var: var.to_owned(),
                        body: Box::new(body),
                    })
                },
            }
        }
        debug_assert_eq!(values.len(), 1);
        values
            .pop()
            .expect("mu-calculus clone PDA produced no result")
    }
}

fn push_unary<'a>(
    tasks: &mut Vec<CloneTask<'a>>,
    base: usize,
    finish: impl FnOnce(usize) -> CloneTask<'a>,
    body: &'a MuCalculusFormula,
) {
    tasks.push(finish(base));
    tasks.push(CloneTask::Visit(body));
}

fn push_binary<'a>(
    tasks: &mut Vec<CloneTask<'a>>,
    base: usize,
    finish: impl FnOnce(usize) -> CloneTask<'a>,
    left: &'a MuCalculusFormula,
    right: &'a MuCalculusFormula,
) {
    tasks.push(finish(base));
    tasks.push(CloneTask::Visit(right));
    tasks.push(CloneTask::Visit(left));
}

fn finish_unary(
    values: &mut Vec<MuCalculusFormula>,
    base: usize,
    build: impl FnOnce(MuCalculusFormula) -> MuCalculusFormula,
) {
    let body = values
        .pop()
        .expect("mu-calculus clone PDA lost a unary body");
    values.truncate(base);
    values.push(build(body));
}

fn finish_binary(
    values: &mut Vec<MuCalculusFormula>,
    base: usize,
    build: impl FnOnce(MuCalculusFormula, MuCalculusFormula) -> MuCalculusFormula,
) {
    let right = values
        .pop()
        .expect("mu-calculus clone PDA lost a right operand");
    let left = values
        .pop()
        .expect("mu-calculus clone PDA lost a left operand");
    values.truncate(base);
    values.push(build(left, right));
}

impl PartialEq for MuCalculusFormula {
    fn eq(&self, other: &Self) -> bool {
        let mut work = vec![(self, other)];
        while let Some((left, right)) = work.pop() {
            match (left, right) {
                (MuCalculusFormula::True, MuCalculusFormula::True)
                | (MuCalculusFormula::False, MuCalculusFormula::False) => {},
                (MuCalculusFormula::Var(a), MuCalculusFormula::Var(b))
                | (MuCalculusFormula::Atom(a), MuCalculusFormula::Atom(b))
                    if a == b => {},
                (MuCalculusFormula::Not(a), MuCalculusFormula::Not(b)) => work.push((a, b)),
                (MuCalculusFormula::And(al, ar), MuCalculusFormula::And(bl, br))
                | (MuCalculusFormula::Or(al, ar), MuCalculusFormula::Or(bl, br)) => {
                    work.push((ar, br));
                    work.push((al, bl));
                },
                (
                    MuCalculusFormula::Diamond { child_idx: ai, body: ab },
                    MuCalculusFormula::Diamond { child_idx: bi, body: bb },
                )
                | (
                    MuCalculusFormula::Box { child_idx: ai, body: ab },
                    MuCalculusFormula::Box { child_idx: bi, body: bb },
                ) if ai == bi => work.push((ab, bb)),
                (
                    MuCalculusFormula::Mu { var: av, body: ab },
                    MuCalculusFormula::Mu { var: bv, body: bb },
                )
                | (
                    MuCalculusFormula::Nu { var: av, body: ab },
                    MuCalculusFormula::Nu { var: bv, body: bb },
                ) if av == bv => work.push((ab, bb)),
                _ => return false,
            }
        }
        true
    }
}

impl Eq for MuCalculusFormula {}

impl Hash for MuCalculusFormula {
    fn hash<H: Hasher>(&self, state: &mut H) {
        let mut work = vec![self];
        while let Some(formula) = work.pop() {
            std::mem::discriminant(formula).hash(state);
            match formula {
                MuCalculusFormula::True | MuCalculusFormula::False => {},
                MuCalculusFormula::Var(value) | MuCalculusFormula::Atom(value) => value.hash(state),
                MuCalculusFormula::Not(body) => work.push(body),
                MuCalculusFormula::And(left, right) | MuCalculusFormula::Or(left, right) => {
                    work.push(right);
                    work.push(left);
                },
                MuCalculusFormula::Diamond { child_idx, body }
                | MuCalculusFormula::Box { child_idx, body } => {
                    child_idx.hash(state);
                    work.push(body);
                },
                MuCalculusFormula::Mu { var, body } | MuCalculusFormula::Nu { var, body } => {
                    var.hash(state);
                    work.push(body);
                },
            }
        }
    }
}

fn take_children(formula: &mut MuCalculusFormula, work: &mut Vec<MuCalculusFormula>) {
    let take = |child: &mut Box<MuCalculusFormula>| {
        *std::mem::replace(child, Box::new(MuCalculusFormula::True))
    };
    match formula {
        MuCalculusFormula::Not(body)
        | MuCalculusFormula::Diamond { body, .. }
        | MuCalculusFormula::Box { body, .. }
        | MuCalculusFormula::Mu { body, .. }
        | MuCalculusFormula::Nu { body, .. } => work.push(take(body)),
        MuCalculusFormula::And(left, right) | MuCalculusFormula::Or(left, right) => {
            work.push(take(left));
            work.push(take(right));
        },
        MuCalculusFormula::Var(_)
        | MuCalculusFormula::True
        | MuCalculusFormula::False
        | MuCalculusFormula::Atom(_) => {},
    }
}

impl Drop for MuCalculusFormula {
    fn drop(&mut self) {
        let mut work = Vec::new();
        take_children(self, &mut work);
        while let Some(mut formula) = work.pop() {
            take_children(&mut formula, &mut work);
        }
    }
}

enum FormatTask<'a> {
    Visit(&'a MuCalculusFormula),
    Text(&'static str),
    Index(usize),
    Name(&'a str),
    Quoted(&'a str),
}

impl fmt::Debug for MuCalculusFormula {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut tasks = vec![FormatTask::Visit(self)];
        while let Some(task) = tasks.pop() {
            match task {
                FormatTask::Text(text) => formatter.write_str(text)?,
                FormatTask::Index(index) => write!(formatter, "{index:?}")?,
                FormatTask::Name(name) => write!(formatter, "{name:?}")?,
                FormatTask::Quoted(name) => write!(formatter, "{name:?}")?,
                FormatTask::Visit(MuCalculusFormula::Var(var)) => {
                    write!(formatter, "Var({var:?})")?
                },
                FormatTask::Visit(MuCalculusFormula::True) => formatter.write_str("True")?,
                FormatTask::Visit(MuCalculusFormula::False) => formatter.write_str("False")?,
                FormatTask::Visit(MuCalculusFormula::Atom(atom)) => {
                    write!(formatter, "Atom({atom:?})")?
                },
                FormatTask::Visit(MuCalculusFormula::Not(body)) => {
                    push_unary_format(&mut tasks, "Not(", body)
                },
                FormatTask::Visit(MuCalculusFormula::And(left, right)) => {
                    push_binary_format(&mut tasks, "And(", left, right)
                },
                FormatTask::Visit(MuCalculusFormula::Or(left, right)) => {
                    push_binary_format(&mut tasks, "Or(", left, right)
                },
                FormatTask::Visit(MuCalculusFormula::Diamond { child_idx, body }) => {
                    tasks.push(FormatTask::Text(" }"));
                    tasks.push(FormatTask::Visit(body));
                    tasks.push(FormatTask::Text(", body: "));
                    tasks.push(FormatTask::Index(*child_idx));
                    tasks.push(FormatTask::Text("Diamond { child_idx: "));
                },
                FormatTask::Visit(MuCalculusFormula::Box { child_idx, body }) => {
                    tasks.push(FormatTask::Text(" }"));
                    tasks.push(FormatTask::Visit(body));
                    tasks.push(FormatTask::Text(", body: "));
                    tasks.push(FormatTask::Index(*child_idx));
                    tasks.push(FormatTask::Text("Box { child_idx: "));
                },
                FormatTask::Visit(MuCalculusFormula::Mu { var, body }) => {
                    push_binding_debug(&mut tasks, "Mu { var: ", var, body)
                },
                FormatTask::Visit(MuCalculusFormula::Nu { var, body }) => {
                    push_binding_debug(&mut tasks, "Nu { var: ", var, body)
                },
            }
        }
        Ok(())
    }
}

fn push_unary_format<'a>(
    tasks: &mut Vec<FormatTask<'a>>,
    open: &'static str,
    body: &'a MuCalculusFormula,
) {
    tasks.push(FormatTask::Text(")"));
    tasks.push(FormatTask::Visit(body));
    tasks.push(FormatTask::Text(open));
}

fn push_binary_format<'a>(
    tasks: &mut Vec<FormatTask<'a>>,
    open: &'static str,
    left: &'a MuCalculusFormula,
    right: &'a MuCalculusFormula,
) {
    tasks.push(FormatTask::Text(")"));
    tasks.push(FormatTask::Visit(right));
    tasks.push(FormatTask::Text(", "));
    tasks.push(FormatTask::Visit(left));
    tasks.push(FormatTask::Text(open));
}

fn push_binding_debug<'a>(
    tasks: &mut Vec<FormatTask<'a>>,
    open: &'static str,
    var: &'a str,
    body: &'a MuCalculusFormula,
) {
    tasks.push(FormatTask::Text(" }"));
    tasks.push(FormatTask::Visit(body));
    tasks.push(FormatTask::Text(", body: "));
    tasks.push(FormatTask::Name(var));
    tasks.push(FormatTask::Text(open));
}

impl fmt::Display for MuCalculusFormula {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut tasks = vec![FormatTask::Visit(self)];
        while let Some(task) = tasks.pop() {
            match task {
                FormatTask::Text(text) => formatter.write_str(text)?,
                FormatTask::Index(index) => write!(formatter, "{index}")?,
                FormatTask::Name(name) => formatter.write_str(name)?,
                FormatTask::Quoted(name) => write!(formatter, "\"{name}\"")?,
                FormatTask::Visit(MuCalculusFormula::Var(var)) => formatter.write_str(var)?,
                FormatTask::Visit(MuCalculusFormula::True) => formatter.write_str("true")?,
                FormatTask::Visit(MuCalculusFormula::False) => formatter.write_str("false")?,
                FormatTask::Visit(MuCalculusFormula::Atom(atom)) => {
                    tasks.push(FormatTask::Quoted(atom));
                },
                FormatTask::Visit(MuCalculusFormula::Not(body)) => {
                    tasks.push(FormatTask::Text(")"));
                    tasks.push(FormatTask::Visit(body));
                    tasks.push(FormatTask::Text("~("));
                },
                FormatTask::Visit(MuCalculusFormula::And(left, right)) => {
                    push_display_binary(&mut tasks, " /\\ ", left, right)
                },
                FormatTask::Visit(MuCalculusFormula::Or(left, right)) => {
                    push_display_binary(&mut tasks, " \\/ ", left, right)
                },
                FormatTask::Visit(MuCalculusFormula::Diamond { child_idx, body }) => {
                    tasks.push(FormatTask::Text(")"));
                    tasks.push(FormatTask::Visit(body));
                    tasks.push(FormatTask::Text(">.("));
                    tasks.push(FormatTask::Index(*child_idx));
                    tasks.push(FormatTask::Text("<"));
                },
                FormatTask::Visit(MuCalculusFormula::Box { child_idx, body }) => {
                    tasks.push(FormatTask::Text(")"));
                    tasks.push(FormatTask::Visit(body));
                    tasks.push(FormatTask::Text("].("));
                    tasks.push(FormatTask::Index(*child_idx));
                    tasks.push(FormatTask::Text("["));
                },
                FormatTask::Visit(MuCalculusFormula::Mu { var, body }) => {
                    push_binding_display(&mut tasks, "mu ", var, body)
                },
                FormatTask::Visit(MuCalculusFormula::Nu { var, body }) => {
                    push_binding_display(&mut tasks, "nu ", var, body)
                },
            }
        }
        Ok(())
    }
}

fn push_display_binary<'a>(
    tasks: &mut Vec<FormatTask<'a>>,
    separator: &'static str,
    left: &'a MuCalculusFormula,
    right: &'a MuCalculusFormula,
) {
    tasks.push(FormatTask::Text(")"));
    tasks.push(FormatTask::Visit(right));
    tasks.push(FormatTask::Text(separator));
    tasks.push(FormatTask::Visit(left));
    tasks.push(FormatTask::Text("("));
}

fn push_binding_display<'a>(
    tasks: &mut Vec<FormatTask<'a>>,
    prefix: &'static str,
    var: &'a str,
    body: &'a MuCalculusFormula,
) {
    tasks.push(FormatTask::Visit(body));
    tasks.push(FormatTask::Text("."));
    tasks.push(FormatTask::Name(var));
    tasks.push(FormatTask::Text(prefix));
}
