//! Heap-backed lifecycle machines for the recursive weighted-MSO formula carrier.

use std::fmt;
use std::hash::{Hash, Hasher};

use super::WeightedMsoFormula;

#[derive(Clone, Copy)]
enum BinaryKind {
    Or,
    And,
}

#[derive(Clone, Copy)]
enum QuantifierKind {
    ExistsFirst,
    ExistsSecond,
    ForallFirst,
    ForallSecond,
}

enum CloneTask<'formula> {
    Visit(&'formula WeightedMsoFormula),
    Binary(BinaryKind),
    Quantifier(QuantifierKind, String),
}

impl Clone for WeightedMsoFormula {
    fn clone(&self) -> Self {
        let mut tasks = vec![CloneTask::Visit(self)];
        let mut values = Vec::new();
        while let Some(task) = tasks.pop() {
            match task {
                CloneTask::Visit(WeightedMsoFormula::Constant(value)) => {
                    values.push(WeightedMsoFormula::Constant(value.clone()));
                },
                CloneTask::Visit(WeightedMsoFormula::AtomicPos { label, var }) => {
                    values.push(WeightedMsoFormula::AtomicPos {
                        label: label.clone(),
                        var: var.clone(),
                    });
                },
                CloneTask::Visit(WeightedMsoFormula::NegAtomicPos { label, var }) => {
                    values.push(WeightedMsoFormula::NegAtomicPos {
                        label: label.clone(),
                        var: var.clone(),
                    });
                },
                CloneTask::Visit(WeightedMsoFormula::Order { x, y }) => {
                    values.push(WeightedMsoFormula::Order { x: x.clone(), y: y.clone() });
                },
                CloneTask::Visit(WeightedMsoFormula::NegOrder { x, y }) => {
                    values.push(WeightedMsoFormula::NegOrder { x: x.clone(), y: y.clone() });
                },
                CloneTask::Visit(WeightedMsoFormula::InSet { var, set_var }) => {
                    values.push(WeightedMsoFormula::InSet {
                        var: var.clone(),
                        set_var: set_var.clone(),
                    });
                },
                CloneTask::Visit(WeightedMsoFormula::NotInSet { var, set_var }) => {
                    values.push(WeightedMsoFormula::NotInSet {
                        var: var.clone(),
                        set_var: set_var.clone(),
                    });
                },
                CloneTask::Visit(WeightedMsoFormula::Or(left, right)) => {
                    push_binary(&mut tasks, BinaryKind::Or, left, right);
                },
                CloneTask::Visit(WeightedMsoFormula::And(left, right)) => {
                    push_binary(&mut tasks, BinaryKind::And, left, right);
                },
                CloneTask::Visit(WeightedMsoFormula::ExistsFirst { var, body }) => {
                    push_quantifier(&mut tasks, QuantifierKind::ExistsFirst, var, body);
                },
                CloneTask::Visit(WeightedMsoFormula::ExistsSecond { var, body }) => {
                    push_quantifier(&mut tasks, QuantifierKind::ExistsSecond, var, body);
                },
                CloneTask::Visit(WeightedMsoFormula::ForallFirst { var, body }) => {
                    push_quantifier(&mut tasks, QuantifierKind::ForallFirst, var, body);
                },
                CloneTask::Visit(WeightedMsoFormula::ForallSecond { var, body }) => {
                    push_quantifier(&mut tasks, QuantifierKind::ForallSecond, var, body);
                },
                CloneTask::Binary(kind) => {
                    let right = values
                        .pop()
                        .expect("weighted-MSO clone PDA lost binary RHS");
                    let left = values
                        .pop()
                        .expect("weighted-MSO clone PDA lost binary LHS");
                    values.push(match kind {
                        BinaryKind::Or => WeightedMsoFormula::Or(Box::new(left), Box::new(right)),
                        BinaryKind::And => WeightedMsoFormula::And(Box::new(left), Box::new(right)),
                    });
                },
                CloneTask::Quantifier(kind, var) => {
                    let body = Box::new(
                        values
                            .pop()
                            .expect("weighted-MSO clone PDA lost quantified body"),
                    );
                    values.push(match kind {
                        QuantifierKind::ExistsFirst => {
                            WeightedMsoFormula::ExistsFirst { var, body }
                        },
                        QuantifierKind::ExistsSecond => {
                            WeightedMsoFormula::ExistsSecond { var, body }
                        },
                        QuantifierKind::ForallFirst => {
                            WeightedMsoFormula::ForallFirst { var, body }
                        },
                        QuantifierKind::ForallSecond => {
                            WeightedMsoFormula::ForallSecond { var, body }
                        },
                    });
                },
            }
        }
        debug_assert_eq!(values.len(), 1);
        values
            .pop()
            .expect("weighted-MSO clone PDA produced no formula")
    }
}

fn push_binary<'formula>(
    tasks: &mut Vec<CloneTask<'formula>>,
    kind: BinaryKind,
    left: &'formula WeightedMsoFormula,
    right: &'formula WeightedMsoFormula,
) {
    tasks.push(CloneTask::Binary(kind));
    tasks.push(CloneTask::Visit(right));
    tasks.push(CloneTask::Visit(left));
}

fn push_quantifier<'formula>(
    tasks: &mut Vec<CloneTask<'formula>>,
    kind: QuantifierKind,
    var: &str,
    body: &'formula WeightedMsoFormula,
) {
    tasks.push(CloneTask::Quantifier(kind, var.to_string()));
    tasks.push(CloneTask::Visit(body));
}

impl PartialEq for WeightedMsoFormula {
    fn eq(&self, other: &Self) -> bool {
        let mut work = vec![(self, other)];
        while let Some((left, right)) = work.pop() {
            match (left, right) {
                (WeightedMsoFormula::Constant(a), WeightedMsoFormula::Constant(b)) if a == b => {},
                (
                    WeightedMsoFormula::AtomicPos { label: al, var: av },
                    WeightedMsoFormula::AtomicPos { label: bl, var: bv },
                )
                | (
                    WeightedMsoFormula::NegAtomicPos { label: al, var: av },
                    WeightedMsoFormula::NegAtomicPos { label: bl, var: bv },
                ) if al == bl && av == bv => {},
                (
                    WeightedMsoFormula::Order { x: ax, y: ay },
                    WeightedMsoFormula::Order { x: bx, y: by },
                )
                | (
                    WeightedMsoFormula::NegOrder { x: ax, y: ay },
                    WeightedMsoFormula::NegOrder { x: bx, y: by },
                ) if ax == bx && ay == by => {},
                (
                    WeightedMsoFormula::InSet { var: av, set_var: asv },
                    WeightedMsoFormula::InSet { var: bv, set_var: bsv },
                )
                | (
                    WeightedMsoFormula::NotInSet { var: av, set_var: asv },
                    WeightedMsoFormula::NotInSet { var: bv, set_var: bsv },
                ) if av == bv && asv == bsv => {},
                (WeightedMsoFormula::Or(al, ar), WeightedMsoFormula::Or(bl, br))
                | (WeightedMsoFormula::And(al, ar), WeightedMsoFormula::And(bl, br)) => {
                    work.push((ar, br));
                    work.push((al, bl));
                },
                (
                    WeightedMsoFormula::ExistsFirst { var: av, body: ab },
                    WeightedMsoFormula::ExistsFirst { var: bv, body: bb },
                )
                | (
                    WeightedMsoFormula::ExistsSecond { var: av, body: ab },
                    WeightedMsoFormula::ExistsSecond { var: bv, body: bb },
                )
                | (
                    WeightedMsoFormula::ForallFirst { var: av, body: ab },
                    WeightedMsoFormula::ForallFirst { var: bv, body: bb },
                )
                | (
                    WeightedMsoFormula::ForallSecond { var: av, body: ab },
                    WeightedMsoFormula::ForallSecond { var: bv, body: bb },
                ) if av == bv => work.push((ab, bb)),
                _ => return false,
            }
        }
        true
    }
}

impl Eq for WeightedMsoFormula {}

impl Hash for WeightedMsoFormula {
    fn hash<H: Hasher>(&self, state: &mut H) {
        let mut work = vec![self];
        while let Some(formula) = work.pop() {
            std::mem::discriminant(formula).hash(state);
            match formula {
                WeightedMsoFormula::Constant(value) => value.hash(state),
                WeightedMsoFormula::AtomicPos { label, var }
                | WeightedMsoFormula::NegAtomicPos { label, var } => {
                    label.hash(state);
                    var.hash(state);
                },
                WeightedMsoFormula::Order { x, y } | WeightedMsoFormula::NegOrder { x, y } => {
                    x.hash(state);
                    y.hash(state);
                },
                WeightedMsoFormula::InSet { var, set_var }
                | WeightedMsoFormula::NotInSet { var, set_var } => {
                    var.hash(state);
                    set_var.hash(state);
                },
                WeightedMsoFormula::Or(left, right) | WeightedMsoFormula::And(left, right) => {
                    work.push(right);
                    work.push(left);
                },
                WeightedMsoFormula::ExistsFirst { var, body }
                | WeightedMsoFormula::ExistsSecond { var, body }
                | WeightedMsoFormula::ForallFirst { var, body }
                | WeightedMsoFormula::ForallSecond { var, body } => {
                    var.hash(state);
                    work.push(body);
                },
            }
        }
    }
}

enum DebugTask<'formula> {
    Visit(&'formula WeightedMsoFormula),
    Text(&'static str),
}

impl fmt::Debug for WeightedMsoFormula {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut tasks = vec![DebugTask::Visit(self)];
        while let Some(task) = tasks.pop() {
            match task {
                DebugTask::Text(text) => formatter.write_str(text)?,
                DebugTask::Visit(WeightedMsoFormula::Constant(value)) => {
                    write!(formatter, "Constant({value:?})")?;
                },
                DebugTask::Visit(WeightedMsoFormula::AtomicPos { label, var }) => {
                    write!(formatter, "AtomicPos {{ label: {label:?}, var: {var:?} }}")?;
                },
                DebugTask::Visit(WeightedMsoFormula::NegAtomicPos { label, var }) => {
                    write!(formatter, "NegAtomicPos {{ label: {label:?}, var: {var:?} }}")?;
                },
                DebugTask::Visit(WeightedMsoFormula::Order { x, y }) => {
                    write!(formatter, "Order {{ x: {x:?}, y: {y:?} }}")?;
                },
                DebugTask::Visit(WeightedMsoFormula::NegOrder { x, y }) => {
                    write!(formatter, "NegOrder {{ x: {x:?}, y: {y:?} }}")?;
                },
                DebugTask::Visit(WeightedMsoFormula::InSet { var, set_var }) => {
                    write!(formatter, "InSet {{ var: {var:?}, set_var: {set_var:?} }}")?;
                },
                DebugTask::Visit(WeightedMsoFormula::NotInSet { var, set_var }) => {
                    write!(formatter, "NotInSet {{ var: {var:?}, set_var: {set_var:?} }}")?;
                },
                DebugTask::Visit(WeightedMsoFormula::Or(left, right)) => {
                    push_binary_debug(&mut tasks, "Or(", left, right);
                },
                DebugTask::Visit(WeightedMsoFormula::And(left, right)) => {
                    push_binary_debug(&mut tasks, "And(", left, right);
                },
                DebugTask::Visit(WeightedMsoFormula::ExistsFirst { var, body }) => {
                    write!(formatter, "ExistsFirst {{ var: {var:?}, body: ")?;
                    push_body_debug(&mut tasks, body);
                },
                DebugTask::Visit(WeightedMsoFormula::ExistsSecond { var, body }) => {
                    write!(formatter, "ExistsSecond {{ var: {var:?}, body: ")?;
                    push_body_debug(&mut tasks, body);
                },
                DebugTask::Visit(WeightedMsoFormula::ForallFirst { var, body }) => {
                    write!(formatter, "ForallFirst {{ var: {var:?}, body: ")?;
                    push_body_debug(&mut tasks, body);
                },
                DebugTask::Visit(WeightedMsoFormula::ForallSecond { var, body }) => {
                    write!(formatter, "ForallSecond {{ var: {var:?}, body: ")?;
                    push_body_debug(&mut tasks, body);
                },
            }
        }
        Ok(())
    }
}

fn push_binary_debug<'formula>(
    tasks: &mut Vec<DebugTask<'formula>>,
    prefix: &'static str,
    left: &'formula WeightedMsoFormula,
    right: &'formula WeightedMsoFormula,
) {
    tasks.push(DebugTask::Text(")"));
    tasks.push(DebugTask::Visit(right));
    tasks.push(DebugTask::Text(", "));
    tasks.push(DebugTask::Visit(left));
    tasks.push(DebugTask::Text(prefix));
}

fn push_body_debug<'formula>(
    tasks: &mut Vec<DebugTask<'formula>>,
    body: &'formula WeightedMsoFormula,
) {
    tasks.push(DebugTask::Text(" }"));
    tasks.push(DebugTask::Visit(body));
}

fn take_children(formula: &mut WeightedMsoFormula, work: &mut Vec<WeightedMsoFormula>) {
    let take = |child: &mut Box<WeightedMsoFormula>| {
        *std::mem::replace(child, Box::new(WeightedMsoFormula::Constant("true".to_string())))
    };
    match formula {
        WeightedMsoFormula::Or(left, right) | WeightedMsoFormula::And(left, right) => {
            work.push(take(left));
            work.push(take(right));
        },
        WeightedMsoFormula::ExistsFirst { body, .. }
        | WeightedMsoFormula::ExistsSecond { body, .. }
        | WeightedMsoFormula::ForallFirst { body, .. }
        | WeightedMsoFormula::ForallSecond { body, .. } => work.push(take(body)),
        WeightedMsoFormula::Constant(_)
        | WeightedMsoFormula::AtomicPos { .. }
        | WeightedMsoFormula::NegAtomicPos { .. }
        | WeightedMsoFormula::Order { .. }
        | WeightedMsoFormula::NegOrder { .. }
        | WeightedMsoFormula::InSet { .. }
        | WeightedMsoFormula::NotInSet { .. } => {},
    }
}

impl Drop for WeightedMsoFormula {
    fn drop(&mut self) {
        let mut work = Vec::new();
        take_children(self, &mut work);
        while let Some(mut formula) = work.pop() {
            take_children(&mut formula, &mut work);
        }
    }
}
