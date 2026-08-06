//! Heap-backed lifecycle and debug-formatting machines for guard formulas.

use std::fmt;

use super::GuardFormula;

#[derive(Clone, Copy)]
enum BinaryKind {
    And,
    Or,
    Implies,
}

enum CloneTask<'formula> {
    Visit(&'formula GuardFormula),
    Not,
    Binary(BinaryKind),
}

impl Clone for GuardFormula {
    fn clone(&self) -> Self {
        let mut tasks = vec![CloneTask::Visit(self)];
        let mut values = Vec::new();
        while let Some(task) = tasks.pop() {
            match task {
                CloneTask::Visit(GuardFormula::True) => values.push(GuardFormula::True),
                CloneTask::Visit(GuardFormula::False) => values.push(GuardFormula::False),
                CloneTask::Visit(GuardFormula::Linear(pred)) => {
                    values.push(GuardFormula::Linear(pred.clone()));
                },
                CloneTask::Visit(GuardFormula::Prop(test)) => {
                    values.push(GuardFormula::Prop(test.clone()));
                },
                CloneTask::Visit(GuardFormula::Scalar { var, pred }) => {
                    values.push(GuardFormula::Scalar { var: *var, pred: pred.clone() });
                },
                CloneTask::Visit(GuardFormula::ScalarRel { op, left, right }) => {
                    values.push(GuardFormula::ScalarRel {
                        op: *op,
                        left: left.clone(),
                        right: right.clone(),
                    });
                },
                CloneTask::Visit(GuardFormula::And(left, right)) => {
                    push_binary(&mut tasks, BinaryKind::And, left, right);
                },
                CloneTask::Visit(GuardFormula::Or(left, right)) => {
                    push_binary(&mut tasks, BinaryKind::Or, left, right);
                },
                CloneTask::Visit(GuardFormula::Implies(left, right)) => {
                    push_binary(&mut tasks, BinaryKind::Implies, left, right);
                },
                CloneTask::Visit(GuardFormula::Not(inner)) => {
                    tasks.push(CloneTask::Not);
                    tasks.push(CloneTask::Visit(inner));
                },
                CloneTask::Visit(GuardFormula::Atom(atom)) => {
                    values.push(GuardFormula::Atom(*atom));
                },
                CloneTask::Not => {
                    let inner = values.pop().expect("guard formula clone PDA lost negand");
                    values.push(GuardFormula::Not(Box::new(inner)));
                },
                CloneTask::Binary(kind) => {
                    let right = values
                        .pop()
                        .expect("guard formula clone PDA lost binary RHS");
                    let left = values
                        .pop()
                        .expect("guard formula clone PDA lost binary LHS");
                    values.push(match kind {
                        BinaryKind::And => GuardFormula::And(Box::new(left), Box::new(right)),
                        BinaryKind::Or => GuardFormula::Or(Box::new(left), Box::new(right)),
                        BinaryKind::Implies => {
                            GuardFormula::Implies(Box::new(left), Box::new(right))
                        },
                    });
                },
            }
        }
        debug_assert_eq!(values.len(), 1);
        values
            .pop()
            .expect("guard formula clone PDA produced no value")
    }
}

fn push_binary<'formula>(
    tasks: &mut Vec<CloneTask<'formula>>,
    kind: BinaryKind,
    left: &'formula GuardFormula,
    right: &'formula GuardFormula,
) {
    tasks.push(CloneTask::Binary(kind));
    tasks.push(CloneTask::Visit(right));
    tasks.push(CloneTask::Visit(left));
}

impl PartialEq for GuardFormula {
    fn eq(&self, other: &Self) -> bool {
        let mut work = vec![(self, other)];
        while let Some((left, right)) = work.pop() {
            match (left, right) {
                (GuardFormula::True, GuardFormula::True)
                | (GuardFormula::False, GuardFormula::False) => {},
                (GuardFormula::Linear(a), GuardFormula::Linear(b)) if a == b => {},
                (GuardFormula::Prop(a), GuardFormula::Prop(b)) if a == b => {},
                (
                    GuardFormula::Scalar { var: av, pred: ap },
                    GuardFormula::Scalar { var: bv, pred: bp },
                ) if av == bv && ap == bp => {},
                (
                    GuardFormula::ScalarRel { op: ao, left: al, right: ar },
                    GuardFormula::ScalarRel { op: bo, left: bl, right: br },
                ) if ao == bo && al == bl && ar == br => {},
                (GuardFormula::And(al, ar), GuardFormula::And(bl, br))
                | (GuardFormula::Or(al, ar), GuardFormula::Or(bl, br))
                | (GuardFormula::Implies(al, ar), GuardFormula::Implies(bl, br)) => {
                    work.push((ar, br));
                    work.push((al, bl));
                },
                (GuardFormula::Not(a), GuardFormula::Not(b)) => work.push((a, b)),
                (GuardFormula::Atom(a), GuardFormula::Atom(b)) if a == b => {},
                _ => return false,
            }
        }
        true
    }
}

impl Eq for GuardFormula {}

fn take_children(formula: &mut GuardFormula, work: &mut Vec<GuardFormula>) {
    let take =
        |child: &mut Box<GuardFormula>| *std::mem::replace(child, Box::new(GuardFormula::True));
    match formula {
        GuardFormula::And(left, right)
        | GuardFormula::Or(left, right)
        | GuardFormula::Implies(left, right) => {
            work.push(take(left));
            work.push(take(right));
        },
        GuardFormula::Not(inner) => work.push(take(inner)),
        GuardFormula::True
        | GuardFormula::False
        | GuardFormula::Linear(_)
        | GuardFormula::Prop(_)
        | GuardFormula::Scalar { .. }
        | GuardFormula::ScalarRel { .. }
        | GuardFormula::Atom(_) => {},
    }
}

impl Drop for GuardFormula {
    fn drop(&mut self) {
        let mut work = Vec::new();
        take_children(self, &mut work);
        while let Some(mut formula) = work.pop() {
            take_children(&mut formula, &mut work);
        }
    }
}

enum DebugTask<'formula> {
    Visit(&'formula GuardFormula),
    Text(&'static str),
}

impl fmt::Debug for GuardFormula {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut tasks = vec![DebugTask::Visit(self)];
        while let Some(task) = tasks.pop() {
            match task {
                DebugTask::Text(text) => formatter.write_str(text)?,
                DebugTask::Visit(GuardFormula::True) => formatter.write_str("True")?,
                DebugTask::Visit(GuardFormula::False) => formatter.write_str("False")?,
                DebugTask::Visit(GuardFormula::Linear(pred)) => {
                    write!(formatter, "Linear({pred:?})")?;
                },
                DebugTask::Visit(GuardFormula::Prop(test)) => {
                    write!(formatter, "Prop({test:?})")?;
                },
                DebugTask::Visit(GuardFormula::Scalar { var, pred }) => {
                    write!(formatter, "Scalar {{ var: {var:?}, pred: {pred:?} }}")?;
                },
                DebugTask::Visit(GuardFormula::ScalarRel { op, left, right }) => {
                    write!(
                        formatter,
                        "ScalarRel {{ op: {op:?}, left: {left:?}, right: {right:?} }}"
                    )?;
                },
                DebugTask::Visit(GuardFormula::And(left, right)) => {
                    push_binary_debug(&mut tasks, "And(", left, right);
                },
                DebugTask::Visit(GuardFormula::Or(left, right)) => {
                    push_binary_debug(&mut tasks, "Or(", left, right);
                },
                DebugTask::Visit(GuardFormula::Implies(left, right)) => {
                    push_binary_debug(&mut tasks, "Implies(", left, right);
                },
                DebugTask::Visit(GuardFormula::Not(inner)) => {
                    tasks.push(DebugTask::Text(")"));
                    tasks.push(DebugTask::Visit(inner));
                    tasks.push(DebugTask::Text("Not("));
                },
                DebugTask::Visit(GuardFormula::Atom(atom)) => {
                    write!(formatter, "Atom({atom:?})")?;
                },
            }
        }
        Ok(())
    }
}

fn push_binary_debug<'formula>(
    tasks: &mut Vec<DebugTask<'formula>>,
    prefix: &'static str,
    left: &'formula GuardFormula,
    right: &'formula GuardFormula,
) {
    tasks.push(DebugTask::Text(")"));
    tasks.push(DebugTask::Visit(right));
    tasks.push(DebugTask::Text(", "));
    tasks.push(DebugTask::Visit(left));
    tasks.push(DebugTask::Text(prefix));
}
