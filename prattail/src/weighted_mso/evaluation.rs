//! Stack-safe concrete Boolean evaluation for weighted-MSO formulas.

use std::collections::HashSet;

use crate::automata::semiring::{BooleanWeight, Semiring};

use super::{Assignment, WeightedMsoFormula};

#[derive(Clone, Copy)]
enum FoldKind {
    Or,
    And,
}

enum Task<'formula> {
    Visit(&'formula WeightedMsoFormula),
    Fold(FoldKind),
    FirstStep {
        existential: bool,
        var: &'formula str,
        body: &'formula WeightedMsoFormula,
        next: usize,
        saved: Option<usize>,
        accumulator: BooleanWeight,
    },
    FirstAfter {
        existential: bool,
        var: &'formula str,
        body: &'formula WeightedMsoFormula,
        next: usize,
        saved: Option<usize>,
        accumulator: BooleanWeight,
    },
    SecondStep {
        existential: bool,
        var: &'formula str,
        body: &'formula WeightedMsoFormula,
        bits: Vec<bool>,
        saved: Option<HashSet<usize>>,
        accumulator: BooleanWeight,
    },
    SecondAfter {
        existential: bool,
        var: &'formula str,
        body: &'formula WeightedMsoFormula,
        bits: Vec<bool>,
        saved: Option<HashSet<usize>>,
        accumulator: BooleanWeight,
    },
}

pub(super) fn evaluate(
    formula: &WeightedMsoFormula,
    word: &[String],
    assignment: &Assignment,
) -> BooleanWeight {
    let mut environment = assignment.clone();
    let mut tasks = vec![Task::Visit(formula)];
    let mut values = Vec::new();
    while let Some(task) = tasks.pop() {
        match task {
            Task::Visit(WeightedMsoFormula::Constant(value)) => {
                values.push(if matches!(value.as_str(), "false" | "0") {
                    BooleanWeight::zero()
                } else {
                    BooleanWeight::one()
                })
            },
            Task::Visit(WeightedMsoFormula::AtomicPos { label, var }) => {
                let position = environment
                    .first_order
                    .get(var)
                    .unwrap_or_else(|| panic!("unbound first-order variable: {var}"));
                values.push(weight(*position < word.len() && word[*position] == *label));
            },
            Task::Visit(WeightedMsoFormula::NegAtomicPos { label, var }) => {
                let position = environment
                    .first_order
                    .get(var)
                    .unwrap_or_else(|| panic!("unbound first-order variable: {var}"));
                values.push(weight(!(*position < word.len() && word[*position] == *label)));
            },
            Task::Visit(WeightedMsoFormula::Order { x, y }) => {
                let left = environment
                    .first_order
                    .get(x)
                    .unwrap_or_else(|| panic!("unbound first-order variable: {x}"));
                let right = environment
                    .first_order
                    .get(y)
                    .unwrap_or_else(|| panic!("unbound first-order variable: {y}"));
                values.push(weight(left <= right));
            },
            Task::Visit(WeightedMsoFormula::NegOrder { x, y }) => {
                let left = environment
                    .first_order
                    .get(x)
                    .unwrap_or_else(|| panic!("unbound first-order variable: {x}"));
                let right = environment
                    .first_order
                    .get(y)
                    .unwrap_or_else(|| panic!("unbound first-order variable: {y}"));
                values.push(weight(left > right));
            },
            Task::Visit(WeightedMsoFormula::InSet { var, set_var })
            | Task::Visit(WeightedMsoFormula::NotInSet { var, set_var }) => {
                let position = environment
                    .first_order
                    .get(var)
                    .unwrap_or_else(|| panic!("unbound first-order variable: {var}"));
                let set = environment
                    .second_order
                    .get(set_var)
                    .unwrap_or_else(|| panic!("unbound second-order variable: {set_var}"));
                let contains = set.contains(position);
                values.push(weight(match task {
                    Task::Visit(WeightedMsoFormula::InSet { .. }) => contains,
                    Task::Visit(WeightedMsoFormula::NotInSet { .. }) => !contains,
                    _ => unreachable!(),
                }));
            },
            Task::Visit(WeightedMsoFormula::Or(left, right)) => {
                push_fold(&mut tasks, FoldKind::Or, left, right);
            },
            Task::Visit(WeightedMsoFormula::And(left, right)) => {
                push_fold(&mut tasks, FoldKind::And, left, right);
            },
            Task::Visit(WeightedMsoFormula::ExistsFirst { var, body }) => {
                tasks.push(Task::FirstStep {
                    existential: true,
                    var,
                    body,
                    next: 0,
                    saved: environment.first_order.get(var).copied(),
                    accumulator: BooleanWeight::zero(),
                });
            },
            Task::Visit(WeightedMsoFormula::ForallFirst { var, body }) => {
                tasks.push(Task::FirstStep {
                    existential: false,
                    var,
                    body,
                    next: 0,
                    saved: environment.first_order.get(var).copied(),
                    accumulator: BooleanWeight::one(),
                });
            },
            Task::Visit(WeightedMsoFormula::ExistsSecond { var, body }) => {
                tasks.push(Task::SecondStep {
                    existential: true,
                    var,
                    body,
                    bits: vec![false; word.len()],
                    saved: environment.second_order.get(var).cloned(),
                    accumulator: BooleanWeight::zero(),
                });
            },
            Task::Visit(WeightedMsoFormula::ForallSecond { var, body }) => {
                tasks.push(Task::SecondStep {
                    existential: false,
                    var,
                    body,
                    bits: vec![false; word.len()],
                    saved: environment.second_order.get(var).cloned(),
                    accumulator: BooleanWeight::one(),
                });
            },
            Task::Fold(kind) => {
                let right = values
                    .pop()
                    .expect("weighted-MSO evaluator lost binary RHS");
                let left = values
                    .pop()
                    .expect("weighted-MSO evaluator lost binary LHS");
                values.push(match kind {
                    FoldKind::Or => left.plus(&right),
                    FoldKind::And => left.times(&right),
                });
            },
            Task::FirstStep {
                existential,
                var,
                body,
                next,
                saved,
                accumulator,
            } => {
                if next == word.len() {
                    restore_first(&mut environment, var, saved);
                    values.push(accumulator);
                } else {
                    environment.first_order.insert(var.to_string(), next);
                    tasks.push(Task::FirstAfter {
                        existential,
                        var,
                        body,
                        next: next + 1,
                        saved,
                        accumulator,
                    });
                    tasks.push(Task::Visit(body));
                }
            },
            Task::FirstAfter {
                existential,
                var,
                body,
                next,
                saved,
                accumulator,
            } => {
                let body_value = values
                    .pop()
                    .expect("weighted-MSO evaluator lost first-order body value");
                let accumulator = combine(existential, accumulator, body_value);
                if short_circuits(existential, accumulator) {
                    restore_first(&mut environment, var, saved);
                    values.push(accumulator);
                } else {
                    tasks.push(Task::FirstStep {
                        existential,
                        var,
                        body,
                        next,
                        saved,
                        accumulator,
                    });
                }
            },
            Task::SecondStep {
                existential,
                var,
                body,
                bits,
                saved,
                accumulator,
            } => {
                let subset = bits
                    .iter()
                    .enumerate()
                    .filter_map(|(index, included)| included.then_some(index))
                    .collect();
                environment.second_order.insert(var.to_string(), subset);
                tasks.push(Task::SecondAfter {
                    existential,
                    var,
                    body,
                    bits,
                    saved,
                    accumulator,
                });
                tasks.push(Task::Visit(body));
            },
            Task::SecondAfter {
                existential,
                var,
                body,
                mut bits,
                saved,
                accumulator,
            } => {
                let body_value = values
                    .pop()
                    .expect("weighted-MSO evaluator lost second-order body value");
                let accumulator = combine(existential, accumulator, body_value);
                if short_circuits(existential, accumulator) || !increment_subset(&mut bits) {
                    restore_second(&mut environment, var, saved);
                    values.push(accumulator);
                } else {
                    tasks.push(Task::SecondStep {
                        existential,
                        var,
                        body,
                        bits,
                        saved,
                        accumulator,
                    });
                }
            },
        }
    }
    debug_assert_eq!(values.len(), 1);
    values
        .pop()
        .expect("weighted-MSO evaluator produced no value")
}

fn push_fold<'formula>(
    tasks: &mut Vec<Task<'formula>>,
    kind: FoldKind,
    left: &'formula WeightedMsoFormula,
    right: &'formula WeightedMsoFormula,
) {
    tasks.push(Task::Fold(kind));
    tasks.push(Task::Visit(right));
    tasks.push(Task::Visit(left));
}

fn weight(value: bool) -> BooleanWeight {
    if value {
        BooleanWeight::one()
    } else {
        BooleanWeight::zero()
    }
}

fn combine(existential: bool, accumulator: BooleanWeight, value: BooleanWeight) -> BooleanWeight {
    if existential {
        accumulator.plus(&value)
    } else {
        accumulator.times(&value)
    }
}

fn short_circuits(existential: bool, value: BooleanWeight) -> bool {
    if existential {
        value.is_one()
    } else {
        value.is_zero()
    }
}

fn increment_subset(bits: &mut [bool]) -> bool {
    for bit in bits {
        if *bit {
            *bit = false;
        } else {
            *bit = true;
            return true;
        }
    }
    false
}

fn restore_first(environment: &mut Assignment, var: &str, saved: Option<usize>) {
    if let Some(value) = saved {
        environment.first_order.insert(var.to_string(), value);
    } else {
        environment.first_order.remove(var);
    }
}

fn restore_second(environment: &mut Assignment, var: &str, saved: Option<HashSet<usize>>) {
    if let Some(value) = saved {
        environment.second_order.insert(var.to_string(), value);
    } else {
        environment.second_order.remove(var);
    }
}
