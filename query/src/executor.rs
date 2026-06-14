//! Executor: run a Plan against a DataSource, return Vec<Vec<String>>.

use crate::ast::{Term, Variable};
use crate::data_source::QueryDataSource;
use crate::operations::{difference, equijoin, project};
use crate::planner::{FilterOp, Plan, Step, TermRef};
use std::collections::HashMap;

#[derive(Debug)]
pub enum ExecuteError {
    RelationNotFound { name: String },
}

impl std::fmt::Display for ExecuteError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ExecuteError::RelationNotFound { name } => {
                write!(f, "Relation '{}' not found", name)
            },
        }
    }
}

impl std::error::Error for ExecuteError {}

pub type ExecuteResult<T> = Result<T, ExecuteError>;

pub fn execute(plan: &Plan, data: &impl QueryDataSource) -> ExecuteResult<Vec<Vec<String>>> {
    let mut current: Vec<Vec<String>> = Vec::new();

    for step in &plan.steps {
        current = execute_step(step, current, data)?;
    }

    Ok(project(current, plan.projection.clone()))
}

fn execute_step(
    step: &Step,
    current: Vec<Vec<String>>,
    data: &impl QueryDataSource,
) -> ExecuteResult<Vec<Vec<String>>> {
    match step {
        Step::Scan { relation, terms } => {
            let rows = filter_relation_rows(data.get_relation(relation), terms);
            Ok(rows)
        },
        Step::Join {
            relation,
            terms,
            left_indices,
            right_indices,
        } => {
            let right = filter_relation_rows(data.get_relation(relation), terms);
            Ok(equijoin(current, right, left_indices.clone(), right_indices.clone()))
        },
        Step::Filter { condition } => Ok(execute_filter(current, condition)),
        Step::Difference { relation, terms, join_indices } => {
            let right = filter_relation_rows(data.get_relation(relation), terms);
            Ok(difference(current, right, join_indices.clone()))
        },
    }
}

fn filter_relation_rows(rows: Vec<Vec<String>>, terms: &[Term]) -> Vec<Vec<String>> {
    rows.into_iter()
        .filter(|row| row_matches_terms(row, terms))
        .collect()
}

fn row_matches_terms(row: &[String], terms: &[Term]) -> bool {
    if row.len() < terms.len() {
        return false;
    }

    let mut variables = HashMap::<&str, &str>::new();
    for (index, term) in terms.iter().enumerate() {
        match term {
            Term::Variable(Variable { name }) => {
                let value = row[index].as_str();
                if let Some(existing) = variables.insert(name.as_str(), value) {
                    if existing != value {
                        return false;
                    }
                }
            },
            Term::Constant(expected) => {
                if !constant_matches(row[index].as_str(), expected) {
                    return false;
                }
            },
            Term::Wildcard => {},
        }
    }

    true
}

fn constant_matches(actual: &str, expected: &str) -> bool {
    actual == expected || unquote_string_constant(expected).as_deref() == Some(actual)
}

fn unquote_string_constant(value: &str) -> Option<String> {
    let inner = value.strip_prefix('"')?.strip_suffix('"')?;
    let mut output = String::with_capacity(inner.len());
    let mut chars = inner.chars();
    while let Some(ch) = chars.next() {
        if ch != '\\' {
            output.push(ch);
            continue;
        }

        let escaped = chars.next()?;
        match escaped {
            '\\' => output.push('\\'),
            '"' => output.push('"'),
            'n' => output.push('\n'),
            'r' => output.push('\r'),
            't' => output.push('\t'),
            other => {
                output.push('\\');
                output.push(other);
            },
        }
    }
    Some(output)
}

fn resolve_term(row: &[String], term: &TermRef) -> String {
    match term {
        TermRef::Col(i) => row[*i].clone(),
        TermRef::Const(s) => s.clone(),
    }
}

fn execute_filter(input: Vec<Vec<String>>, condition: &FilterOp) -> Vec<Vec<String>> {
    let FilterOp::Compare { left, op, right } = condition;
    input
        .into_iter()
        .filter(|row| {
            let l = resolve_term(row, left);
            let r = resolve_term(row, right);
            op.eval_str(&l, &r)
        })
        .collect()
}
