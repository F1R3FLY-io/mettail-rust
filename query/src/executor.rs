//! Executor: run a Plan against a DataSource, return Vec<Vec<String>>.

use crate::data_source::AscentResultsDataSource;
use crate::operations::{difference, equijoin, project};
use crate::planner::{FilterOp, Plan, Step, TermRef};

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

pub fn execute(plan: &Plan, data: &AscentResultsDataSource<'_>) -> ExecuteResult<Vec<Vec<String>>> {
    let mut current: Vec<Vec<String>> = Vec::new();

    for step in &plan.steps {
        current = execute_step(step, current, data)?;
    }

    Ok(project(current, plan.projection.clone()))
}

fn execute_step(
    step: &Step,
    current: Vec<Vec<String>>,
    data: &AscentResultsDataSource<'_>,
) -> ExecuteResult<Vec<Vec<String>>> {
    match step {
        Step::Scan { relation } => {
            let rows = data.get_relation(relation);
            Ok(rows)
        },
        Step::Join { relation, left_indices, right_indices } => {
            let right = data.get_relation(relation);
            Ok(equijoin(current, right, left_indices.clone(), right_indices.clone()))
        },
        Step::Filter { condition } => Ok(execute_filter(current, condition)),
        Step::Difference { relation, join_indices } => {
            let right = data.get_relation(relation);
            Ok(difference(current, right, join_indices.clone()))
        },
    }
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
