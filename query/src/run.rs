//! Run a query string against Ascent results: parse → plan → execute.

use crate::data_source::AscentResultsDataSource;
use crate::executor::{execute, ExecuteError};
use crate::parse::{parse_query, ParseError};
use crate::planner::{PlanError, Planner};
use crate::schema::QuerySchema;
use mettail_runtime::AscentResults;

#[derive(Debug)]
pub enum QueryError {
    Parse(ParseError),
    Plan(PlanError),
    Execute(ExecuteError),
}

impl std::fmt::Display for QueryError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            QueryError::Parse(e) => write!(f, "{}", e),
            QueryError::Plan(e) => write!(f, "{}", e),
            QueryError::Execute(e) => write!(f, "{}", e),
        }
    }
}

impl std::error::Error for QueryError {}

impl From<ParseError> for QueryError {
    fn from(e: ParseError) -> Self {
        QueryError::Parse(e)
    }
}

impl From<PlanError> for QueryError {
    fn from(e: PlanError) -> Self {
        QueryError::Plan(e)
    }
}

impl From<ExecuteError> for QueryError {
    fn from(e: ExecuteError) -> Self {
        QueryError::Execute(e)
    }
}

/// Parse, plan, and execute a single rule over the given Ascent results.
/// Schema is derived from `results.custom_relations`. Returns one row per result tuple (head columns).
pub fn run_query(rule_str: &str, results: &AscentResults) -> Result<Vec<Vec<String>>, QueryError> {
    let schema = QuerySchema::from_custom_relations(&results.custom_relations);
    let query = parse_query(rule_str, &schema)?;
    let plan = Planner::plan(&query)?;
    let data = AscentResultsDataSource::new(results);
    let rows = execute(&plan, &data)?;
    Ok(rows)
}

#[cfg(test)]
mod tests {
    use super::*;
    use mettail_runtime::RelationData;

    #[test]
    fn test_run_query_path_and_negation() {
        let mut custom_relations = std::collections::HashMap::new();
        custom_relations.insert(
            "path".to_string(),
            RelationData {
                param_types: vec!["Proc".into(), "Proc".into()],
                tuples: vec![vec!["a".into(), "b".into()], vec!["a".into(), "c".into()]],
            },
        );
        custom_relations.insert(
            "rw_proc".to_string(),
            RelationData {
                param_types: vec!["Proc".into(), "Proc".into()],
                tuples: vec![vec!["a".into(), "b".into()], vec!["b".into(), "c".into()]],
            },
        );
        let results = AscentResults {
            all_terms: vec![],
            rewrites: vec![],
            equivalences: vec![],
            custom_relations,
        };
        let rows = run_query(
            "query(result) <-- path(a, result), !rw_proc(result, _).",
            &results,
        )
        .unwrap();
        // path(a, result) gives result=b and result=c. !rw_proc(result,_) removes result in rw_proc's first col {a,b}. So only c remains.
        assert_eq!(rows.len(), 1);
        assert_eq!(rows[0], vec!["c"]);
    }
}
