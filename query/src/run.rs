//! Run a query string against runtime results: parse → plan → execute.

use crate::data_source::{AscentOracleDataSource, RuntimeReportDataSource};
use crate::executor::{execute, ExecuteError};
use crate::parse::{parse_query, ParseError};
use crate::planner::{PlanError, Planner};
use crate::schema::QuerySchema;
use mettail_runtime::{AscentResults, RuntimeBackendReport};

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

/// Parse, plan, and execute a single rule over explicit Ascent oracle results.
///
/// Schema is derived from `results.custom_relations`. Production callers should
/// use [`run_query_report`] so the query boundary remains
/// `RuntimeBackendReport`-shaped.
pub fn run_ascent_oracle_query(
    rule_str: &str,
    results: &AscentResults,
) -> Result<Vec<Vec<String>>, QueryError> {
    let data = AscentOracleDataSource::new(results);
    run_query_with_schema_and_data(rule_str, data.schema(), &data)
}

/// Parse, plan, and execute a single rule over a runtime backend report.
///
/// Ascent-shaped reports expose their extracted custom relations. Dovetail and
/// Rho-machine reports expose report/observation relations without fabricating
/// `AscentResults`.
pub fn run_query_report(
    rule_str: &str,
    report: &RuntimeBackendReport,
) -> Result<Vec<Vec<String>>, QueryError> {
    let data = RuntimeReportDataSource::new(report);
    run_query_with_schema_and_data(rule_str, data.schema(), &data)
}

fn run_query_with_schema_and_data(
    rule_str: &str,
    schema: QuerySchema,
    data: &impl crate::data_source::QueryDataSource,
) -> Result<Vec<Vec<String>>, QueryError> {
    let query = parse_query(rule_str, &schema)?;
    let plan = Planner::plan(&query)?;
    let rows = execute(&plan, data)?;
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
                tuples: vec![
                    vec!["a".into(), "b".into()],
                    vec!["a".into(), "c".into()],
                    vec!["z".into(), "d".into()],
                ],
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
        let rows = run_ascent_oracle_query(
            "query(result) <-- path(\"a\", result), !rw_proc(result, _).",
            &results,
        )
        .unwrap();
        // path("a", result) gives result=b and result=c. !rw_proc(result,_) removes result in rw_proc's first col {a,b}. So only c remains.
        assert_eq!(rows.len(), 1);
        assert_eq!(rows[0], vec!["c"]);
    }

    #[test]
    fn test_run_query_report_observations() {
        let report = RuntimeBackendReport::try_observations(
            mettail_runtime::RuntimeBackend::RhoMachine,
            mettail_runtime::RuntimeBackendArtifact::RhoNormalizedAst,
            vec![mettail_runtime::RuntimeChannelObservation::new(
                "OUT",
                vec![
                    mettail_runtime::RuntimeObservationValue::Text("rho-backend".to_string()),
                    mettail_runtime::RuntimeObservationValue::Text("other".to_string()),
                ],
            )],
        )
        .expect("sample observation report is valid");

        let rows = run_query_report("query(value) <-- runtime_observation(OUT, value).", &report)
            .expect("runtime observations are queryable");
        assert_eq!(rows, vec![vec!["rho-backend"], vec!["other"]]);
    }

    #[test]
    fn test_run_query_report_dovetail_roots() {
        let report =
            RuntimeBackendReport::try_dovetail(mettail_runtime::RuntimeDovetailRunReport {
                roots: vec![b"root".to_vec()],
                root_ordinals: vec![0],
                terms: vec![mettail_runtime::RuntimeDovetailTermRecord {
                    ordinal: 0,
                    class_id: 7,
                    key: b"root".to_vec(),
                    op_display: "ForComprehension".to_string(),
                    weight_display: "0".to_string(),
                    is_root: true,
                    source_display: None,
                }],
                derivation_edges: Vec::new(),
                rule_firings: Vec::new(),
                rewrite_justifications: Vec::new(),
                declined_folds: Vec::new(),
                completeness: mettail_runtime::RuntimeDovetailCompleteness::Complete,
                graph_kind: mettail_runtime::RuntimeDovetailGraphKind::Derivation,
            })
            .expect("sample Dovetail report is valid");

        let rows = run_query_report("query(op) <-- dovetail_root(_, _, op, _).", &report)
            .expect("Dovetail roots are queryable");
        assert_eq!(rows, vec![vec!["ForComprehension"]]);
    }
}
