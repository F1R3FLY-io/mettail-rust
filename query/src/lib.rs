//! Runtime query interpreter for MeTTaIL: parse and execute Datalog-style rules over runtime reports.

pub mod ast;
pub mod data_source;
pub mod executor;
pub mod operations;
pub mod parse;
pub mod planner;
pub mod run;
pub mod schema;

pub use ast::{BodyAtom, CompareOp, IfExpr, Query, Term, Variable};
pub use data_source::{AscentOracleDataSource, QueryDataSource, RuntimeReportDataSource};
pub use executor::{execute, ExecuteError};
pub use parse::{parse_query, pre_parse_rule, ParseError, PreParseError, PreParsedRule};
pub use planner::{Plan, PlanError, Planner, Step};
pub use run::{run_ascent_oracle_query, run_query_report, QueryError};
pub use schema::QuerySchema;
