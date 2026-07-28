//! Runtime integration generation
//!
//! Generates types that implement `mettail_runtime` traits:
//! - `language` - `{Name}Language` struct implementing `Language` trait
//! - `metadata` - `{Name}Metadata` for REPL introspection
//! - `environment` - `{Name}Env` for storing variable bindings

pub mod binder_congruence;
pub mod disposition;
pub mod dovetail_report;
pub mod environment;
pub mod guard_codegen;
pub mod language;
pub mod metadata;
pub mod numeric_cast_adapter;
#[cfg(test)]
pub mod predicate_lower;
pub mod rho_dataflow;
pub mod rho_invocation;
pub mod wpda_codegen;
