//! Runtime integration generation
//!
//! Generates types that implement `mettail_runtime` traits:
//! - `language` - `{Name}Language` struct implementing `Language` trait
//! - `metadata` - `{Name}Metadata` for REPL introspection
//! - `environment` - `{Name}Env` for storing variable bindings

pub mod language;
pub mod metadata;
pub mod environment;
