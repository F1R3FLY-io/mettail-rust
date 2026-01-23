//! Runtime integration generation
//!
//! Generates types that implement `mettail_runtime` traits:
//! - `language` - `{Name}Language` struct implementing `Language` trait
//! - `metadata` - `{Name}Metadata` for REPL introspection
//! - `environment` - `{Name}Env` for storing variable bindings

pub mod language;
pub mod metadata;
pub mod environment;

pub use language::generate_language_impl;
pub use metadata::generate_metadata;
pub use environment::generate_environments;
