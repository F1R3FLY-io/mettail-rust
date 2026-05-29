//! MeTTaIL Unified Specification (MUS) compiler for `.rho` module files.

pub mod assemble;
pub mod error;
pub mod eval;
pub mod fragments;
pub mod island;
pub mod lexer;
pub mod ntir;
pub mod parity;
pub mod parser;
pub mod project;
pub mod resolve;
pub mod semantics;
pub mod surface;

pub use assemble::compile_entry_with_spaces;
pub use assemble::{compile_entry, compile_language, validate_ntir};
pub use error::{Result, SpecError};
pub use island::{process_island, IslandArtifact, ProcGst};
pub use ntir::Ntir;
pub use parity::{diff_snapshots, language_def_from_monolithic, LanguageSnapshot};
pub use parser::parse_file;
pub use project::{
    parse_projected_language_def, project_rust_file, project_rust_source,
    project_rust_source_with_spaces, verify_projection_sources, write_projected_rs,
    write_projected_rs_with_spaces,
};
pub use resolve::resolve_graph;
