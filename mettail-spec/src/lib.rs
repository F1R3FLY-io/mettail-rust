//! MeTTaIL Unified Specification (MUS) compiler for `.rho` module files.

pub mod assemble;
pub mod error;
pub mod eval;
pub mod fragments;
pub mod lexer;
pub mod ntir;
pub mod parser;
pub mod resolve;
pub mod semantics;
pub mod surface;

pub use assemble::{compile_entry, compile_language, validate_ntir};
pub use error::{Result, SpecError};
pub use ntir::Ntir;
pub use parser::parse_file;
pub use resolve::resolve_graph;
