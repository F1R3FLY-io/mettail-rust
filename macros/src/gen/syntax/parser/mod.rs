//! Parser generation (LALRPOP integration)
//!
//! Generates LALRPOP grammar files and writes them to the filesystem.

mod lalrpop;
mod writer;

pub use lalrpop::*;
pub use writer::*;
