//! AST definitions for the theory! macro
//!
//! This module defines the abstract syntax tree for theory definitions,
//! including grammar rules, equations, and rewrite rules.
//!
//! ## Module Structure
//!
//! The types are organized into focused modules:
//! - `term` - Term expressions (Expr)
//! - `syntax` - Syntax patterns for grammar generation (SyntaxExpr, PatternOp)
//! - `typesystem` - Type expressions and context (TypeExpr, TypeContext)
//! - `grammar` - Grammar items and term parameters
//! - `theory` - Top-level theory structure
//!
//! Currently all types are defined in `types.rs` and re-exported through
//! the focused modules. A future refactor will move definitions to
//! their respective modules.


// Focused modules that re-export from types.rs
// In future phases, definitions will migrate here
pub mod term;
pub mod pattern;
pub mod syntax;
pub mod types;
pub mod grammar;
pub mod theory;

pub use term::*;
pub use pattern::*;
pub use syntax::*;
pub use types::*;
pub use grammar::*;
pub use theory::*;

// Tests
#[cfg(test)]
mod tests;