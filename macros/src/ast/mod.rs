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


pub mod pattern;
pub mod types;
pub mod grammar;
pub mod language;

pub mod tests;
pub mod validation;