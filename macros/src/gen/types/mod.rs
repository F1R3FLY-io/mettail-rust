//! AST type generation
//!
//! Generates Rust enum definitions for language types. Each language type
//! becomes an enum with variants for each constructor, plus auto-generated
//! variants for variables and literals.

pub mod enums;
