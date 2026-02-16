//! Syntax-layer generation
//!
//! Generates code for text ↔ AST conversion:
//! - `parser/` - PraTTaIL parser generation (text → AST)
//! - `display` - Display trait implementations (AST → text)
//! - `var_inference` - Variable type inference for parser lambda resolution

pub mod display;
pub mod parser;
pub mod var_inference;
