//! Syntax-layer generation
//!
//! Generates code for text ↔ AST conversion:
//! - `parser/` - LALRPOP grammar generation (text → AST)
//! - `display` - Display trait implementations (AST → text)
//! - `var_inference` - Variable type inference for parser lambda resolution

pub mod parser;
pub mod display;
pub mod var_inference;

pub use display::generate_display;
pub use var_inference::generate_var_category_inference;
