//! Syntax-layer generation
//!
//! Generates code for text ↔ AST conversion:
//! - `parser/` - PraTTaIL parser generation (text → AST)
//! - `display` - Display trait implementations (AST → text)
//! - `var_inference` - Variable type inference for parser lambda resolution

pub mod debug;
pub mod display;
pub mod parser;
/// ★ SURFACE SYNONYMY (2026-07-26) — one denotation, one surface. Derives the alias classes and
/// the inert groupings from the grammar and tells `display` which member to render each through.
pub mod synonymy;
pub mod var_inference;
