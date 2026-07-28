//! Syntax-layer generation
//!
//! Generates code for text ↔ AST conversion:
//! - `parser/` - PraTTaIL parser generation (text → AST)
//! - `display` - Display trait implementations (AST → text)
//! - `var_inference` - Variable type inference for parser lambda resolution

pub mod debug;
pub mod display;
pub mod parser;
/// ★ CONSTRUCTOR SCHEMA — the inverse of `debug`. `debug` prints a term as text that is NOT
/// Rust (`Arc` erased, enum qualification erased and ambiguous, `Scope`/`HashBag` shapes
/// synthesized); this pass emits the field-type table that lets a tool read that text back and
/// write the term as valid Rust source. Consumed by `testkit`'s proptest-corpus harvester.
pub mod rust_ctor;
/// ★ SURFACE SYNONYMY (2026-07-26) — one denotation, one surface. Derives the alias classes and
/// the inert groupings from the grammar and tells `display` which member to render each through.
pub mod synonymy;
pub mod var_inference;
