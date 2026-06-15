//! Surface-syntax AST and parser for the MeTTaIL `language!` macro.
//!
//! This crate is a regular library (not `proc-macro = true`). The proc-macro
//! crate `mettail-macros` depends on this crate for its AST definitions; any
//! other crate (REPL, LSP, simulator, doc-gen, fuzzer) can also depend on it
//! to construct or introspect `LanguageDef` values programmatically — for
//! example via `parse2::<LanguageDef>(quote!{ ... })`.
//!
//! The split exists because Cargo's `proc-macro = true` target type forbids
//! non-proc-macro consumers from importing types from a proc-macro crate.

pub mod auto_inject;
pub mod compose;
pub mod fragment;
pub mod grammar;
pub mod grammar_shapes;
pub mod identity;
pub mod language;
pub mod merge;
pub mod pattern;
pub mod registry;
pub mod token_codec;
pub mod types;
pub mod validation;

#[cfg(test)]
pub mod tests;
