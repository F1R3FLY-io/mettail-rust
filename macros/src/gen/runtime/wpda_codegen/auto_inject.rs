//! Auto-injection codegen — emit synthetic cross-cat injection rules
//! for lossless built-in promotion edges.
//!
//! ## Relocated to `mettail-ast` (2026-06-15)
//!
//! The auto-injection engine moved into [`mettail_ast::auto_inject`] so the
//! exact macro-time augmentation of a `LanguageDef` (composition +
//! auto-injection) can be replayed at runtime by
//! [`mettail_ast::auto_inject::reconstruct_language_def`]. The macro computes
//! the definition fingerprint *after* this augmentation, so hosting it in
//! `mettail-ast` lets a generated language's `definition_source()` be
//! re-augmented to the exact same fingerprint without depending on the
//! proc-macro crate.
//!
//! `emit_auto_injection_rules` + `AutoInjectionOutput` are re-exported here so
//! `crate::gen::runtime::wpda_codegen::auto_inject::emit_auto_injection_rules`
//! at `macros/src/lib.rs` keeps resolving unchanged.
//!
//! See [`mettail_ast::auto_inject`] for the full algorithm, the demand-driven
//! emission policy, and the synthetic congruence / cast-canonicalization
//! rewrites.

// `AutoInjectionOutput` is re-exported for API completeness (mirrors the
// pre-relocation surface of this module) even though current in-crate callers
// only name `emit_auto_injection_rules`.
#[allow(unused_imports)]
pub use mettail_ast::auto_inject::{emit_auto_injection_rules, AutoInjectionOutput};
