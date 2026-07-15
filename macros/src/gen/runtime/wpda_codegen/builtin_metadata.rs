//! Built-in type metadata — shape recognizers and lattice queries.
//!
//! **Stage 3.27d-pre + 3.13 + 3.27d + 3.27f shared infrastructure (2026-04-30).**
//!
//! ## Relocated to `mettail-ast` (2026-06-15)
//!
//! The shape recognizers (`classify_simple_projection_shape`,
//! `classify_unary_prefix_shape`) and their result structs now live in
//! [`mettail_ast::grammar_shapes`] so the auto-injection codegen they support
//! can be replayed at runtime by `mettail_ast::auto_inject::reconstruct_language_def`.
//! They are re-exported here so every existing `mettail-macros`-internal caller
//! (e.g. `super::builtin_metadata::classify_unary_prefix_shape` in the
//! prefix/infix/binder passes and `crate::gen::...::classify_simple_projection_shape`
//! in `semantic_hash.rs` / `native::eval.rs`) keeps resolving unchanged.
//!
//! ## Why a shared module?
//!
//! The shape recognizer for unary-prefix rules and the shape recognizer
//! for simple cross-cat projection rules share the same `tc.len() == 1`
//! single-Simple-param invariant — they branch on one extra check
//! (whether `T == rule.category` or not). Putting them in one module
//! consolidates the underlying invariant test and makes future
//! built-in-aware features have a single place to look.
//!
//! ## Future-proof contract
//!
//! Adding a new built-in type (e.g., `Decimal128`):
//! 1. Add `NativeKind::Decimal128` variant to `ast/src/language.rs`.
//! 2. Update `from_syn_type` arm.
//! 3. Add lossless edges to `BuiltinTypeLattice` impl
//!    (`Decimal128 -> [CanonicalBigRat]` etc.).
//! 4. Update `standard_token_variant`.
//!
//! No code change in `binder.rs`, `prefix.rs`, `infix.rs`, or
//! `semantic_actions.rs` is needed for the shared shape recognizers.

// `SimpleProjectionShape` / `UnaryPrefixShape` are re-exported for API
// completeness (mirrors the pre-relocation surface of this module) even though
// current in-crate callers only name the `classify_*` functions.
#[allow(unused_imports)]
pub use mettail_ast::grammar_shapes::{
    classify_fold_alias_send_shape, classify_fold_alias_shape, classify_simple_projection_shape,
    classify_unary_prefix_shape, FoldAliasSendShape, FoldAliasShape, SimpleProjectionShape,
    UnaryPrefixShape,
};
