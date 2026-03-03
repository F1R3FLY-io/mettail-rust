//! Composition test languages exercising all four DSL composition mechanisms.

#![allow(
    non_local_definitions,
    clippy::crate_in_macro_def,
    clippy::empty_line_after_outer_attr
)]

// Phase 1: Fragments (no code emitted, just registry entries)
pub mod fragments;

// Phase 2: Base language for extends/includes tests
pub mod base_lang;

// Phase 2: Extended language (extends: [BaseMath])
pub mod extended_lang;

// Phase 3: Mixin language (mixins: [IntArithFragment, BoolOpsFragment])
pub mod mixed_lang;

// Phase 4: Grammar import language (includes: [BaseMath])
pub mod grammar_import_lang;

// Phase 5: Composed language (compose_languages! { Calculator + Lambda })
pub mod composed_lang;
