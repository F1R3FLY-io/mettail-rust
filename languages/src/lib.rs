// MeTTaIL Language Definitions Library
//
// This crate contains the core language definitions used across examples and the REPL.
// Each language is defined in its own module using the language! macro.

#![allow(
    clippy::cloned_ref_to_slice_refs,
    clippy::type_complexity,
    unused_imports, // generated parser code may include unused imports
)]

pub mod ambient;
pub mod calculator;
pub mod class2hashmapsmoke;
pub mod class2multi;
pub mod class2optsmoke;
pub mod class2smoke;
pub mod class3multi;
pub mod class3opt;
pub mod guarded_rho;
pub mod lambda;
pub mod led_test;
pub mod optsmoke;
pub mod refinementsmoke;
pub mod rhocalc;

// Composition test languages — module order matters for proc-macro registry population.
// fragments and base_lang must compile before their consumers.
pub mod composition;

// Re-export composition language modules at crate root for generated test file access.
// Generated test files use `mettail_languages::{name}::*` which requires crate-root modules.
pub use composition::base_lang as basemath;
pub use composition::extended_lang as extmath;
pub use composition::mixed_lang as mixedmath;
pub use composition::grammar_import_lang as importedmath;
pub use led_test as ledtest;
pub use guarded_rho as guardedrho;

/// Proc → [`mettail_runtime::NumericInput`] adapters; lives beside `src/` on purpose.
#[path = "../numeric_dispatch.rs"]
mod numeric_dispatch;

// Re-export eqrel for the generated Ascent code
// The generated code uses `#[ds(crate::eqrel)]` which expects eqrel at crate root
pub use ascent_byods_rels::eqrel;

// Dual-indexed binary relation provider (A-RT03).
// The generated code uses `#[ds(crate::dual_indexed)]` for rw_cat, fold_cat,
// and collection projection relations to ensure O(1) lookups on both columns.
pub mod dual_indexed;

// Re-export the aliased macro names from the modules
pub use ambient::ambient_source;
pub use calculator::calculator_source;
pub use lambda::lambda_source;
pub use rhocalc::rhocalc_source;

// Note: Different languages may export types with the same names (e.g., Proc, Term)
// Users should import from specific modules to avoid ambiguity:
//   use mettail_languages::rhocalc::*;
//   use mettail_languages::ambient::*;
//   use mettail_languages::lambda::*;
