// MeTTaIL Language Definitions Library
//
// This crate contains the core language definitions used across examples and the REPL.
// Each language is defined in its own module using the language! macro.

#![allow(
    clippy::cloned_ref_to_slice_refs,
    clippy::type_complexity,
    unused_imports, // generated parser code may include unused imports
)]

#[cfg(feature = "ambient")]
pub mod ambient;
#[cfg(feature = "calculator")]
pub mod calculator;
#[cfg(feature = "class2hashmapsmoke")]
pub mod class2hashmapsmoke;
#[cfg(feature = "class2multi")]
pub mod class2multi;
#[cfg(feature = "class2optsmoke")]
pub mod class2optsmoke;
#[cfg(feature = "class2smoke")]
pub mod class2smoke;
#[cfg(feature = "class3multi")]
pub mod class3multi;
#[cfg(feature = "class3opt")]
pub mod class3opt;
#[cfg(feature = "guarded-rho")]
pub mod guarded_rho;
#[cfg(feature = "lambda")]
pub mod lambda;
#[cfg(feature = "led-test")]
pub mod led_test;
#[cfg(feature = "optsmoke")]
pub mod optsmoke;
#[cfg(feature = "refinementsmoke")]
pub mod refinementsmoke;
#[cfg(feature = "rhocalc")]
pub mod rhocalc;

// Composition test languages — module order matters for proc-macro registry population.
// fragments and base_lang must compile before their consumers.
#[cfg(feature = "composition")]
pub mod composition;

// Re-export composition language modules at crate root for generated test file access.
// Generated test files use `mettail_languages::{name}::*` which requires crate-root modules.
#[cfg(feature = "composition")]
pub use composition::base_lang as basemath;
#[cfg(feature = "composition")]
pub use composition::extended_lang as extmath;
#[cfg(feature = "composition")]
pub use composition::grammar_import_lang as importedmath;
#[cfg(feature = "composition")]
pub use composition::mixed_lang as mixedmath;
#[cfg(feature = "guarded-rho")]
pub use guarded_rho as guardedrho;
#[cfg(feature = "led-test")]
pub use led_test as ledtest;

/// Proc → [`mettail_runtime::NumericInput`] adapters; lives beside `src/` on purpose.
#[path = "../numeric_dispatch.rs"]
#[cfg(any(feature = "calculator", feature = "rhocalc"))]
mod numeric_dispatch;

// Re-export eqrel for the generated Ascent oracle code.
// The generated code uses `#[ds(crate::eqrel)]` which expects eqrel at crate root.
#[cfg(feature = "oracle-ascent")]
pub use ascent_byods_rels::eqrel;

// Dual-indexed binary relation provider for the explicit Ascent oracle (A-RT03).
// The generated code uses `#[ds(crate::dual_indexed)]` for rw_cat, fold_cat,
// and collection projection relations to ensure O(1) lookups on both columns.
#[cfg(feature = "oracle-ascent")]
pub mod dual_indexed;

// Re-export the aliased macro names from the modules
#[cfg(all(feature = "ambient", feature = "oracle-ascent"))]
pub use ambient::ambient_source;
#[cfg(all(feature = "calculator", feature = "oracle-ascent"))]
pub use calculator::calculator_source;
#[cfg(all(feature = "lambda", feature = "oracle-ascent"))]
pub use lambda::lambda_source;
#[cfg(all(feature = "rhocalc", feature = "oracle-ascent"))]
pub use rhocalc::rhocalc_source;

// Note: Different languages may export types with the same names (e.g., Proc, Term)
// Users should import from specific modules to avoid ambiguity:
//   use mettail_languages::rhocalc::*;
//   use mettail_languages::ambient::*;
//   use mettail_languages::lambda::*;
