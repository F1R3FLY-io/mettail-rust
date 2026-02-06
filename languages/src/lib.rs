// MeTTaIL Language Definitions Library
//
// This crate contains the core language definitions used across examples and the REPL.
// Each language is defined in its own module using the language! macro.

#![allow(
    clippy::cloned_ref_to_slice_refs,
    clippy::type_complexity,
    unused_imports, // generated LALRPOP code may include unused imports
)]

pub mod ambient;
pub mod calculator;
pub mod lambda;
pub mod rhocalc;

// Re-export eqrel for the generated Ascent code
// The generated code uses `#[ds(crate::eqrel)]` which expects eqrel at crate root
pub use ascent_byods_rels::eqrel;

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
