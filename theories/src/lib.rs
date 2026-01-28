// MeTTaIL Theory Definitions Library
//
// This crate contains the core theory definitions used across examples and the REPL.
// Each theory is defined in its own module using the theory! macro.

pub mod ambient;
pub mod calculator;
pub mod rhocalc;

// Re-export eqrel for the generated Ascent code
// The generated code uses `#[ds(crate::eqrel)]` which expects eqrel at crate root
pub use ascent_byods_rels::eqrel;

// Re-export the aliased macro names from the modules
// This makes rhocalc_source and ambient_source accessible as mettail_theories::rhocalc_source
pub use ambient::ambient_source;
pub use calculator::calculator_source;
pub use rhocalc::rhocalc_source;

// Note: Both rhocalc and ambient export Proc and Name types
// Users should import from specific modules to avoid ambiguity:
//   use mettail_theories::rhocalc::*;
//   use mettail_theories::ambient::*;
