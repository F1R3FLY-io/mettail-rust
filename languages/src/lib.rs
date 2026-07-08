// MeTTaIL Language Definitions Library
//
// This crate contains the core language definitions used across examples and the REPL.
// Each language is defined in its own module using the language! macro.

#![allow(
    clippy::cloned_ref_to_slice_refs,
    clippy::type_complexity,
    unused_imports, // generated parser code may include unused imports
)]

#[cfg(feature = "ac-demo")]
pub mod acdemo;
// Stage AC2b: the bag-TRANSFORMING (nested-bag RHS) AC firing demonstration language.
#[cfg(feature = "ac-bag-demo")]
pub mod acbagdemo;
#[cfg(feature = "ambient")]
pub mod ambient;
#[cfg(feature = "appsubst")]
pub mod appsubst;
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
// Stage 3b: the canonical single-receive Rholang COMMUNICATION rule (non-linear AC firing).
#[cfg(feature = "comm-demo")]
pub mod commdemo;
// Stage 3a: the unary-congruence (contextual join) demonstration language.
#[cfg(feature = "ctx-demo")]
pub mod ctxdemo;
// Stage 3c: the untyped λ-calculus binder/β-substitution demonstration language.
#[cfg(feature = "lambda-demo")]
pub mod lambdademo;
// Stage 3e (rho-native): the native-system-process (`![…] fold` PowInt) firing demonstration.
#[cfg(feature = "native-demo")]
pub mod nativedemo;
// PIECE 3: keyword-reservation OPT-OUT fixture (Fortran-style full ambiguity).
#[cfg(feature = "fortran_model")]
pub mod fortran_model;
// PIECE 3: keyword-reservation ENABLED (`auto`) twin of fortran_model.
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
#[cfg(feature = "reserved_model")]
pub mod reserved_model;
#[cfg(feature = "rhocalc")]
pub mod rhocalc;
#[cfg(feature = "swap-demo")]
pub mod swapdemo;

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

// Note: Different languages may export types with the same names (e.g., Proc, Term)
// Users should import from specific modules to avoid ambiguity:
//   use mettail_languages::rhocalc::*;
//   use mettail_languages::ambient::*;
//   use mettail_languages::lambda::*;
