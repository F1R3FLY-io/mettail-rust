//! Grammar-only codegen for mettail-languages.
//!
//! This crate is a build-dependency of `mettail-languages`. When it is built,
//! `build.rs` extracts the `language! { ... }` body from each file in
//! `../src/` and generates `language_grammar!` invocations. Those run and write
//! `.lalrpop` files into `../src/generated/`, so that `build.rs` of the parent
//! crate can run LALRPOP on freshly generated grammars.

#![allow(
    non_local_definitions,
    clippy::crate_in_macro_def,
    clippy::empty_line_after_outer_attr
)]

include!(concat!(env!("OUT_DIR"), "/generated.rs"));
