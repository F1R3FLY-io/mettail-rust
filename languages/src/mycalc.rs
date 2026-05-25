//! MyCalc language generated from `.rho` specs (see `specs/mycalc/` and `build.rs`).

#![allow(
    non_local_definitions,
    clippy::crate_in_macro_def,
    clippy::empty_line_after_outer_attr
)]

include!(concat!(env!("OUT_DIR"), "/mycalc_lang.rs"));
