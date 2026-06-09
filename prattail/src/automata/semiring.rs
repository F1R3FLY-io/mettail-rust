//! Re-export facade for the weight algebra.
//!
//! The semiring trait hierarchy, all weight types, the Newton-SCC closure
//! (`solve_scc_weights_newton`, `matrix_star_ref`), and `PackingFactored` now
//! live in the standalone, substrate-agnostic `dovetail-semiring` crate (single
//! source of truth). This module preserves the historical
//! `crate::automata::semiring::*` import path for prattail's consumers.
//!
//! FV note: `formal/rocq/mathematical_analyses/theories/SemiringLaws.v` traces
//! `trait Semiring` to this algebra; the definitions now live in
//! `dovetail-semiring/src/lib.rs`.

pub use dovetail_semiring::*;
