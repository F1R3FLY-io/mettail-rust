//! Semiring types for weighted automata.
//!
//! Provides the `Semiring` trait and `TropicalWeight` implementation, adapted
//! from the `lling-llang` WFST library. Only the minimal subset needed for
//! PraTTaIL's weighted lexer pipeline is included here (~100 LOC) rather than
//! depending on the full 95K LOC `lling-llang` crate, preserving the 55s
//! proc-macro build time.
//!
//! ## Tropical Semiring
//!
//! The tropical semiring `(R+ union {+inf}, min, +, +inf, 0.0)` maps naturally
//! to lexer token priority: lower weight = higher priority. The `plus` operation
//! (min) selects the best alternative; `times` (addition) accumulates costs
//! along a path.
//!
//! ## Derived from lling-llang
//!
//! Source: `lling-llang/src/semiring/tropical.rs`
//! License: MIT OR Apache-2.0
//!
//! ## Module organization
//!
//! The weight algebra was split (2026-06-21, behaviour-preserving) out of a single
//! 6,552-line `lib.rs` into focused modules, re-exported here as a flat façade so
//! every `rigail::X` / `mettail::rigail::X` path is unchanged:
//!
//! - [`traits`] — the semiring trait tower (`Semiring`, `SemiringRef`,
//!   `StarSemiring`, …) plus `PackingFactored`.
//! - [`solvers`] — Newton-SCC cyclic-weight closure + matrix-star.
//! - one module per weight type (`tropical`, `counting`, `boolean`, `edit`,
//!   `product`, `context`, `complexity`, `log_entropy`, `nbest`, `viterbi`,
//!   `arctic`, `fuzzy`, `truncation`, `amplitude`).
//! - [`lex_weight`] — lexicographic provenance weight (pre-existing module).

use std::cmp::Ordering;
use std::fmt;

pub mod lex_weight;
pub use lex_weight::LexicographicWeight;

mod traits;
pub use traits::*;

mod solvers;
pub use solvers::*;
// Crate-internal Newton-SCC helpers — re-exported at the crate root only for the
// test suite (they were private `fn`s here before the 2026-06-21 split; `solvers`
// uses them directly, so the re-export is test-only).
#[cfg(test)]
pub(crate) use solvers::{build_differential_matrix, evaluate_f};

mod tropical;
pub use tropical::*;

mod counting;
pub use counting::*;

mod boolean;
pub use boolean::*;

mod edit;
pub use edit::*;

mod product;
pub use product::*;

mod context;
pub use context::*;

mod complexity;
pub use complexity::*;

mod log_entropy;
pub use log_entropy::*;

mod nbest;
pub use nbest::*;

mod viterbi;
pub use viterbi::*;

mod arctic;
pub use arctic::*;

mod fuzzy;
pub use fuzzy::*;

mod truncation;
pub use truncation::*;

mod amplitude;
pub use amplitude::*;

#[cfg(test)]
mod tests;
