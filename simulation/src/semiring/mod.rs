//! New semiring types for simulation and analysis.
//!
//! These extend the core semirings in `mettail_prattail::automata::semiring` with
//! carriers tailored for simulation workloads:
//!
//! - [`ExpectationWeight`] — joint weight + expected cost, combined via logsumexp
//! - [`ParikhWeight`] — fixed-dimensional counter vectors for Parikh-image analysis
//! - [`StreamingWeight`] — Welford's online statistics (count, mean, M2, min, max)
//! - [`FreeWeight`] — symbolic semiring expressions as an AST (implements `SemiringRef`)

pub mod expectation;
pub mod free;
pub mod parikh;
pub mod streaming;

pub use expectation::ExpectationWeight;
pub use free::{FreeExpr, FreeWeight};
pub use parikh::ParikhWeight;
pub use streaming::StreamingWeight;
