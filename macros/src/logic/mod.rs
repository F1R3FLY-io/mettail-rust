//! Logic-side code-generation helpers retained after the Ascent runtime
//! backend was retired (P6).
//!
//! The Ascent Datalog rewrite-engine generator (`generate_ascent_source` and
//! its transitive closure) was removed; production rewrite execution is now
//! Dovetail/Rho. What remains are the still-live helpers used by the
//! WPDA/Dovetail codegen path:
//!
//! - `common` — shared category / HOL-domain utilities (`compute_hol_domain_pairs`)
//! - `rules` — freshness-function generation (`generate_freshness_functions`)
//! - `stratification` — predicated-type negation-cycle analysis (`analyze`)
//! - `writer` — generated-source spill / `include!` helpers (`spill_and_include`)
//! - `multi_channel_analysis` — test-only channel-analysis utilities

pub mod common;
#[cfg(test)]
pub mod multi_channel_analysis;
pub mod stratification;
pub mod writer;
pub mod rules;
