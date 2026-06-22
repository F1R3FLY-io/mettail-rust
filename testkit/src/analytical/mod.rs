//! Analytical test drivers for automata-guided test generation.
//!
//! Each sub-module integrates with a specific prattail analysis module
//! and provides functions that generated `#[test]` code calls.

// Tier 1: TRS analysis (confluence, termination).
//
// The e-graph and theory-morphism wrappers that previously lived here were
// redundant with the live `pipeline/analysis.rs` analyses (egraph/morphism)
// and carried zero consumers, so they were removed (OSLF Phase 7b). Semantic
// (Tier 2) analysis is now the Dovetail/Rho runtime-verification path; the
// legacy CESK/green-thread analyses were retired in P6 and the dead CEGAR
// wrapper was removed alongside the e-graph/morphism wrappers.
pub mod confluence;
pub mod termination;

// Predicated type guard analysis
pub mod guards;
