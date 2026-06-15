//! Analytical test drivers for automata-guided test generation.
//!
//! Each sub-module integrates with a specific prattail analysis module
//! and provides functions that generated `#[test]` code calls.

// Tier 1: TRS analysis (confluence, termination, e-graph, morphism)
pub mod confluence;
pub mod egraph_tests;
pub mod morphism_tests;
pub mod termination;

// Tier 2: Semantic analysis. CESK/green-thread runtime analyses are explicit
// legacy opt-ins; Dovetail/Rho runtime verification is the production path.
pub mod cegar_tests;
#[cfg(feature = "legacy-cesk-runtime")]
pub mod cesk_coverage;
#[cfg(feature = "legacy-cesk-runtime")]
pub mod green_thread_tests;

// Predicated type guard analysis
pub mod guards;
