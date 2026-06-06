//! Analytical test drivers for automata-guided test generation.
//!
//! Each sub-module integrates with a specific prattail analysis module
//! and provides functions that generated `#[test]` code calls.

// Tier 1: TRS analysis (confluence, termination, e-graph, morphism)
pub mod confluence;
pub mod egraph_tests;
pub mod morphism_tests;
pub mod termination;

// Tier 2: Semantic analysis (CESK, CEGAR, green threads)
pub mod cegar_tests;
pub mod cesk_coverage;
pub mod green_thread_tests;

// Predicated type guard analysis
pub mod guards;
