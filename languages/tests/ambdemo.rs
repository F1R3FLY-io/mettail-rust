//! Host binary for the test-hosted `AmbDemo` demonstration language.
//!
//! Stage 3d: the Ambient-calculus `OpenRule` STRUCTURAL non-linear AC firing demonstration.
//!
//! Task #11 (extended 2026-07-26): `AmbDemo` is a DEMONSTRATION grammar, not a production
//! language, so its definition lives in `languages/tests/definitions/ambdemo.rs`, not in the
//! `languages` library — `languages/src/` is production-only.
//!
//! This file is its DESIGNATED HOST: it declares the definition module and is the one and only
//! invoker of the opt-in `ambdemo_generated_tests!` wrapper, which materializes the
//! macro-generated unit / prop / rewrite / analytical sections that used to be written to
//! `languages/tests/gen_ambdemo_*.rs`. Every other consumer (`rholang-runtime/tests/rho_net_ambient_firing.rs`, `rholang-codegen/tests/a_s5c_production_language_gates.rs`, `languages/tests/set_automaton_size_optimal.rs`)
//! `#[path]`-includes the same definition WITHOUT invoking the wrapper, so the generated tests
//! exist exactly once across the whole suite.

#[path = "definitions/ambdemo.rs"]
mod ambdemo;

ambdemo::ambdemo_generated_tests!(crate::ambdemo);
