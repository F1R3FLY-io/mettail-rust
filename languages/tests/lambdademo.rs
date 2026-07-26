//! Host binary for the test-hosted `LambdaDemo` demonstration language.
//!
//! Stage 3c: the untyped λ-calculus binder/β-substitution demonstration.
//!
//! Task #11 (extended 2026-07-26): `LambdaDemo` is a DEMONSTRATION grammar, not a production
//! language, so its definition lives in `languages/tests/definitions/lambdademo.rs`, not in the
//! `languages` library — `languages/src/` is production-only.
//!
//! This file is its DESIGNATED HOST: it declares the definition module and is the one and only
//! invoker of the opt-in `lambdademo_generated_tests!` wrapper, which materializes the
//! macro-generated unit / prop / rewrite / analytical sections that used to be written to
//! `languages/tests/gen_lambdademo_*.rs`. Every other consumer (`rholang-runtime/tests/rho_net_beta_firing.rs`, `rho_net_naive_equivalence.rs`, `languages/tests/set_automaton_size_optimal.rs`, `rholang-runtime/benches/support/workloads.rs`)
//! `#[path]`-includes the same definition WITHOUT invoking the wrapper, so the generated tests
//! exist exactly once across the whole suite.

#[path = "definitions/lambdademo.rs"]
mod lambdademo;

lambdademo::lambdademo_generated_tests!(crate::lambdademo);
