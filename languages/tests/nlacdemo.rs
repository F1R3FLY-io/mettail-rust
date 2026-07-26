//! Host binary for the test-hosted `NlAcDemo` demonstration language.
//!
//! Stage 4 S-AC (AC3): the NON-LINEAR `{x, x, ...rest}` bare-var AC firing demonstration.
//!
//! Task #11 (extended 2026-07-26): `NlAcDemo` is a DEMONSTRATION grammar, not a production
//! language, so its definition lives in `languages/tests/definitions/nlacdemo.rs`, not in the
//! `languages` library — `languages/src/` is production-only.
//!
//! This file is its DESIGNATED HOST: it declares the definition module and is the one and only
//! invoker of the opt-in `nlacdemo_generated_tests!` wrapper, which materializes the
//! macro-generated unit / prop / rewrite / analytical sections that used to be written to
//! `languages/tests/gen_nlacdemo_*.rs`. Every other consumer (`rholang-runtime/tests/rho_net_nl_ac_firing.rs`, `languages/tests/set_automaton_size_optimal.rs`)
//! `#[path]`-includes the same definition WITHOUT invoking the wrapper, so the generated tests
//! exist exactly once across the whole suite.

#[path = "definitions/nlacdemo.rs"]
mod nlacdemo;

nlacdemo::nlacdemo_generated_tests!(crate::nlacdemo);
