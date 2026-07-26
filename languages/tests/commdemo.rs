//! Host binary for the test-hosted `CommDemo` demonstration language.
//!
//! Stage 3b: the canonical single-receive Rholang COMMUNICATION rule (non-linear AC firing).
//!
//! Task #11 (extended 2026-07-26): `CommDemo` is a DEMONSTRATION grammar, not a production
//! language, so its definition lives in `languages/tests/definitions/commdemo.rs`, not in the
//! `languages` library — `languages/src/` is production-only.
//!
//! This file is its DESIGNATED HOST: it declares the definition module and is the one and only
//! invoker of the opt-in `commdemo_generated_tests!` wrapper, which materializes the
//! macro-generated unit / prop / rewrite / analytical sections that used to be written to
//! `languages/tests/gen_commdemo_*.rs`. Every other consumer (`rholang-runtime/tests/rho_net_comm_firing.rs`, `languages/tests/set_automaton_size_optimal.rs`)
//! `#[path]`-includes the same definition WITHOUT invoking the wrapper, so the generated tests
//! exist exactly once across the whole suite.

#[path = "definitions/commdemo.rs"]
mod commdemo;

commdemo::commdemo_generated_tests!(crate::commdemo);
