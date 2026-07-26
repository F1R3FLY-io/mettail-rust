//! Host binary for the test-hosted `BiCongDemo` demonstration language.
//!
//! Stage 4 S-contextual (sub-slice 2): the 2-ARY-congruence (n-hole contextual join) demonstration.
//!
//! Task #11 (extended 2026-07-26): `BiCongDemo` is a DEMONSTRATION grammar, not a production
//! language, so its definition lives in `languages/tests/definitions/bicongdemo.rs`, not in the
//! `languages` library — `languages/src/` is production-only.
//!
//! This file is its DESIGNATED HOST: it declares the definition module and is the one and only
//! invoker of the opt-in `bicongdemo_generated_tests!` wrapper, which materializes the
//! macro-generated unit / prop / rewrite / analytical sections that used to be written to
//! `languages/tests/gen_bicongdemo_*.rs`. Every other consumer (`rholang-runtime/tests/rho_net_bicong_firing.rs`, `languages/tests/set_automaton_size_optimal.rs`)
//! `#[path]`-includes the same definition WITHOUT invoking the wrapper, so the generated tests
//! exist exactly once across the whole suite.

#[path = "definitions/bicongdemo.rs"]
mod bicongdemo;

bicongdemo::bicongdemo_generated_tests!(crate::bicongdemo);
