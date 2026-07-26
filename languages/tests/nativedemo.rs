//! Host binary for the test-hosted `NativeDemo` demonstration language.
//!
//! Stage 3e (rho-native): the native-system-process (`![…] fold` PowInt) firing demonstration.
//!
//! Task #11 (extended 2026-07-26): `NativeDemo` is a DEMONSTRATION grammar, not a production
//! language, so its definition lives in `languages/tests/definitions/nativedemo.rs`, not in the
//! `languages` library — `languages/src/` is production-only.
//!
//! This file is its DESIGNATED HOST: it declares the definition module and is the one and only
//! invoker of the opt-in `nativedemo_generated_tests!` wrapper, which materializes the
//! macro-generated unit / prop / rewrite / analytical sections that used to be written to
//! `languages/tests/gen_nativedemo_*.rs`. Every other consumer (`rholang-runtime/tests/rho_net_native_firing.rs`, `languages/tests/set_automaton_size_optimal.rs`)
//! `#[path]`-includes the same definition WITHOUT invoking the wrapper, so the generated tests
//! exist exactly once across the whole suite.

#[path = "definitions/nativedemo.rs"]
mod nativedemo;

nativedemo::nativedemo_generated_tests!(crate::nativedemo);
