//! Host binary for the test-hosted `NativeFoldDemo` demonstration language.
//!
//! Task #11 (extended 2026-07-26): `NativeFoldDemo` is a Stage 3f DEMONSTRATION
//! grammar (its only reducing rule is the native scalar fold `AddInt(a, b) ~> a + b`),
//! so its definition lives in `languages/tests/definitions/nativefolddemo.rs`, not in
//! the `languages` library. `languages/src/` is production-only.
//!
//! This file is its DESIGNATED HOST: it declares the definition module and is the one
//! and only invoker of the opt-in `nativefolddemo_generated_tests!` wrapper, which
//! materializes the macro-generated unit / prop / analytical sections that used to be
//! written to `languages/tests/gen_nativefolddemo_*.rs`. Other consumers
//! (`set_automaton_size_optimal.rs`, `rholang-runtime/tests/rho_net_native_fold_firing.rs`)
//! include the same definition WITHOUT invoking the wrapper, so the generated tests
//! exist exactly once across the whole suite.

#[path = "definitions/nativefolddemo.rs"]
mod nativefolddemo;

nativefolddemo::nativefolddemo_generated_tests!(crate::nativefolddemo);
