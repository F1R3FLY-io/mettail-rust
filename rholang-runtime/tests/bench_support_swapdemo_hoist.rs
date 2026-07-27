//! Task #11 (extended 2026-07-26) — the RELOCATED B3 warm-mode-hoist test.
//!
//! This test used to be a `#[cfg(test)]` unit test inside `rholang-runtime/src/bench_support.rs`.
//! It is LANGUAGE-scoped (it asserts that `compile_bench_language` hoists a language's compile
//! exactly once and that the artifacts share one fingerprint), so it survives `SwapDemo`'s move
//! out of `languages/src/` — but it cannot stay in the library crate.
//!
//! Why: `SwapDemo` is now TEST-HOSTED (`languages/tests/definitions/swapdemo.rs`), so a consumer
//! must `#[path]`-include the definition and expand `language!` in its own crate. The expansion
//! emits `unsafe` blocks (the iterative comparison / hashing walkers) and `unsafe impl Send/Sync`,
//! and `rholang-runtime/src/lib.rs` carries `#![forbid(unsafe_code)]` — a `forbid` level that an
//! inner `#![allow]` deliberately cannot override. An integration-test crate root has its own lint
//! levels, so the include is legal here and the assertions are unchanged.
//!
//! ## The silent-`cfg` trap this file is subject to
//!
//! A `cfg` inside a macro expansion resolves against the crate BEING COMPILED. The expansion's
//! `#[cfg(feature = "rho-codegen")]` / `#[cfg(feature = "dovetail-codegen")]` blocks therefore
//! resolve against `rholang-runtime`, not `mettail-languages`. Both features are declared in this
//! crate's manifest and `swap-demo-runtime` turns them on; omitting them would NOT fail loudly —
//! the gated blocks would simply vanish.
//!
//! This binary is a CONSUMER, not `SwapDemo`'s designated host (`languages/tests/swapdemo.rs`
//! is), so it does not invoke the `swapdemo_generated_tests!` wrapper.
//! `bench_support` itself is quarantined behind `bench-naive-baseline`, so this file
//! carries BOTH gates: the module must exist AND `SwapDemo`'s codegen surface must be on.
#![cfg(all(feature = "swap-demo-runtime", feature = "bench-naive-baseline"))]

use mettail_rholang_runtime::bench_support::{compile_bench_language, count_receive_nodes};

#[path = "../../languages/tests/definitions/swapdemo.rs"]
mod swapdemo;

use swapdemo::SwapDemoLanguage;

/// (B3) The warm-mode hoist compiles SwapDemo ONCE: the ruleset and the
/// plan share one fingerprint, the installed σ-receiver program is a real
/// receiver network, and the compiled artifacts are reusable by reference.
#[test]
fn compile_bench_language_hoists_swapdemo_once() {
    use mettail_runtime::Language;

    let source = SwapDemoLanguage
        .metadata()
        .definition_source()
        .expect("the generated SwapDemo exposes its definition_source");
    let compiled =
        compile_bench_language(source).expect("SwapDemo compiles through the warm-mode hoist");
    assert_eq!(
        compiled.ruleset.language_fingerprint,
        compiled.lowered.definition_fingerprint(),
        "the hoisted ruleset and lowering share ONE fingerprint"
    );
    assert!(
        compiled.ruleset.automaton.view().entry_count() >= 1,
        "SwapDemo compiles at least the SwapStep entry"
    );
    assert!(
        count_receive_nodes(&compiled.installed_program) >= 1,
        "the installed program is a real σ-receiver network"
    );
    assert!(!compiled.def.rewrites.is_empty(), "the reconstructed def carries its rewrites");
}
