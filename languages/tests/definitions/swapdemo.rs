// Task #11 (extended 2026-07-26): as a library module this definition inherited
// `languages/src/lib.rs`'s crate-level `#![allow(unused_imports, ...)]`. A `#[path]`-included
// module inherits nothing, and each consumer exercises a different slice of the generated
// surface (the parser, the codegen helpers, or neither), so `dead_code` / `unused_imports`
// are expected here rather than a signal. They are allowed at the definition -- the one place
// every consumer shares -- instead of being re-allowed at each `#[path]` site.
#![allow(
    dead_code,
    unused_imports,
    non_local_definitions,
    clippy::crate_in_macro_def,
    clippy::empty_line_after_outer_attr
)]

use mettail_macros::language;

// Epic 4 (R-5) demonstration language: the `Swap(x, y) ~> Pair(y, x)` base rewrite
// over nullary `A`/`B`. This mirrors `SWAP_DEMO_FRAGMENT` in
// `rholang-runtime/tests/rho_net_injection_demo.rs` (the hand-built R-2 precedent),
// promoted to a generated `language!` so the full dovetail-driven Rho σ-injection
// path can be exercised end-to-end in `rholang-runtime/tests/rho_net_equivalence.rs`:
// the generated `dovetail_report_for` resolves + bare-ifies σ (R-4), and the
// generated `rho_net_invocation_from_dovetail_to` builds the σ-injection the runtime
// runs against the installed σ-receiver program.
//
// `Swap(A, B) ≠ Pair(B, A)`, so a positive OUT observation is non-vacuous evidence
// the rewrite fired with the σ Dovetail computed.
language! {
    name: SwapDemo,

    options {
        // Task #11 (extended 2026-07-26): this is a NON-PRODUCTION language definition
        // (`languages/src/` is production-only), so it lives in
        // `languages/tests/definitions/`. The key tells the macro to emit the generated
        // suite INLINE (the opt-in `swapdemo_generated_tests!` wrapper) instead of writing
        // `languages/tests/gen_swapdemo_*.rs`, whose `use mettail_languages::swapdemo::*;`
        // header cannot resolve once the definition has left the library; it also gives the
        // simulation CLI a `#[path]` prologue instead of that same library import.
        hosted_in: "tests/definitions/swapdemo.rs",
        emit_simulator: false,
        emit_blockly: false,
    },

    types {
        Proc
    },

    terms {
        A . |- "A" : Proc ;
        B . |- "B" : Proc ;
        Pair . x:Proc, y:Proc |- "pair" "(" x "," y ")" : Proc ;
        Swap . x:Proc, y:Proc |- "swap" "(" x "," y ")" : Proc ;
    },

    equations {},

    rewrites {
        SwapStep . |- (Swap x y) ~> (Pair y x) ;
    },
}
