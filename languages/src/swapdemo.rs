#![allow(
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
