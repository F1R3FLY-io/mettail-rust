#![allow(
    non_local_definitions,
    clippy::crate_in_macro_def,
    clippy::empty_line_after_outer_attr
)]

use mettail_macros::language;

// Stage 3a demonstration language: a UNARY CONGRUENCE (contextual) rewrite
// `WrapCong: | S ~> T |- Wrap(S) ~> Wrap(T)` closes the context `Wrap(_)` around the inner
// premise `S ~> T`, whose mechanism is the base rewrite `Flip: Swap(x, y) ~> Pair(y, x)`.
//
// This is the FIRST bundled language shape that exercises the in-Rho CONTEXTUAL firing path
// (Stage 3a) end-to-end: SwapDemo has only a base rewrite, AcDemo only an AC rewrite, and
// RhoCalc's sole congruence (`ParCong`) is over an AC `PPar` bag — too entangled for the first
// slice (it stays fail-closed). A clean unary constructor context `Wrap(_)` isolates INV-6 (a
// contextual rewrite fires as an atomic JOIN) without AC.
//
// Promoted to a generated `language!` (exactly like `swapdemo`/`acdemo`) so the full
// dovetail-driven Rho contextual σ-injection path can run end-to-end in
// `rholang-runtime/tests/rho_net_contextual_firing.rs`: the generated `dovetail_report_for`
// fires the inner premise `Flip` (the e-graph congruence closure closes `Wrap(_)` implicitly,
// so `WrapCong` itself fires no Dovetail rule) and resolves + bare-ifies its σ; the generated
// `rho_net_contextual_invocation_from_dovetail_to` reconstructs the reduced hole
// `T = RHS(Flip)[σ] = Pair(B, A)` and delivers it on `WrapCong`'s premise location channel,
// where the installed `contextual_join_receiver_par` binds it and emits `⟦Wrap(T)⟧` on `@out`.
//
// `Wrap(Swap(A, B))` reduces to `Wrap(Pair(B, A))` (the reduced context), and
// `Wrap(Swap(A, B)) ≠ Wrap(Pair(B, A))`, so a positive OUT observation is non-vacuous evidence
// the contextual rewrite fired as a COMM with the σ Dovetail computed.
language! {
    name: CtxDemo,

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
        Wrap . x:Proc |- "wrap" "(" x ")" : Proc ;
    },

    equations {},

    rewrites {
        Flip . |- (Swap x y) ~> (Pair y x) ;
        WrapCong . | S ~> T |- (Wrap S) ~> (Wrap T) ;
    },
}
