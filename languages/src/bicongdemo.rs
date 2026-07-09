#![allow(
    non_local_definitions,
    clippy::crate_in_macro_def,
    clippy::empty_line_after_outer_attr
)]

use mettail_macros::language;

// Stage 4 (S-contextual, sub-slice 2) demonstration language: a 2-ARY CONGRUENCE (contextual)
// rewrite `NodeCong: | S0 ~> T0, S1 ~> T1 |- Node(S0, S1) ~> Node(T0, T1)` closes the context
// `Node(_, _)` around TWO inner premises, whose mechanism is the base rewrite
// `Flip: Swap(x, y) ~> Pair(y, x)`.
//
// This is the FIRST bundled language shape exercising the N-ARY (n > 1) in-Rho CONTEXTUAL firing
// path (Stage 4 S-contextual, sub-slice 2) end-to-end. CtxDemo's `WrapCong` is UNARY (one hole);
// this widens it to TWO holes, each reduced IN RHO at its OWN hole position (`Node.0` / `Node.1`)
// and routed to its OWN join premise channel, so `Node(Swap(A, B), Swap(C, D))` reassembles to
// `Node(Pair(B, A), Pair(D, C))` — each reduced hole placed at its context position by the
// hole↔channel correspondence.
//
// Because `Pair(B, A) ≠ Pair(D, C)`, the reassembled `Node(Pair(B, A), Pair(D, C))` is NON-SYMMETRIC:
// a positive OUT observation of exactly this value is non-vacuous evidence that BOTH holes fired in
// Rho AND that each reduced hole landed at the CORRECT context position (a swapped routing would
// land `Node(Pair(D, C), Pair(B, A))`). `Node(Swap(A, B), Swap(C, D)) ≠ Node(Pair(B, A), Pair(D, C))`,
// so it is also non-vacuous against the input.
//
// Promoted to a generated `language!` (exactly like `ctxdemo`) so the full dovetail-driven Rho
// contextual σ-injection path runs end-to-end in `rholang-runtime/tests/rho_net_bicong_firing.rs`:
// the generated `dovetail_report_for` fires the TWO inner premise `Flip`s (the e-graph congruence
// closure closes `Node(_, _)` implicitly, so `NodeCong` itself fires no explicit Dovetail rule), and
// the generated `rho_net_contextual_invocation_from_dovetail_to` LOCATES each hole's premise redex
// IN RHO, routes each reduced hole to its join premise channel, and the installed
// `contextual_join_receiver_par` (n = 2) reassembles `⟦Node(Pair(B, A), Pair(D, C))⟧` on `@out`.
language! {
    name: BiCongDemo,

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
        C . |- "C" : Proc ;
        D . |- "D" : Proc ;
        Pair . x:Proc, y:Proc |- "pair" "(" x "," y ")" : Proc ;
        Swap . x:Proc, y:Proc |- "swap" "(" x "," y ")" : Proc ;
        Node . x:Proc, y:Proc |- "node" "(" x "," y ")" : Proc ;
    },

    equations {},

    rewrites {
        Flip . |- (Swap x y) ~> (Pair y x) ;
        NodeCong . | S0 ~> T0, S1 ~> T1 |- (Node S0 S1) ~> (Node T0 T1) ;
    },
}
