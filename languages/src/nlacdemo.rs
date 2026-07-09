#![allow(
    non_local_definitions,
    clippy::crate_in_macro_def,
    clippy::empty_line_after_outer_attr
)]

use mettail_macros::language;

// Stage 4 S-AC (AC3) demonstration language: the NON-LINEAR with-rest HashBag AC base rewrite
// `PPar{x, x, ...rest} ~> Wrap(x)` over nullary `A`/`B`/`C` — the repeated bare element var `x`
// expresses the `N ≡ N` non-linear consistency shape (the abstract form of the Ambient/Comm
// channel-equality guard) with the RHS referencing the SAME bound `x`, so — unlike the structured
// Ambient/Comm rules whose reducts are host-computed — the WHOLE match AND fire is in Rho: the
// co-installed `ac_sigma_receiver_par_with_condition` picks TWO EQUAL elements (the
// `Receive.condition` guard `EEq(slot0, slot1)`), binds `rest`, and emits `Wrap(x)` for the shared
// element `x`.
//
// This is the NON-LINEAR analogue of `AcDemo` (whose single-`x` LHS is linear): it exercises the
// AC3 `ac_nonlinear_condition` guard end-to-end. Kept SEPARATE (like `AcBagDemo`) so its firing
// suite does not interfere with `AcDemo`/`AcBagDemo` — the same subject would fire different rules.
//
// The subject `{A | A | B}` has a UNIQUE non-linear match — only `A` occurs twice, so `x = A`,
// `rest = {B}`, and OUT is `Wrap(A)` deterministically. `{A | B | C}` (all distinct) has NO match.
// A positive OUT observation of `Wrap(A)` is non-vacuous evidence the non-linear AC rewrite fired
// as a COMM with the guard enforced (two equal elements picked).
language! {
    name: NlAcDemo,

    options {
        emit_simulator: false,
        emit_blockly: false,
    },

    types {
        Proc
        ![mettail_runtime::HashBag<Proc>] as Bag {
            open_parts: ["#{"],
            close_parts: ["}#"],
            sep: "|",
        }
    },

    terms {
        A . |- "A" : Proc ;
        B . |- "B" : Proc ;
        C . |- "C" : Proc ;
        Wrap . x:Proc |- "wrap" "(" x ")" : Proc ;
        PPar . ps:HashBag(Proc) |- "#{" ps.*sep("|") "}#" : Proc ;
    },

    equations {},

    rewrites {
        NlAcStep . |- (PPar {x, x, ...rest}) ~> (Wrap x) ;
    },
}
