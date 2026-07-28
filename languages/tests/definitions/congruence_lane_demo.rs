// Task #94 — RED C. See `languages/tests/lowering_disposition_reds.rs` for the assertions.
#![allow(
    dead_code,
    unused_imports,
    non_local_definitions,
    clippy::crate_in_macro_def,
    clippy::empty_line_after_outer_attr
)]

use mettail_macros::language;

// ─────────────────────────────────────────────────────────────────────────────
// ★★ RED C — THE ANTI-VACUITY CHECK ON THE FIX ITSELF.
//
// RED A and RED B both assert that something IS a declination. A mechanism could pass both by
// declaring everything it does not emit a rule for to be a declination — and it would then be
// catastrophically wrong, because the overwhelmingly common reason a rewrite produces no rule is
// that ANOTHER LANE COVERS IT. In the bundled Rholang, 400 of 461 declared rewrites produce no
// structural rule for exactly that reason. Calling them declinations would bury the fifteen real
// ones under four hundred false positives and make the inventory worthless.
//
// `WrapCong` is that case in miniature. It is a congruence rewrite:
//
//     S ~> T  ⊢  Wrap(S) ~> Wrap(T)
//
// and it needs no lowered rule, because after `AToB` merges `A`'s e-class with `B`'s, e-graph
// CONGRUENCE CLOSURE propagates that merge through every enclosing e-node — including
// `Wrap(_)` — without any rule firing. Emitting a rule would duplicate work the closure already
// does. So the correct disposition is `DeliveredElsewhere { EGraphCongruenceClosure }`, and
// `Declined` would be a lie about a rewrite that works perfectly.
//
// `AToB` is the paired positive control: a rewrite on the same language, in the same walk, that
// IS lowered here. Without it, "WrapCong was attributed elsewhere" could not be distinguished
// from "the rewrite walk did nothing at all".
language! {
    name: CongruenceLaneDemo,

    options {
        emit_tests: false,
        emit_simulator: false,
        emit_blockly: false,
    },

    types {
        Term
    },

    terms {
        Wrap . a:Term |- "wrap" "(" a ")" : Term ;
        A . |- "a" : Term ;
        B . |- "b" : Term ;
    },

    equations {},

    rewrites {
        // The kernel rewrite: lowered HERE, as a structural rule.
        AToB . |- A ~> B ;
        // The congruence closure of that kernel rewrite: lowered on the E-GRAPH lane.
        WrapCong . | S ~> T |- (Wrap S) ~> (Wrap T) ;
    },
}
