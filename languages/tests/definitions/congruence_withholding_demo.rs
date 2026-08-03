//! End-to-end fixture for declared congruence withholding.
//!
//! `PairRightWithheld` severs only `Pair` field 1.  The sibling field 0 remains an ordinary
//! e-class child, which makes `pair(box(a),box(a))` a compact positive/negative witness: the
//! strictly cost-reducing kernel rewrite `box(X) -> X` propagates through the left field and
//! cannot propagate through the right. A same-cost `a -> b` witness would be ambiguous because
//! an e-graph extractor may legitimately choose either representative of the merged e-class.

#![allow(
    dead_code,
    unused_imports,
    non_local_definitions,
    clippy::crate_in_macro_def,
    clippy::empty_line_after_outer_attr
)]

use mettail_macros::language;

language! {
    name: CongruenceWithholdingDemo,

    options {
        hosted_in: "tests/definitions/congruence_withholding_demo.rs",
        emit_tests: false,
        emit_simulator: false,
        emit_blockly: false,
    },

    types { Term }

    terms {
        A . |- "a" : Term ;
        Box . value:Term |- "box" "(" value ")" : Term ;
        Pair . left:Term, right:Term
        |- "pair" "(" left "," right ")" : Term ;
    },

    equations {},

    rewrites {
        Unbox . |- (Box X) ~> X ;
        PairRightWithheld . | S ~/> T |- (Pair X S) ~> (Pair X T) ;
    },
}
