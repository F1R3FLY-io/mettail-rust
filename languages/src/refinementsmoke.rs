//! Synthetic test grammar for refinement-type predicate codegen (B8).
//!
//! Exercises the closure-body lowering — `RefinementPredicate::Linear { x > 0 }`
//! is lowered to a closure registered with the runtime registry. The
//! `language!` macro emits a `register_refinements()` function that the
//! smoke test calls before evaluating predicates.

#![allow(
    non_local_definitions,
    clippy::crate_in_macro_def,
    clippy::empty_line_after_outer_attr
)]

use mettail_macros::language;

language! {
    name: RefinementSmoke,

    types {
        ![i32] as Int
        PosInt = { x: Int | x > 0 };
    },

    terms {
        IntToPosInt . i:Int |- i : PosInt ;
    },

    equations {},

    rewrites {},
}
