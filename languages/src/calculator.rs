#![allow(
    non_local_definitions,
    clippy::crate_in_macro_def,
    clippy::empty_line_after_outer_attr
)]

use mettail_macros::language;

language! {
    name: Calculator,
    types {
        ![i32] as Int
    },
    terms {
        Add . Int ::= Int "+" Int ;
        Sub . Int ::= Int "-" Int ;
    },
    equations {
    },
    rewrites {
        if S ~> T then (Add S R) ~> (Add T R);
        if S ~> T then (Add L S) ~> (Add L T);
        if S ~> T then (Sub S R) ~> (Sub T R);
        if S ~> T then (Sub L S) ~> (Sub L T);
    },
    semantics {
        Add: +,
        Sub: -,
    }
}
