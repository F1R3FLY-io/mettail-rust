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
        Add . a:Int, b:Int |- a "+" b : Int ![a + b] step;
        Sub . a:Int, b:Int |- a "-" b : Int ![a - b] fold;
        Up . a:Int, b:Int |- a "~" b : Int ![2 * a + 3 * b] fold;
    },
    equations {
    },
    rewrites {
        AddCongL . | S ~> T |- (Add S R) ~> (Add T R);
        AddCongR . | S ~> T |- (Add L S) ~> (Add L T);
        SubCongL . | S ~> T |- (Sub S R) ~> (Sub T R);
        SubCongR . | S ~> T |- (Sub L S) ~> (Sub L T);
    },
}
