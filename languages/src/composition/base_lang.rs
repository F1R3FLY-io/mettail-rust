//! Base language for testing `extends:` and `includes:` composition.
//!
//! Defines a minimal arithmetic language with rewrites.

use mettail_macros::language;

language! {
    name: BaseMath,
    types {
        ![i32] as Num
    },
    terms {
        Add . a:Num, b:Num |- a "+" b : Num ![a + b] fold;
        Sub . a:Num, b:Num |- a "-" b : Num ![a - b] fold;
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
