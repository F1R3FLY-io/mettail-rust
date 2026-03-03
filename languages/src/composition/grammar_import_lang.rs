//! Language that imports grammar from `BaseMath` via `includes:`.
//!
//! Imports types and terms from BaseMath (Add, Sub) but NOT equations/rewrites.
//! Adds its own Div rule and provides its own rewrites for all rules.

use mettail_macros::language;

language! {
    name: ImportedMath,
    includes: [BaseMath],
    types {
    },
    terms {
        Div . a:Num, b:Num |- a "/" b : Num ![a / b] fold;
    },
    equations {
    },
    rewrites {
        // Rewrites for imported rules (includes does NOT import rewrites)
        AddCongL . | S ~> T |- (Add S R) ~> (Add T R);
        AddCongR . | S ~> T |- (Add L S) ~> (Add L T);
        SubCongL . | S ~> T |- (Sub S R) ~> (Sub T R);
        SubCongR . | S ~> T |- (Sub L S) ~> (Sub L T);
        // Rewrites for locally defined rules
        DivCongL . | S ~> T |- (Div S R) ~> (Div T R);
        DivCongR . | S ~> T |- (Div L S) ~> (Div L T);
    },
}
