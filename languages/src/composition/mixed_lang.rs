//! Language that mixes in fragments via `mixins:`.
//!
//! Pulls in `IntArithFragment` (Int type + Add/Sub/Mul) and `BoolOpsFragment`
//! (Bool type + And/Or/Not). Adds its own negation rule and rewrites.

use mettail_macros::language;

language! {
    name: MixedMath,
    mixins: [IntArithFragment, BoolOpsFragment],
    types {
    },
    terms {
        Neg . a:Int |- "-" a : Int ![(-a)] fold;
    },
    equations {
    },
    rewrites {
        AddIntCongL . | S ~> T |- (AddInt S R) ~> (AddInt T R);
        AddIntCongR . | S ~> T |- (AddInt L S) ~> (AddInt L T);
        SubIntCongL . | S ~> T |- (SubInt S R) ~> (SubInt T R);
        SubIntCongR . | S ~> T |- (SubInt L S) ~> (SubInt L T);
        MulIntCongL . | S ~> T |- (MulInt S R) ~> (MulInt T R);
        MulIntCongR . | S ~> T |- (MulInt L S) ~> (MulInt L T);
        NegCong     . | S ~> T |- (Neg S) ~> (Neg T);
        AndCongL    . | S ~> T |- (And S R) ~> (And T R);
        AndCongR    . | S ~> T |- (And L S) ~> (And L T);
        OrCongL     . | S ~> T |- (Or S R) ~> (Or T R);
        OrCongR     . | S ~> T |- (Or L S) ~> (Or L T);
        NotCong     . | S ~> T |- (Not S) ~> (Not T);
    },
}
