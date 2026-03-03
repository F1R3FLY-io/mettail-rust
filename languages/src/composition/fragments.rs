//! Reusable grammar fragments for composition testing.
//!
//! These fragments define types + terms only. They generate no code —
//! consuming `language!` definitions pull them in via `mixins: [...]`.

use mettail_macros::language_fragment;

language_fragment! {
    name: IntArithFragment,
    types {
        ![i32] as Int
    },
    terms {
        AddInt . a:Int, b:Int |- a "+" b : Int ![a + b] fold;
        SubInt . a:Int, b:Int |- a "-" b : Int ![a - b] fold;
        MulInt . a:Int, b:Int |- a "*" b : Int ![a * b] fold;
    }
}

language_fragment! {
    name: BoolOpsFragment,
    types {
        ![bool] as Bool
    },
    terms {
        And . a:Bool, b:Bool |- a "and" b : Bool ![a && b] step;
        Or  . a:Bool, b:Bool |- a "or" b  : Bool ![a || b] step;
        Not . a:Bool |- "not" a : Bool ![!a] step;
    }
}
