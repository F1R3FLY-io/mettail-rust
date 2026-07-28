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
        SubInt . a:Int, b:Int |- a "-" b : Int ![a - b] fold same;
        MulInt . a:Int, b:Int |- a "*" b : Int ![a * b] fold;
    }
}

language_fragment! {
    name: BoolOpsFragment,
    types {
        ![bool] as Bool
    },
    terms {
        // Loosest first — declaration order IS precedence order, so `or` must be
        // declared before `and` for `a or b and c` to read `a or (b and c)`.
        Or  . a:Bool, b:Bool |- a "or" b  : Bool ![a || b] step;
        And . a:Bool, b:Bool |- a "and" b : Bool ![a && b] step;
        Not . a:Bool |- "not" a : Bool ![!a] step;
    }
}
