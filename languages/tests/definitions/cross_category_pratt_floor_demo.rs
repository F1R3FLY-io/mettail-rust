//! Minimal deterministic grammar for category-changing closed-primary Pratt tests.

#![allow(
    dead_code,
    unused_imports,
    non_local_definitions,
    clippy::crate_in_macro_def,
    clippy::empty_line_after_outer_attr
)]

use mettail_macros::language;

language! {
    name: CrossCategoryPrattFloorDemo,

    options {
        hosted_in: "tests/definitions/cross_category_pratt_floor_demo.rs",
        emit_tests: false,
        emit_simulator: false,
        emit_blockly: false,
    },

    types {
        Proc
        Name
    },

    terms {
        NameAtom . |- "n" : Name;
        NameGroup . inner:Name |- "name" "(" inner ")" : Name;
        ProcAtom . |- "p" : Proc;
        Send . channel:Name, body:Proc |- channel "!" "(" body ")" : Proc;
        Parallel . left:Proc, right:Proc |- left "|" right : Proc;
    },

    equations {},
    rewrites {},
}
