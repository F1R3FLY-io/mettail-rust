//! Generated-language fixture for a binder whose result and body categories differ.
//!
//! `Wrap` belongs to `Wrapper`, while its scope body belongs to `Proc`. The
//! typed Dovetail lowering PDA must therefore schedule `VisitProc` for the body;
//! routing it through `VisitWrapper` would interpret a raw `Proc` pointer as the
//! wrong generated AST type.

#![allow(
    dead_code,
    unused_imports,
    non_local_definitions,
    clippy::crate_in_macro_def,
    clippy::empty_line_after_outer_attr
)]

use mettail_macros::language;

language! {
    name: CrossCategoryBinderInverseDemo,

    options {
        emit_tests: false,
        emit_simulator: false,
        emit_blockly: false,
    },

    types {
        Proc
        Wrapper
        Name
    },

    terms {
        Zero . |- "0" : Proc ;
        Hit . |- "hit" : Proc ;
        Name0 . |- "n0" : Name ;

        Wrap . ^x.body:[Name -> Proc] |- "wrap" x "." body : Wrapper ;

        Probe . wrapped:Wrapper |- "probe" wrapped : Proc ![{
            match wrapped {
                Wrapper::Wrap(_) => Proc::Hit,
                other => Proc::Probe(std::sync::Arc::new(other.clone())),
            }
        }] fold;
    },

    equations {},
}
