//! Phase 4 #1 (2026-05-11): multi-collection-slot Class 2 smoke grammar.
//!
//! Exercises two SimpleCollection params in a single rule. The
//! per-language lookups (close, sep, element_src) are now 3-tuple
//! keyed on `(result_src_idx, rule_idx, slot_idx)` so the two
//! collection slots can have distinct close delimiters parsed in
//! sequence. The marker `bp` stores the static `slot_idx`; the walker
//! carries runtime accumulator ids separately through CollectionId
//! action arguments.

#![allow(
    non_local_definitions,
    clippy::crate_in_macro_def,
    clippy::empty_line_after_outer_attr
)]

use mettail_macros::language;

language! {
    name: Class2Multi,

    types {
        Proc
    },

    terms {
        PZero . |- "0" : Proc;

        Pair . xs:Vec(Proc), ys:Vec(Proc)
            |- "pair" "(" xs.*sep("|") ")" "(" ys.*sep("|") ")" : Proc;
    },

    equations {},

    rewrites {},
}
