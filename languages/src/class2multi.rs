//! Phase 4 #1 (2026-05-11): multi-collection-slot Class 2 smoke grammar.
//!
//! Exercises two SimpleCollection params in a single rule. The
//! per-language lookups (close, sep, element_src) are now 3-tuple
//! keyed on `(result_src_idx, rule_idx, slot_idx)` so the two
//! collection slots can have distinct close delimiters parsed in
//! sequence. The walker's emit_push_side_effects continues to
//! overwrite `symbol.bp` with the allocator-assigned accumulator_id
//! at push time; in the supported subset (no outer collection
//! nesting), accumulator_id == slot_idx.

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
