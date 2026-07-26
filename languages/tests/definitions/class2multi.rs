//! Phase 4 #1 (2026-05-11): multi-collection-slot Class 2 smoke grammar.
//!
//! Exercises two SimpleCollection params in a single rule. The
//! per-language lookups (close, sep, element_src) are now 3-tuple
//! keyed on `(result_src_idx, rule_idx, slot_idx)` so the two
//! collection slots can have distinct close delimiters parsed in
//! sequence. The marker `bp` stores the static `slot_idx`; the walker
//! carries runtime accumulator ids separately through CollectionId
//! action arguments.

// Task #11 (extended 2026-07-26): as a library module this definition inherited
// `languages/src/lib.rs`'s crate-level `#![allow(unused_imports, ...)]`. A `#[path]`-included
// module inherits nothing, and each consumer exercises a different slice of the generated
// surface (the parser, the codegen helpers, or neither), so `dead_code` / `unused_imports`
// are expected here rather than a signal. They are allowed at the definition -- the one place
// every consumer shares -- instead of being re-allowed at each `#[path]` site.
#![allow(
    dead_code,
    unused_imports,
    non_local_definitions,
    clippy::crate_in_macro_def,
    clippy::empty_line_after_outer_attr
)]

use mettail_macros::language;

language! {
    name: Class2Multi,

    options {
        // Task #11 (extended 2026-07-26): this is a NON-PRODUCTION language definition
        // (`languages/src/` is production-only), so it lives in
        // `languages/tests/definitions/`. The key tells the macro to emit the generated
        // suite INLINE (the opt-in `class2multi_generated_tests!` wrapper) instead of writing
        // `languages/tests/gen_class2multi_*.rs`, whose `use mettail_languages::class2multi::*;`
        // header cannot resolve once the definition has left the library; it also gives the
        // simulation CLI a `#[path]` prologue instead of that same library import.
        hosted_in: "tests/definitions/class2multi.rs",
    },

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
