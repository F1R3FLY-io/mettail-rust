//! Synthetic test grammar for refinement-type predicate codegen (B8).
//!
//! Exercises the closure-body lowering — `RefinementPredicate::Linear { x > 0 }`
//! is lowered to a closure registered with the runtime registry. The
//! `language!` macro emits a `register_refinements()` function that the
//! smoke test calls before evaluating predicates.

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
    name: RefinementSmoke,

    options {
        // Task #11 (extended 2026-07-26): this is a NON-PRODUCTION language definition
        // (`languages/src/` is production-only), so it lives in
        // `languages/tests/definitions/`. The key tells the macro to emit the generated
        // suite INLINE (the opt-in `refinementsmoke_generated_tests!` wrapper) instead of writing
        // `languages/tests/gen_refinementsmoke_*.rs`, whose `use mettail_languages::refinementsmoke::*;`
        // header cannot resolve once the definition has left the library; it also gives the
        // simulation CLI a `#[path]` prologue instead of that same library import.
        hosted_in: "tests/definitions/refinementsmoke.rs",
    },

    types {
        ![i32] as Int
        PosInt = { x: Int | x > 0 };
    },

    terms {
        IntToPosInt . i:Int |- i : PosInt ;
    },

    equations {},

    rewrites {},
}
