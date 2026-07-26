//! B9 / Class 2 BINDER-WITH-COLLECTION-PARAM smoke grammar (2026-05-08).
//!
//! Minimal grammar exercising a multi-Param rule with one tag param + one
//! Vec-typed collection param parsed via `Sep` over a separator. The
//! minimal-composition design routes the binder rule's collection slot
//! through a `CollectionMarker` push + `is_binder_internal_collection`
//! FireAction-suppression — reusing the existing `WpdaState::CollectionLoop`
//! apparatus rather than introducing a specialized
//! `WpdaState::BinderSimpleCollectionLoop`.
//!
//! The `Choose` rule is structurally analogous to a guarded-choice
//! operator: a tag `a:Proc` followed by a parenthesized
//! `|`-separated list of alternatives `qs:Vec(Proc)`.

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
    name: Class2Smoke,

    options {
        // Task #11 (extended 2026-07-26): this is a NON-PRODUCTION language definition
        // (`languages/src/` is production-only), so it lives in
        // `languages/tests/definitions/`. The key tells the macro to emit the generated
        // suite INLINE (the opt-in `class2smoke_generated_tests!` wrapper) instead of writing
        // `languages/tests/gen_class2smoke_*.rs`, whose `use mettail_languages::class2smoke::*;`
        // header cannot resolve once the definition has left the library; it also gives the
        // simulation CLI a `#[path]` prologue instead of that same library import.
        hosted_in: "tests/definitions/class2smoke.rs",
    },

    types {
        Proc
    },

    terms {
        PZero . |- "0" : Proc;

        Choose . a:Proc, qs:Vec(Proc)
            |- "choose" a "(" qs.*sep("|") ")" : Proc;
    },

    equations {},

    rewrites {},
}
