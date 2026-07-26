//! Phase 4 #3 (2026-05-12): Class-2 SimpleCollection inside *opt(...) smoke
//! grammar.
//!
//! Exercises a SimpleCollection slot nested inside an optional group. The
//! per-(src, rule, slot_idx) predicate `is_class3_collection_per_slot`
//! correctly returns `false` for this Class-2 slot — no BinderScope is
//! opened spuriously. The Optional extractor's CollectionDrain inner arm
//! (previously emitted as `()` when SimpleCollection was rejected by
//! classify_binder) now materializes `Option<Vec<#elem>>`.
//!
//! Grammar:
//!   ChooseMaybe . a:Proc, *opt(qs:Vec(Proc))
//!       |- "choose" a *opt("with" "(" qs.*sep("|") ")") : Proc;
//!
//! Expected behavior:
//! - When optional taken (`choose 0 with ( 0 | 0 )`):
//!     ChooseMaybe(Box<PZero>, Some(vec![PZero, PZero]))
//! - When optional skipped (`choose 0`):
//!     ChooseMaybe(Box<PZero>, None)
//!
//! Slot allocation (by syntax_pattern walk in classify_binder):
//!   - syntax_pattern[2] (*opt(...)) → OptionalGroup with inner walk:
//!       inner_idx[2] (Op(Sep{qs, "|", None})) → SimpleCollection slot 0

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
    name: Class2OptSmoke,

    options {
        // Task #11 (extended 2026-07-26): this is a NON-PRODUCTION language definition
        // (`languages/src/` is production-only), so it lives in
        // `languages/tests/definitions/`. The key tells the macro to emit the generated
        // suite INLINE (the opt-in `class2optsmoke_generated_tests!` wrapper) instead of writing
        // `languages/tests/gen_class2optsmoke_*.rs`, whose `use mettail_languages::class2optsmoke::*;`
        // header cannot resolve once the definition has left the library; it also gives the
        // simulation CLI a `#[path]` prologue instead of that same library import.
        hosted_in: "tests/definitions/class2optsmoke.rs",
    },

    types {
        Proc
    },

    terms {
        PZero . |- "0" : Proc;

        ChooseMaybe . a:Proc, *opt(qs:Vec(Proc))
            |- "choose" a *opt("with" "(" qs.*sep("|") ")") : Proc;
    },

    equations {},

    rewrites {},
}
