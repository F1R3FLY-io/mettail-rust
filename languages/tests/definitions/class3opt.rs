//! Phase 4 #4 stretch (2026-05-12): Class-3 ZIP-MAP-SEP BinderListLoop
//! combined with Class-2 SimpleCollection inside `*opt(...)`.
//!
//! This combines the features of:
//!   - Phase 4 #2 (Class-3 top-level multi-slot)
//!   - Phase 4 #3 (Class-2 SimpleCollection inside *opt)
//!
//! Grammar (term_context order chosen so Scope is LAST for the term-ops
//! codegen's Scope-last assumption; the *opt collection slot precedes
//! the Scope to keep the BinderList+Body action_args adjacent at the
//! tail):
//!
//!   PInputsOptTagged . ns:Vec(Name), *opt(qs:Vec(Proc)), ^[xs].p:[Name* -> Proc]
//!       |- "(" *zip(ns,xs).*map(|n,x| n "?" x).*sep(",") ")"
//!          "." "{" p "}"
//!          *opt("with" "[" qs.*sep("|") "]")
//!       : Proc;
//!
//! Slot allocation order (by syntax_pattern walk):
//!   - syntax_pattern[1] (*zip.*map.*sep): BinderListLoop slot 0 (Class-3 names)
//!   - syntax_pattern[9] (*opt(... qs.*sep ...)): OptionalGroup with inner
//!     Sep slot 1 (Class-2 inside *opt)
//!
//! This rule exercises:
//!   - Class-3 names accumulator allocation + binder scope open/close.
//!   - Class-2 SimpleCollection inside *opt: when taken, allocates a
//!     second collection slot.
//!   - Per-(src, rule, slot_idx) `is_class3_collection_per_slot`
//!     disambiguates: slot 0 is Class-3 (opens BinderScope), slot 1
//!     inside *opt is Class-2 (no BinderScope).
//!   - Optional+Collection AST emission (`Option<Vec<Proc>>`).

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
    name: Class3Opt,

    options {
        // Task #11 (extended 2026-07-26): this is a NON-PRODUCTION language definition
        // (`languages/src/` is production-only), so it lives in
        // `languages/tests/definitions/`. The key tells the macro to emit the generated
        // suite INLINE (the opt-in `class3opt_generated_tests!` wrapper) instead of writing
        // `languages/tests/gen_class3opt_*.rs`, whose `use mettail_languages::class3opt::*;`
        // header cannot resolve once the definition has left the library; it also gives the
        // simulation CLI a `#[path]` prologue instead of that same library import.
        hosted_in: "tests/definitions/class3opt.rs",
    },

    types {
        Proc
        Name
    },

    terms {
        PZero . |- "0" : Proc;

        NQuote . p:Proc |- "@" "(" p ")" : Name;

        PInputsOptTagged . ns:Vec(Name), *opt(qs:Vec(Proc)), ^[xs].p:[Name* -> Proc]
            |- "(" *zip(ns,xs).*map(|n,x| n "?" x).*sep(",") ")"
               "." "{" p "}"
               *opt("with" "[" qs.*sep("|") "]")
            : Proc;
    },

    equations {},

    rewrites {},
}
