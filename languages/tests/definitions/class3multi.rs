//! Phase 4 #2 (2026-05-12): Class-3 + Class-2 multi-collection-slot smoke
//! grammar.
//!
//! Exercises a Class-2 SimpleCollection slot at slot_idx=0 AND a Class-3
//! ZIP-MAP-SEP BinderListLoop (with its synthesized names accumulator) at
//! slot_idx=1 in the same rule. The per-(src, rule, slot_idx) predicate
//! `is_class3_collection_per_slot` (replacing the pre-Phase-4-#2 per-rule
//! `is_class3_collection`) ensures only the Class-3 slot opens a
//! BinderScope; the Class-2 sibling slot must NOT.
//!
//! Grammar:
//!   TaggedInputs . tags:Vec(Proc), ns:Vec(Name), ^[xs].p:[Name* -> Proc]
//!       |- "with" "[" tags.*sep(";") "]"
//!          "(" *zip(ns,xs).*map(|n,x| n "?" x).*sep(",") ")"
//!          "." "{" p "}"
//!       : Proc ;
//!
//! Slot allocation order (by syntax_pattern walk in classify_binder):
//!   - syntax_pattern[3] (tags.*sep(";")): SimpleCollection      → slot 0 (Class-2)
//!   - syntax_pattern[5] (*zip(ns,xs).*map.*sep): BinderListLoop → slot 1 (Class-3)
//!
//! Pre-Phase-4-#2 the per-rule `is_class3_collection` predicate would
//! have returned `true` for ALL slots in this rule (because the rule
//! has a Class-3 BinderListLoop somewhere), spuriously opening a
//! BinderScope on the Class-2 tags slot — breaking parsing.
//! Post-Phase-4-#2 the per-slot predicate returns `true` ONLY at
//! (Proc, TaggedInputs, 1).
//!
//! Term-context order chosen so Scope is the LAST AST field (matches
//! the current term-ops codegen's "Scope is last" assumption; see
//! macros/src/gen/term_ops/normalize.rs:975). A future codegen
//! generalization can re-enable Scope-not-last layouts.

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
    name: Class3Multi,

    options {
        // Task #11 (extended 2026-07-26): this is a NON-PRODUCTION language definition
        // (`languages/src/` is production-only), so it lives in
        // `languages/tests/definitions/`. The key tells the macro to emit the generated
        // suite INLINE (the opt-in `class3multi_generated_tests!` wrapper) instead of writing
        // `languages/tests/gen_class3multi_*.rs`, whose `use mettail_languages::class3multi::*;`
        // header cannot resolve once the definition has left the library; it also gives the
        // simulation CLI a `#[path]` prologue instead of that same library import.
        hosted_in: "tests/definitions/class3multi.rs",
    },

    types {
        Proc
        Name
    },

    terms {
        PZero . |- "0" : Proc;

        NQuote . p:Proc |- "@" "(" p ")" : Name;

        TaggedInputs . tags:Vec(Proc), ns:Vec(Name), ^[xs].p:[Name* -> Proc]
            |- "with" "[" tags.*sep(";") "]"
               "(" *zip(ns,xs).*map(|n,x| n "?" x).*sep(",") ")"
               "." "{" p "}"
            : Proc;
    },

    equations {},

    rewrites {},
}
