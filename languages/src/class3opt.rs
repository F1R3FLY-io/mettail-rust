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

#![allow(
    non_local_definitions,
    clippy::crate_in_macro_def,
    clippy::empty_line_after_outer_attr
)]

use mettail_macros::language;

language! {
    name: Class3Opt,

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
