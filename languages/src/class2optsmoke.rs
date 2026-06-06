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

#![allow(
    non_local_definitions,
    clippy::crate_in_macro_def,
    clippy::empty_line_after_outer_attr
)]

use mettail_macros::language;

language! {
    name: Class2OptSmoke,

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
