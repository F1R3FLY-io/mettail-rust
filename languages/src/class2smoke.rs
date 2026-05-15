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

#![allow(
    non_local_definitions,
    clippy::crate_in_macro_def,
    clippy::empty_line_after_outer_attr
)]

use mettail_macros::language;

language! {
    name: Class2Smoke,

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
