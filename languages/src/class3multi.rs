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

#![allow(
    non_local_definitions,
    clippy::crate_in_macro_def,
    clippy::empty_line_after_outer_attr
)]

use mettail_macros::language;

language! {
    name: Class3Multi,

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
