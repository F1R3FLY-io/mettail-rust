//! Guard-inside-optional-group smoke grammar (P3.d / F1 amendment A-11,
//! 2026-07-11).
//!
//! Exercises the SECOND `ParsePredicate` codegen emission site — a
//! `?g:Guard` param INSIDE `*opt(...)` (binder.rs `ParamKind::Guard` →
//! `BinderPosition::GuardSlot` in the optional-group INNER positions,
//! ~binder.rs:836-839; action arg `ActionArgKind::Predicate`). The only
//! other in-tree predicate grammar (`guarded_rho`) uses site 1 (a guard
//! slot directly in a binder rule), so this module is the test-backed
//! coverage for the group-frame flow: the predicate leaf folds into the
//! OPTIONAL group frame's spine and flattens through the
//! `OPTIONAL_PRESENT` packing into `ActionArg::Optional(Some([...
//! Predicate ...]))`.
//!
//! Test inputs (languages/tests/guardopt_smoke.rs):
//!   - `check ( Nil where ok ( Nil ) )` → guard PRESENT (site-2 dispatch)
//!   - `check ( Nil )`                  → guard ABSENT (OptGroupAbsent)

#![allow(
    non_local_definitions,
    clippy::crate_in_macro_def,
    clippy::empty_line_after_outer_attr
)]

use mettail_macros::language;

language! {
    name: GuardOptSmoke,

    options {
        emit_simulator: false,
        emit_blockly: false,
    },

    types {
        Proc
        ![i64] as Int
    },

    terms {
        PNil . |- "Nil" : Proc ;

        /// A proc wrapper whose guard is OPTIONAL: `check(p)` or
        /// `check(p where g)` — the guard slot sits inside `*opt(...)`.
        /// NOTE (A-11 shape): the rule produces the NATIVE category `Int`
        /// with an eval body — the NON-native normalize PDA emitter has a
        /// PRE-EXISTING, engine-independent gap for `Option<Guard>`
        /// fields (`f1_pred` vs `f1_slot/f1_some` field-name mismatch in
        /// the generated `normalize.rs`; classic hits it identically at
        /// COMPILE time), so a Proc-producing guarded-opt rule cannot
        /// build in ANY engine today. The native route exercises the SAME
        /// site-2 parse path (GuardSlot inside the optional group) while
        /// bypassing the unrelated term-ops gap. Documented in the F1
        /// ledger entry.
        PCheck . k:Int, *opt(?g:Guard)
            |- "check" "(" k *opt("where" g) ")" : Int
            ![{ k }] ;
    },

    equations {},

    logic {
        relation ok(Proc);
    },
}
