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
    name: GuardOptSmoke,

    options {
        // Task #11 (extended 2026-07-26): this is a NON-PRODUCTION language definition
        // (`languages/src/` is production-only), so it lives in
        // `languages/tests/definitions/`. The key tells the macro to emit the generated
        // suite INLINE (the opt-in `guardoptsmoke_generated_tests!` wrapper) instead of writing
        // `languages/tests/gen_guardoptsmoke_*.rs`, whose `use mettail_languages::guardoptsmoke::*;`
        // header cannot resolve once the definition has left the library; it also gives the
        // simulation CLI a `#[path]` prologue instead of that same library import.
        hosted_in: "tests/definitions/guardoptsmoke.rs",
        emit_simulator: false,
        emit_blockly: false,
    },

    types {
        Proc
        ![i64] as Int
    },

    terms {
        PNil . |- "Nil" : Proc ;

        /// A wrapper whose guard is OPTIONAL: `check(k)` or
        /// `check(k where g)` — the guard slot sits inside `*opt(...)`.
        /// NOTE (A-11 shape, updated by task #14): the rule produces the
        /// NATIVE category `Int` with an eval body. Historically that
        /// choice dodged a then-unfixed term-ops gap (`f1_pred` vs
        /// `f1_slot/f1_some` in the generated normalize.rs — closed by
        /// task #14 for BOTH the native and non-native shapes); it is
        /// KEPT because the Int shape additionally exercises the native
        /// eval/try_fold path over a guard-bearing variant (the PDA
        /// classify + guard-arity layers), which a Proc shape would not.
        /// The site-2 parse path (GuardSlot inside the optional group) is
        /// identical either way. Documented in the F1 ledger entry.
        PCheck . k:Int, *opt(?g:Guard)
            |- "check" "(" k *opt("where" g) ")" : Int
            ![{ k }] ;
    },

    equations {},

    logic {
        relation ok(Proc);
    },
}
