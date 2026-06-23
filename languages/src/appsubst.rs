//! `AppSubst` — a generality fixture for macro-codegen extension **E1** (generalized substitution
//! lowering).
//!
//! A tiny binder calculus that is deliberately NOT Lambda: different constructor names (`Abs`/`Ap`
//! vs `Lam`/`App`) and different concrete syntax (`abs x. b` / `ap(f, a)`). It has the same shape
//! E1 keys on — a binder `[T -> T]` plus a rewrite whose RHS is an `(eval <binder> <arg>)`
//! substitution — so if E1's substitution detector / dispatch / progress-weights were keyed on
//! Lambda's `Lam`/`App` names (or on `name == "Lambda"`) rather than derived from `LanguageDef`,
//! this language would NOT β-reduce in the Dovetail e-graph. It does (see
//! `languages/tests/lambda_dovetail_synthetic.rs`), proving the mechanism is fully generalized.
//!
//! It is a real `src` fixture (not a test-local `language!`) because the `language!` macro emits a
//! crate-coupled `src/bin/simulate_<lang>.rs` and `tests/gen_<lang>_*.rs` for every invocation; a
//! test-local invocation is therefore infeasible (it would write a bin referencing a nonexistent
//! `mettail_languages::appsubst` module). See `macros/src/gen/runtime/dovetail_report.rs` (the
//! "`language!` is infeasible here" note) and the smoke fixtures (`class2smoke`, …) for the pattern.

#![allow(
    non_local_definitions,
    clippy::crate_in_macro_def,
    clippy::empty_line_after_outer_attr
)]

use mettail_macros::language;

language! {
    name: AppSubst,

    types {
        T
    },

    terms {
        Abs . ^x.body:[T -> T] |- "abs " x "." body : T;

        Ap . f:T, a:T |- "ap" "(" f "," a ")" : T;
    },

    equations {},

    rewrites {
        Reduce . |- (Ap (Abs f) a) ~> (eval f a);
        ApCongL . | M0 ~> M1 |- (Ap M0 N) ~> (Ap M1 N);
        ApCongR . | N0 ~> N1 |- (Ap M N0) ~> (Ap M N1);
        AbsCong . | S ~> T |- (Abs ^x.S) ~> (Abs ^x.T);
    },
}
