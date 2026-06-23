//! Generality gate for macro-codegen extension **E1** (generalized substitution lowering).
//!
//! Defines a SYNTHETIC language `AppSubst` — a tiny binder calculus that is NOT Lambda (different
//! constructor names `Abs`/`Ap`, different concrete syntax `abs x. b` / `ap(f, a)`) — with a binder
//! `[T -> T]` and a rewrite whose RHS is an `(eval <binder> <arg>)` substitution. If E1's
//! substitution detector / dispatch / progress-weights were keyed on Lambda's `Lam`/`App` names (or
//! on `name == "Lambda"`) rather than derived from `LanguageDef`, this language would NOT β-reduce.
//! It does — proving the mechanism is fully generalized.
//!
//! (One `language!` per integration-test crate: each expansion emits crate-level un-namespaced PDA/
//! lexer helpers, so a second `language!` here would collide. A cross-category `[A -> B]` binder is
//! additionally exercised by E2's `PNew` reconstruction in `dovetail_normal_term.rs` and is sound by
//! construction — the E1 dispatch derives `binder_var_cat`/`body_cat` independently from the binder
//! `VariantKind`.)
#![cfg(feature = "dovetail-codegen")]

use mettail_macros::language;
use mettail_runtime::Language;

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

const MAX_ITERS: usize = 64;
const MAX_NODES: usize = 1_000_000;

#[test]
fn synthetic_appsubst_beta_report_is_ok() {
    let lang = AppSubstLanguage;
    let term = lang.parse_term("ap(abs x. x, y)").expect("parse identity application");
    let report = AppSubstLanguage::dovetail_report_for(term.as_ref(), MAX_ITERS, MAX_NODES);
    assert!(
        report.is_ok(),
        "a non-Lambda binder language's `(eval ..)` rewrite must β-reduce after E1: {:?}",
        report.err()
    );
}

#[test]
fn synthetic_appsubst_identity_reduces_to_argument() {
    let lang = AppSubstLanguage;
    let term = lang.parse_term("ap(abs x. x, y)").expect("parse");
    let nf = AppSubstLanguage::dovetail_normal_term(term.as_ref(), MAX_ITERS, MAX_NODES)
        .unwrap_or_else(|e| panic!("dovetail_normal_term returned Err: {e}"));
    assert_eq!(lang.format_term(nf.as_ref()), "y", "(abs x. x) y β-reduces to y");
}

#[test]
fn synthetic_appsubst_contractum_preferred_over_redex() {
    // `(abs x. ap(x,x)) w` → `ap(w, w)` — the MF1 progress-weights must make extraction prefer the
    // contractum over the un-reduced `Ap(Abs.., w)` redex, generically (not via any Lambda-specific
    // weighting).
    let lang = AppSubstLanguage;
    let term = lang.parse_term("ap(abs x. ap(x,x), w)").expect("parse");
    let nf = AppSubstLanguage::dovetail_normal_term(term.as_ref(), MAX_ITERS, MAX_NODES)
        .unwrap_or_else(|e| panic!("dovetail_normal_term returned Err: {e}"));
    assert_eq!(lang.format_term(nf.as_ref()), "ap(w , w)");
}
