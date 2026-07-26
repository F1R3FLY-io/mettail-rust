//! Generality gate for macro-codegen extension **E1** (generalized substitution lowering).
//!
//! Exercises the `AppSubst` src fixture (`mettail_languages::appsubst`) — a tiny binder calculus
//! that is NOT Lambda (different constructor names `Abs`/`Ap`, different concrete syntax `abs x. b`
//! / `ap(f, a)`) with a binder `[T -> T]` and an `(eval <binder> <arg>)` substitution rewrite. If
//! E1's substitution detector / dispatch / progress-weights were keyed on Lambda's `Lam`/`App`
//! names (or on `name == "Lambda"`) rather than derived from `LanguageDef`, this language would NOT
//! β-reduce. It does — proving the mechanism is fully generalized.
//!
//! `AppSubst` is a `src` fixture (`languages/src/appsubst.rs`), not a test-local `language!`: the
//! macro emits a crate-coupled `src/bin/simulate_<lang>.rs` for every invocation, so a test-local
//! invocation would write a bin referencing a nonexistent `mettail_languages::appsubst` module and
//! break `cargo build -p languages`. See the fixture's module doc.
// Task #11 (extended 2026-07-26): the `appsubst` LIBRARY FEATURE is gone (the definition
// is test-hosted now), so naming it in this gate would make the gate unsatisfiable and
// SILENTLY delete the whole generality suite. Only the `dovetail-codegen` half remains a
// real condition; the definition itself is `#[path]`-included unconditionally below.
#![cfg(feature = "dovetail-codegen")]

// Task #11 (extended 2026-07-26): `AppSubst` is a binder-calculus FIXTURE (the E1 generality gate), not a production language, so its
// definition lives in `languages/tests/definitions/appsubst.rs` rather than in the `languages`
// library (`languages/src/` is production-only).
//
// This file is its DESIGNATED HOST: it declares the definition module and is the one and only
// invoker of the opt-in `appsubst_generated_tests!` wrapper, which materializes the
// macro-generated sections that used to be written to `languages/tests/gen_appsubst_*.rs`.
// Other consumers `#[path]`-include the same definition WITHOUT invoking the wrapper, so the
// generated tests exist exactly once across the whole suite.
#[path = "definitions/appsubst.rs"]
mod appsubst;

appsubst::appsubst_generated_tests!(crate::appsubst);

use appsubst::AppSubstLanguage;
use mettail_runtime::Language;

const MAX_ITERS: usize = 64;
const MAX_NODES: usize = 1_000_000;

#[test]
fn synthetic_appsubst_beta_report_is_ok() {
    let lang = AppSubstLanguage;
    let term = lang
        .parse_term("ap(abs x. x, y)")
        .expect("parse identity application");
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
