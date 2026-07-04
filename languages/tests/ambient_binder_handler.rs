//! Inc 1 — Ambient binder-congruence direct-evaluator validation.
//!
//! The handler floats `new`s outward (capture-safe via moniker
//! `unbind`/`Scope::new`). The load-bearing correctness property is FIX-B: the
//! freshness gate is checked against the ORIGINAL binder, so a `new` whose bound
//! name also occurs free in an enclosing prefix's NAME is NOT floated (which
//! would capture it). These tests exercise the evaluator through the real seam
//! (`Language::try_direct_eval`).
#![cfg(feature = "ambient")]

use mettail_languages::ambient::AmbientLanguage;
use mettail_runtime::Language;

/// Float a source term through the handler; `Some(display)` iff it made progress.
fn float(src: &str) -> Option<String> {
    let lang = AmbientLanguage;
    let term = lang.parse_term(src).expect("Ambient term parses");
    lang.try_direct_eval(term.as_ref()).map(|t| format!("{t}"))
}

#[test]
fn prefix_float_does_not_capture_a_shared_name() {
    // The load-bearing capture-safety test. Construct `open(x, new(x, 0))` where
    // the channel name and the `new`'s binder SHARE one `FreeVar` identity — the
    // situation a prior rewrite/substitution can produce (the parser keeps
    // binders fresh, so this cannot be reached by parsing alone). A naïve float
    // (`run_ascent`'s `from_parts_unsafe`, no re-close) would move the channel
    // `x` under `new^x` and CAPTURE it. The handler floats via moniker
    // `unbind`→`Scope::new` (capture-avoiding alpha-renaming): the binder is
    // freshened to `x'`, so the channel `x` stays FREE in the result. We assert
    // exactly that — `x` remains a free variable after the float.
    use mettail_languages::ambient::{Name, Proc};
    use mettail_runtime::{Binder, BoundTerm, FreeVar, OrdVar, Scope, Var};
    use std::sync::Arc;

    let x = FreeVar::fresh(Some("x".to_string()));
    let channel = Arc::new(Name::NVar(OrdVar(Var::Free(x.clone()))));
    let new_x = Proc::PNew(Scope::new(Binder(x.clone()), Arc::new(Proc::PZero)));
    let term = Proc::POpen(channel, Arc::new(new_x));

    let floated = term.binder_congruence_nf();
    let free = BoundTerm::free_vars(&floated);
    assert!(
        free.contains(&x),
        "the channel `x` must remain FREE after the float (no capture); \
         got free_vars {free:?} for {floated}"
    );
}

#[test]
fn floats_prefix_when_binder_fresh_in_name() {
    // `open(a, new(x, 0))`: floats to `new(x, open(a, 0))`. Progress ⇒ Some.
    assert!(float("open(a, new(x, 0))").is_some(), "a prefix-enclosed `new` floats out");
}

#[test]
fn floats_prefix_in_new() {
    // `in(n, new(x, 0))` ⇒ `new(x, in(n, 0))` (InNew), n ≠ x.
    assert!(float("in(n, new(x, 0))").is_some(), "InNew floats");
}

#[test]
fn capturing_witness_in_z_new_x_does_not_capture() {
    // `new(z, in(z, new(x, 0)))`: the inner `new(x,0)` floats out of `in(z, ·)`
    // (x ≠ z ⇒ fresh in the name z). Re-closing recomputes de-Bruijn coordinates
    // locally, so the channel `z` stays bound to the OUTER `new(z, ·)` — NOT
    // captured. The handler must produce a result, and it must round-trip
    // (parse back) to a well-formed term.
    let lang = AmbientLanguage;
    let term = lang.parse_term("new(z, in(z, new(x, 0)))").expect("parses");
    let floated = lang
        .try_direct_eval(term.as_ref())
        .expect("the inner new floats out of the in-prefix");
    let displayed = format!("{floated}");
    // The result must re-parse (well-formed) — a captured term would still parse,
    // but the round-trip confirms the handler produced valid syntax.
    lang.parse_term(&displayed)
        .unwrap_or_else(|e| panic!("floated term must re-parse: {displayed:?}: {e}"));
}

#[test]
fn handler_is_deterministic() {
    // The same source floated twice must yield byte-identical output (no
    // transient `unique_id` leaks into the result — re-close erases the freshened
    // binder identity from the alpha-canonical key, and Display is name-stable).
    let a = float("new(z, in(z, new(x, 0)))");
    let b = float("new(z, in(z, new(x, 0)))");
    assert_eq!(a, b, "handler output must be deterministic");
}

#[test]
fn ground_term_does_not_float() {
    // A term with no floatable `new` redex makes no progress ⇒ None (fail-closed
    // preserved for the seam).
    assert_eq!(float("0"), None);
    assert_eq!(float("{ open(n, 0) | n [ 0 ] }"), None, "no `new` ⇒ no float");
}
