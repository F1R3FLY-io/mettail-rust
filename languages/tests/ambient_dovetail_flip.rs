//! Ambient's Dovetail flip (Inc 1–3).
//!
//! Ambient's structural-congruence EQUATIONS carry the `PNew ^x` binder
//! (`NewComm`) and freshness side conditions (`ScopeExtrusion`, `InNew`,
//! `OutNew`, `OpenNew`, `AmbNew`). These are now discharged by the moniker
//! binder-congruence NativeHandler (float `new`s outward, capture-safe via
//! `unbind`/`Scope::new`), composed with the in-engine AC reduction
//! (`InRule`/`OutRule`/`OpenRule`). The generated compiler therefore produces a
//! COMPLETE report instead of failing closed on the unlowered equations — the
//! flip that `ambient_dovetail_compiler_fails_closed_*` previously pinned as
//! not-yet-reachable.
#![cfg(all(feature = "ambient", feature = "dovetail-codegen"))]

use mettail_languages::ambient::AmbientLanguage;
use mettail_runtime::Language;

#[test]
fn ambient_dovetail_compiler_flips_via_native_handler_and_in_engine_ac() {
    let lang = AmbientLanguage;
    // `{ open(n, 0) | n[0] }`: no `new`, so the handler floats nothing and the
    // `OpenRule` AC reduction `{open(N,P), N[Q], ...rest} ~> {P, Q, ...rest}`
    // fires in-engine. The compiler now produces a report rather than `Err`.
    let term = lang
        .parse_term("{ open(n, 0) | n [ 0 ] }")
        .expect("Ambient parses an open redex");
    let report = AmbientLanguage::dovetail_report_for(term.as_ref(), 64, 1_000_000)
        .expect("Ambient now lowers via the binder NativeHandler + in-engine AC reduction");
    assert!(
        !report.roots.is_empty(),
        "the flipped Ambient Dovetail report must carry at least one root"
    );
    assert!(
        report.is_complete(),
        "the acyclic open-redex reduction must report Complete, not BoundedByCycleCut"
    );
}

#[test]
fn ambient_dovetail_reduces_an_in_rule_redex() {
    let lang = AmbientLanguage;
    // InRule: `{ n[{ in(m, 0) }] | m[0] }` ~> `{ m[{ n[{0}] | 0 }] }` — an ambient
    // `n` carrying an `in(m,·)` enters the sibling ambient `m`. Exercises the AC
    // reduction half on a nested-ambient redex (not just OpenRule).
    let term = lang
        .parse_term("{ n [ { in(m, 0) } ] | m [ 0 ] }")
        .expect("Ambient parses an in-rule redex");
    let report = AmbientLanguage::dovetail_report_for(term.as_ref(), 64, 1_000_000)
        .expect("the InRule AC reduction fires in-engine and the report compiles");
    assert!(!report.roots.is_empty());
    assert!(report.is_complete(), "the acyclic InRule reduction must report Complete");
}

#[test]
fn ambient_dovetail_flips_a_scope_extrusion_redex() {
    let lang = AmbientLanguage;
    // `{ new(x, in(m, 0)) | m[0] }`: the handler floats `new(x, ·)` out of the
    // parallel bag (ScopeExtrusion; `x` fresh in `m[0]`), exposing the soup —
    // `new(x, { in(m, 0) | m[0] })` — and the report compiles. This exercises the
    // binder float (not just the AC half).
    let term = lang
        .parse_term("{ new(x, in(m, 0)) | m [ 0 ] }")
        .expect("Ambient parses a scope-extrusion redex");
    let report = AmbientLanguage::dovetail_report_for(term.as_ref(), 64, 1_000_000)
        .expect("the new floats out via ScopeExtrusion and the report compiles");
    assert!(!report.roots.is_empty());
}
