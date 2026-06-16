//! Pin (Inc 3): rhocalc — a message-passing process calculus (`POutput`/`Comm`,
//! MULTI-binder `PNew ^[xs]` / `PInputs ^[xs]`) — does NOT get the in-engine
//! binder NativeHandler. The `should_emit_binder_congruence` gate requires a
//! surface SINGLE-binder over the primary category (Ambient's `PNew . ^x`), which
//! rhocalc lacks, so no handler is generated and rhocalc's binders/COMM remain
//! host-routed (the `RhoNativeJoin` disposition). This guards the gate against
//! ever flipping a host-backed language onto the Ambient (host-less) binder path.
//!
//! Observable: rhocalc's `try_direct_eval` is the native-fold version — it
//! handles only native (Int) folds and returns `None` for a process term; it
//! never floats a `new`. Contrast Ambient, whose `try_direct_eval` IS the
//! binder-congruence handler (see `ambient_binder_handler.rs`).
#![cfg(all(feature = "rhocalc", feature = "dovetail-codegen"))]

use mettail_languages::rhocalc::RhoCalcLanguage;
use mettail_runtime::Language;

#[test]
fn rhocalc_try_direct_eval_has_no_in_engine_binder_handler() {
    let lang = RhoCalcLanguage;
    // A process term: rhocalc's `try_direct_eval` returns `None` (it is the
    // native-fold version, not a binder-congruence handler). If the gate wrongly
    // emitted the handler for rhocalc, `try_direct_eval` would instead route a
    // process term through `binder_congruence_nf_term`.
    let term = lang.parse_term("0").expect("rhocalc parses 0");
    assert!(
        lang.try_direct_eval(term.as_ref()).is_none(),
        "rhocalc must have NO in-engine binder float handler (it is host-routed)"
    );

    // A scope-extrusion-shaped redex still has no in-engine float either — rhocalc
    // routes `new`/COMM to the host, so a `new`-bearing process is not floated.
    let new_bag = lang
        .parse_term("{ new(x) in { 0 } | 0 }")
        .expect("rhocalc parses a new-in-parallel redex");
    assert!(
        lang.try_direct_eval(new_bag.as_ref()).is_none(),
        "rhocalc does not float a `new` out of a parallel bag (host-routed)"
    );
}
