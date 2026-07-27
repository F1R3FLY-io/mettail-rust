//! Pin (Inc 3): rholang — a message-passing process calculus (`POutput`/`Comm`,
//! MULTI-binder `PNew ^[xs]` / `PInputs ^[xs]`) — does NOT get the in-engine
//! binder-congruence direct evaluator. The `should_emit_binder_congruence` gate requires a
//! surface SINGLE-binder over the primary category (Ambient's `PNew . ^x`), which
//! rholang lacks, so no direct binder evaluator is generated and rholang's binders/COMM remain
//! on the `RhoNativeJoin`/semantic-predicate boundary. This guards the gate against
//! ever flipping a RhoNativeJoin-backed language onto the Ambient direct binder path.
//!
//! Observable: rholang's `try_direct_eval` is the native-fold version — it
//! handles only native (Int) folds and returns `None` for a process term; it
//! never floats a `new`. Contrast Ambient, whose `try_direct_eval` IS the
//! binder-congruence handler (see `ambient_binder_handler.rs`).
#![cfg(all(feature = "rholang", feature = "dovetail-codegen"))]

use mettail_languages::rholang::RholangLanguage;
use mettail_runtime::Language;

#[test]
fn rholang_try_direct_eval_has_no_in_engine_binder_handler() {
    let lang = RholangLanguage;
    // A process term: rholang's `try_direct_eval` returns `None` (it is the
    // native-fold version, not a binder-congruence evaluator). If the gate wrongly
    // emitted the evaluator for rholang, `try_direct_eval` would instead route a
    // process term through `binder_congruence_nf_term`.
    let term = lang.parse_term("0").expect("rholang parses 0");
    assert!(
        lang.try_direct_eval(term.as_ref()).is_none(),
        "rholang must have NO in-engine binder float evaluator"
    );

    // A scope-extrusion-shaped redex still has no in-engine float either — rholang
    // keeps `new`/COMM behind the RhoNativeJoin boundary, so a `new`-bearing process is not floated.
    let new_bag = lang
        .parse_term("{ new x in { 0 } | 0 }")
        .expect("rholang parses a new-in-parallel redex");
    assert!(
        lang.try_direct_eval(new_bag.as_ref()).is_none(),
        "rholang does not float a `new` out of a parallel bag"
    );
}
