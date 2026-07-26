//! B8 (2026-04-28): smoke test for refinement-type predicate codegen.
//!
//! The synthetic `RefinementSmoke` grammar declares
//! `PosInt = { x: Int | x > 0 }`. The `language!` macro emits a
//! `register_refinements()` function (per `wpda_codegen::refinement`)
//! that registers the closure with the runtime registry; calling
//! `evaluate_refinement_predicate("PosInt", &v)` then evaluates the
//! lowered closure body against `v`.
//!
//! End-to-end parse-side enforcement requires action-wrapping at every
//! site that produces a refined-category value. The atomic-literal site
//! (`emit_literal_patterned_action`) is wrapped today; cross-cat
//! injection rules (`IntToPosInt . i:Int |- i : PosInt`) carry a
//! `Box<Int>` payload and need a per-rule pattern-match on the inner
//! variant to surface the native value — that follow-up is tracked
//! separately. The tests below exercise the closure body via the public
//! registry surface, which is the principal B8 deliverable.

// Task #11 (extended 2026-07-26): `RefinementSmoke` is a refinement-predicate codegen FIXTURE, not a production language, so its
// definition lives in `languages/tests/definitions/refinementsmoke.rs` rather than in the `languages`
// library (`languages/src/` is production-only).
//
// This file is its DESIGNATED HOST: it declares the definition module and is the one and only
// invoker of the opt-in `refinementsmoke_generated_tests!` wrapper, which materializes the
// macro-generated sections that used to be written to `languages/tests/gen_refinementsmoke_*.rs`.
// Other consumers `#[path]`-include the same definition WITHOUT invoking the wrapper, so the
// generated tests exist exactly once across the whole suite.
#[path = "definitions/refinementsmoke.rs"]
mod refinementsmoke;

refinementsmoke::refinementsmoke_generated_tests!(crate::refinementsmoke);

use refinementsmoke::register_refinements;
use mettail_runtime::{clear_refinement_registry, evaluate_refinement_predicate};

#[test]
fn refinement_predicate_admits_in_domain_value() {
    clear_refinement_registry();
    register_refinements();
    let v: i32 = 5;
    assert!(
        evaluate_refinement_predicate("PosInt", &v),
        "5 should satisfy PosInt = {{ x: Int | x > 0 }}",
    );
    clear_refinement_registry();
}

#[test]
fn refinement_predicate_rejects_zero_and_negative() {
    clear_refinement_registry();
    register_refinements();
    let zero: i32 = 0;
    let neg: i32 = -3;
    assert!(
        !evaluate_refinement_predicate("PosInt", &zero),
        "0 should NOT satisfy PosInt = {{ x: Int | x > 0 }}",
    );
    assert!(
        !evaluate_refinement_predicate("PosInt", &neg),
        "-3 should NOT satisfy PosInt = {{ x: Int | x > 0 }}",
    );
    clear_refinement_registry();
}

#[test]
fn refinement_predicate_rejects_wrong_type() {
    clear_refinement_registry();
    register_refinements();
    // The PosInt closure downcasts to i32; passing a String should fail.
    let s: String = "5".to_string();
    assert!(
        !evaluate_refinement_predicate("PosInt", &s),
        "non-i32 value must fail downcast → false",
    );
    clear_refinement_registry();
}

#[test]
fn unregistered_refinement_returns_true_conservatively() {
    clear_refinement_registry();
    // Without `register_refinements()`, the registry is empty and any
    // lookup returns `true` (conservative). This is the "no predicate
    // installed → don't reject" contract documented in
    // `runtime/src/refinement.rs::evaluate_refinement_predicate`.
    let v: i32 = 5;
    assert!(
        evaluate_refinement_predicate("PosInt", &v),
        "unregistered name should return true (conservative default)",
    );
}
