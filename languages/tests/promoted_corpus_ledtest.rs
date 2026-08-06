//! **Promoted counterexamples for `ledtest`** — every seed its proptest corpus records,
//! as a named regression test.
//!
//! # Where these came from, and why they are here
//!
//! `languages/tests/gen_ledtest_prop.proptest-regressions` holds 5 seed(s) for inputs
//! that ONCE FALSIFIED a property of this grammar, each with the shrunk counterexample
//! recorded beside it. proptest replays those seeds — but only while the corpus keeps the
//! name the language gives it, and only as an anonymous seed nobody can cite in a bug
//! report or run on its own. A named `#[test]` per entry gives each counterexample an
//! identity, a failure message and a place in the ordinary test run.
//!
//! # How the term was recovered
//!
//! NOT by replaying the seed. proptest persists the seed of the case's FIRST generated
//! input and separately records the SHRUNK value's `Debug`, so replay reconstructs a
//! different — usually larger — term. The measurement is in `testkit/src/ctor.rs`. The
//! `# shrinks to` text is therefore the only complete record of the counterexample, and
//! `testkit`'s harvester reads it back through the constructor schema the `rust_ctor` pass
//! emits during macro expansion:
//!
//! ```text
//! cargo run -p testkit --bin harvest_proptest_corpus -- \
//!     target/generated/ledtest/rust_ctor.rs \
//!     languages/tests/gen_ledtest_prop.proptest-regressions
//! ```
//!
//! # The three assertions, and which one carries the weight
//!
//! 1. the term CONSTRUCTS;
//! 2. ★ its **canonicalised `Debug` equals the corpus-recorded text**, carried here as a
//!    literal. This is the anti-vacuity core: a test that merely constructed *some* term
//!    would pass while proving nothing. [`canonicalize_debug`] quotients out exactly two
//!    things, and both are properties of the PROCESS rather than of the term — `UniqueId(n)`
//!    (a global counter; `FreeVar` equality is by `unique_id` alone, and the generated
//!    strategies mint every variable through the thread-local name cache, so the NAME fixes
//!    the identity) and the ORDER of entries inside a hash container (a `HashBag` is a
//!    multiset whose `PartialEq` already ignores order). Every other byte must match;
//! 3. the properties the generated suite checks for this category.
//!
//! ★ Assertion 2 is HARNESS-INDEPENDENT by construction, and that is not incidental. Under
//! `cargo test` the whole binary shares one process, so an edit to one test shifts the
//! global `UniqueId` counter for every later one, which reorders hash containers; under
//! `cargo nextest` each test is its own process and the counter restarts. Quotienting both
//! process properties is exactly what makes the two harnesses agree. This file is verified
//! under BOTH.
//!
//! # RED proof
//!
//! Mutate one constructor in any test below — swap a nullary for a sibling, perturb an
//! integer — and assertion 2 goes RED, while every other test in the file still passes. The
//! unmutated terms are the control.

#![allow(clippy::needless_borrow)]

use mettail_testkit::ctor::canonicalize_debug;
// Task #11: `ledtest`'s grammar is a test FIXTURE, not a production language — its
// definition lives in `languages/tests/definitions/led_test.rs` rather than in the `languages`
// library, so it is `#[path]`-included here. This binary is a CONSUMER: it deliberately does
// NOT invoke the `ledtest_generated_tests!` wrapper, because the definition's DESIGNATED HOST is `languages/tests/led_delegation_tests.rs` and is the sole
// invoker, so the generated suite stays single-instanced across the workspace.
#[path = "definitions/led_test.rs"]
mod ledtest;
use crate::ledtest::*;

/// Corpus entry 0 — seed `cc a241e2edc4aeebb499b90069779619afd206dac5e977cbce7b40beb5962ff1b8`.
///
/// Recorded counterexample, verbatim from the corpus:
/// ```text
/// term = NegNum(NumLit(1296911694))
/// ```
#[test]
fn corpus_0_num() {
    mettail_runtime::clear_var_cache();
    // 1 — the term CONSTRUCTS.
    let term: Num = Num::NegNum(std::sync::Arc::new(Num::NumLit(1296911694i32)));

    // 2 — ANTI-VACUITY. The reconstructed term's normalised Debug must equal the
    //     text the corpus recorded, character for character. This is what makes
    //     "passes because it built the wrong term" impossible. Only
    //     `UniqueId(n)` and the ORDER of hash-container entries are quotiented
    //     out, and both are properties of the PROCESS rather than of the term:
    //     `UniqueId` comes from a global counter (and `FreeVar` equality is by
    //     unique_id alone, with the name fixing the identity through the var
    //     cache), and a `HashBag` is a multiset whose `PartialEq` ignores order.
    let recorded = "NegNum(NumLit(1296911694))";
    assert_eq!(
        canonicalize_debug(&format!("{:?}", term)),
        recorded,
        "the reconstructed term is not the recorded counterexample"
    );

    // 3 — the properties the corpus's generated suite checks for this category.
    let _ = format!("{:?}", term); // <cat>_debug_does_not_panic
    let _ = format!("{}", term); // <cat>_display_does_not_panic
    assert_eq!(term.clone(), term); // <cat>_clone_eq
}

/// Corpus entry 1 — seed `cc e55c3e0f76c450afcf7f77131d07fb218d219147918271b992f7879a5f43f827`.
///
/// Recorded counterexample, verbatim from the corpus:
/// ```text
/// term = PredToNum(EqNum(PredToNum(BoolLit(true)), PredToNum(BoolLit(true))))
/// ```
#[test]
fn corpus_1_num() {
    mettail_runtime::clear_var_cache();
    // 1 — the term CONSTRUCTS.
    let term: Num = Num::PredToNum(std::sync::Arc::new(Pred::EqNum(
        std::sync::Arc::new(Num::PredToNum(std::sync::Arc::new(Pred::BoolLit(true)))),
        std::sync::Arc::new(Num::PredToNum(std::sync::Arc::new(Pred::BoolLit(true)))),
    )));

    // 2 — ANTI-VACUITY. The reconstructed term's normalised Debug must equal the
    //     text the corpus recorded, character for character. This is what makes
    //     "passes because it built the wrong term" impossible. Only
    //     `UniqueId(n)` and the ORDER of hash-container entries are quotiented
    //     out, and both are properties of the PROCESS rather than of the term:
    //     `UniqueId` comes from a global counter (and `FreeVar` equality is by
    //     unique_id alone, with the name fixing the identity through the var
    //     cache), and a `HashBag` is a multiset whose `PartialEq` ignores order.
    let recorded = "PredToNum(EqNum(PredToNum(BoolLit(true)), PredToNum(BoolLit(true))))";
    assert_eq!(
        canonicalize_debug(&format!("{:?}", term)),
        recorded,
        "the reconstructed term is not the recorded counterexample"
    );

    // 3 — the properties the corpus's generated suite checks for this category.
    let _ = format!("{:?}", term); // <cat>_debug_does_not_panic
    let _ = format!("{}", term); // <cat>_display_does_not_panic
    assert_eq!(term.clone(), term); // <cat>_clone_eq
}

/// Corpus entry 2 — seed `cc ec7bec4ce46db364d17cca03084c568d44f55dadbc618237e6f6aa475d1870ac`.
///
/// Recorded counterexample, verbatim from the corpus:
/// ```text
/// term = CastNum(AddNum(PredToNum(BoolLit(true)), AddNum(NumLit(1275159884),
/// NumLit(1699479909))))
/// ```
#[test]
fn corpus_2_expr() {
    mettail_runtime::clear_var_cache();
    // 1 — the term CONSTRUCTS.
    let term: Expr = Expr::CastNum(std::sync::Arc::new(Num::AddNum(
        std::sync::Arc::new(Num::PredToNum(std::sync::Arc::new(Pred::BoolLit(true)))),
        std::sync::Arc::new(Num::AddNum(
            std::sync::Arc::new(Num::NumLit(1275159884i32)),
            std::sync::Arc::new(Num::NumLit(1699479909i32)),
        )),
    )));

    // 2 — ANTI-VACUITY. The reconstructed term's normalised Debug must equal the
    //     text the corpus recorded, character for character. This is what makes
    //     "passes because it built the wrong term" impossible. Only
    //     `UniqueId(n)` and the ORDER of hash-container entries are quotiented
    //     out, and both are properties of the PROCESS rather than of the term:
    //     `UniqueId` comes from a global counter (and `FreeVar` equality is by
    //     unique_id alone, with the name fixing the identity through the var
    //     cache), and a `HashBag` is a multiset whose `PartialEq` ignores order.
    let recorded =
        "CastNum(AddNum(PredToNum(BoolLit(true)), AddNum(NumLit(1275159884), NumLit(1699479909))))";
    assert_eq!(
        canonicalize_debug(&format!("{:?}", term)),
        recorded,
        "the reconstructed term is not the recorded counterexample"
    );

    // 3 — the properties the corpus's generated suite checks for this category.
    let _ = format!("{:?}", term); // <cat>_debug_does_not_panic
    let _ = format!("{}", term); // <cat>_display_does_not_panic
    assert_eq!(term.clone(), term); // <cat>_clone_eq
}

/// Corpus entry 3 — seed `cc bac9d5a7392970edfb33ab4b9964ed880b13b9ca08fdc80ec56b3f634eeecc14`.
///
/// Recorded counterexample, verbatim from the corpus:
/// ```text
/// term = AndPred(EqNum(NegNum(NumLit(0)), NumLit(0)), BoolLit(false))
/// ```
#[test]
fn corpus_3_pred() {
    mettail_runtime::clear_var_cache();
    // 1 — the term CONSTRUCTS.
    let term: Pred = Pred::AndPred(
        std::sync::Arc::new(Pred::EqNum(
            std::sync::Arc::new(Num::NegNum(std::sync::Arc::new(Num::NumLit(0i32)))),
            std::sync::Arc::new(Num::NumLit(0i32)),
        )),
        std::sync::Arc::new(Pred::BoolLit(false)),
    );

    // 2 — ANTI-VACUITY. The reconstructed term's normalised Debug must equal the
    //     text the corpus recorded, character for character. This is what makes
    //     "passes because it built the wrong term" impossible. Only
    //     `UniqueId(n)` and the ORDER of hash-container entries are quotiented
    //     out, and both are properties of the PROCESS rather than of the term:
    //     `UniqueId` comes from a global counter (and `FreeVar` equality is by
    //     unique_id alone, with the name fixing the identity through the var
    //     cache), and a `HashBag` is a multiset whose `PartialEq` ignores order.
    let recorded = "AndPred(EqNum(NegNum(NumLit(0)), NumLit(0)), BoolLit(false))";
    assert_eq!(
        canonicalize_debug(&format!("{:?}", term)),
        recorded,
        "the reconstructed term is not the recorded counterexample"
    );

    // 3 — the properties the corpus's generated suite checks for this category.
    let _ = format!("{:?}", term); // <cat>_debug_does_not_panic
    let _ = format!("{}", term); // <cat>_display_does_not_panic
    assert_eq!(term.clone(), term); // <cat>_clone_eq
}

/// Corpus entry 4 — seed `cc c2a4d37839b38fb8a897fa5d95f45c634784b4813a6b8b3b740852178a8e3630`.
///
/// Recorded counterexample, verbatim from the corpus:
/// ```text
/// term = EqNum(NegNum(ExprToNum(EVar(OrdVar(Free(FreeVar { unique_id: UniqueId(115),
/// pretty_name: Some("a") }))))), PredToNum(AndPred(BoolLit(true), BoolLit(false))))
/// ```
#[test]
fn corpus_4_pred() {
    mettail_runtime::clear_var_cache();
    // 1 — the term CONSTRUCTS.
    let term: Pred = Pred::EqNum(
        std::sync::Arc::new(Num::NegNum(std::sync::Arc::new(Num::ExprToNum(std::sync::Arc::new(
            Expr::EVar(mettail_runtime::OrdVar(mettail_runtime::Var::Free(
                mettail_runtime::get_or_create_var("a"),
            ))),
        ))))),
        std::sync::Arc::new(Num::PredToNum(std::sync::Arc::new(Pred::AndPred(
            std::sync::Arc::new(Pred::BoolLit(true)),
            std::sync::Arc::new(Pred::BoolLit(false)),
        )))),
    );

    // 2 — ANTI-VACUITY. The reconstructed term's normalised Debug must equal the
    //     text the corpus recorded, character for character. This is what makes
    //     "passes because it built the wrong term" impossible. Only
    //     `UniqueId(n)` and the ORDER of hash-container entries are quotiented
    //     out, and both are properties of the PROCESS rather than of the term:
    //     `UniqueId` comes from a global counter (and `FreeVar` equality is by
    //     unique_id alone, with the name fixing the identity through the var
    //     cache), and a `HashBag` is a multiset whose `PartialEq` ignores order.
    let recorded = "EqNum(NegNum(ExprToNum(EVar(OrdVar(Free(FreeVar { unique_id: UniqueId(_), pretty_name: Some(\"a\") }))))), PredToNum(AndPred(BoolLit(true), BoolLit(false))))";
    assert_eq!(
        canonicalize_debug(&format!("{:?}", term)),
        recorded,
        "the reconstructed term is not the recorded counterexample"
    );

    // 3 — the properties the corpus's generated suite checks for this category.
    let _ = format!("{:?}", term); // <cat>_debug_does_not_panic
    let _ = format!("{}", term); // <cat>_display_does_not_panic
    assert_eq!(term.clone(), term); // <cat>_clone_eq
}
