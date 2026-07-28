//! **Promoted counterexamples for `class2smoke`** — every seed its proptest corpus records,
//! as a named regression test.
//!
//! # Where these came from, and why they are here
//!
//! `languages/tests/gen_class2smoke_prop.proptest-regressions` holds 3 seed(s) for inputs
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
//!     target/generated/class2smoke/rust_ctor.rs \
//!     languages/tests/gen_class2smoke_prop.proptest-regressions
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
// Task #11: `class2smoke`'s grammar is a test FIXTURE, not a production language — its
// definition lives in `languages/tests/definitions/class2smoke.rs` rather than in the `languages`
// library, so it is `#[path]`-included here. This binary is a CONSUMER: it deliberately does
// NOT invoke the `class2smoke_generated_tests!` wrapper, because the definition's DESIGNATED HOST is `languages/tests/class2_binder_with_collection_smoke.rs` and is the sole
// invoker, so the generated suite stays single-instanced across the workspace.
#[path = "definitions/class2smoke.rs"]
mod class2smoke;
use crate::class2smoke::*;

/// Corpus entry 0 — seed `cc 4ebee1f7c26472a3ccbd799717fd443bc19361be0a3ca65553db36f9c66af857`.
///
/// Recorded counterexample, verbatim from the corpus:
/// ```text
/// term = Choose(Choose(PZero, []), [Choose(PVar(OrdVar(Free(FreeVar { unique_id: UniqueId(0),
/// pretty_name: Some("a") }))), [])])
/// ```
#[test]
fn corpus_0_proc() {
    mettail_runtime::clear_var_cache();
    // 1 — the term CONSTRUCTS.
    let term: Proc = Proc::Choose(std::sync::Arc::new(Proc::Choose(std::sync::Arc::new(Proc::PZero), vec![])), vec![Proc::Choose(std::sync::Arc::new(Proc::PVar(mettail_runtime::OrdVar(mettail_runtime::Var::Free(mettail_runtime::get_or_create_var("a"))))), vec![])]);

    // 2 — ANTI-VACUITY. The reconstructed term's normalised Debug must equal the
    //     text the corpus recorded, character for character. This is what makes
    //     "passes because it built the wrong term" impossible. Only
    //     `UniqueId(n)` and the ORDER of hash-container entries are quotiented
    //     out, and both are properties of the PROCESS rather than of the term:
    //     `UniqueId` comes from a global counter (and `FreeVar` equality is by
    //     unique_id alone, with the name fixing the identity through the var
    //     cache), and a `HashBag` is a multiset whose `PartialEq` ignores order.
    let recorded = "Choose(Choose(PZero, []), [Choose(PVar(OrdVar(Free(FreeVar { unique_id: UniqueId(_), pretty_name: Some(\"a\") }))), [])])";
    assert_eq!(
        canonicalize_debug(&format!("{:?}", term)),
        recorded,
        "the reconstructed term is not the recorded counterexample"
    );

    // 3 — the properties the corpus's generated suite checks for this category.
    let _ = format!("{:?}", term);            // <cat>_debug_does_not_panic
    let _ = format!("{}", term);              // <cat>_display_does_not_panic
    assert_eq!(term.clone(), term);           // <cat>_clone_eq
}

/// Corpus entry 1 — seed `cc 4756f946a6070a449c3d0568c24b0f233e36a568aa3e556d0a663d29d57c06e7`.
///
/// Recorded counterexample, verbatim from the corpus:
/// ```text
/// term = Choose(Choose(PVar(OrdVar(Free(FreeVar { unique_id: UniqueId(0), pretty_name:
/// Some("a") }))), [PZero]), [PVar(OrdVar(Free(FreeVar { unique_id: UniqueId(0), pretty_name:
/// Some("a") }))), PVar(OrdVar(Free(FreeVar { unique_id: UniqueId(0), pretty_name: Some("a")
/// }))), Choose(Choose(PZero, []), [PZero])])
/// ```
#[test]
fn corpus_1_proc() {
    mettail_runtime::clear_var_cache();
    // 1 — the term CONSTRUCTS.
    let term: Proc = Proc::Choose(std::sync::Arc::new(Proc::Choose(std::sync::Arc::new(Proc::PVar(mettail_runtime::OrdVar(mettail_runtime::Var::Free(mettail_runtime::get_or_create_var("a"))))), vec![Proc::PZero])), vec![Proc::PVar(mettail_runtime::OrdVar(mettail_runtime::Var::Free(mettail_runtime::get_or_create_var("a")))), Proc::PVar(mettail_runtime::OrdVar(mettail_runtime::Var::Free(mettail_runtime::get_or_create_var("a")))), Proc::Choose(std::sync::Arc::new(Proc::Choose(std::sync::Arc::new(Proc::PZero), vec![])), vec![Proc::PZero])]);

    // 2 — ANTI-VACUITY. The reconstructed term's normalised Debug must equal the
    //     text the corpus recorded, character for character. This is what makes
    //     "passes because it built the wrong term" impossible. Only
    //     `UniqueId(n)` and the ORDER of hash-container entries are quotiented
    //     out, and both are properties of the PROCESS rather than of the term:
    //     `UniqueId` comes from a global counter (and `FreeVar` equality is by
    //     unique_id alone, with the name fixing the identity through the var
    //     cache), and a `HashBag` is a multiset whose `PartialEq` ignores order.
    let recorded = "Choose(Choose(PVar(OrdVar(Free(FreeVar { unique_id: UniqueId(_), pretty_name: Some(\"a\") }))), [PZero]), [PVar(OrdVar(Free(FreeVar { unique_id: UniqueId(_), pretty_name: Some(\"a\") }))), PVar(OrdVar(Free(FreeVar { unique_id: UniqueId(_), pretty_name: Some(\"a\") }))), Choose(Choose(PZero, []), [PZero])])";
    assert_eq!(
        canonicalize_debug(&format!("{:?}", term)),
        recorded,
        "the reconstructed term is not the recorded counterexample"
    );

    // 3 — the properties the corpus's generated suite checks for this category.
    let _ = format!("{:?}", term);            // <cat>_debug_does_not_panic
    let _ = format!("{}", term);              // <cat>_display_does_not_panic
    assert_eq!(term.clone(), term);           // <cat>_clone_eq
}

/// Corpus entry 2 — seed `cc 3698d656e8b4e4b8c418a616559ce6aaa51db97ddc3d916cb84281ffe1d7e9f2`.
///
/// Recorded counterexample, verbatim from the corpus:
/// ```text
/// term = Choose(Choose(PVar(OrdVar(Free(FreeVar { unique_id: UniqueId(0), pretty_name:
/// Some("a") }))), [PVar(OrdVar(Free(FreeVar { unique_id: UniqueId(0), pretty_name: Some("a")
/// }))), PVar(OrdVar(Free(FreeVar { unique_id: UniqueId(0), pretty_name: Some("a") })))]),
/// [Choose(PVar(OrdVar(Free(FreeVar { unique_id: UniqueId(0), pretty_name: Some("a") }))),
/// [PVar(OrdVar(Free(FreeVar { unique_id: UniqueId(0), pretty_name: Some("a") }))),
/// PVar(OrdVar(Free(FreeVar { unique_id: UniqueId(0), pretty_name: Some("a") })))]),
/// Choose(Choose(PZero, [PZero]), [Choose(PVar(OrdVar(Free(FreeVar { unique_id: UniqueId(0),
/// pretty_name: Some("a") }))), [PZero, PZero]), PVar(OrdVar(Free(FreeVar { unique_id:
/// UniqueId(0), pretty_name: Some("a") })))])])
/// ```
#[test]
fn corpus_2_proc() {
    mettail_runtime::clear_var_cache();
    // 1 — the term CONSTRUCTS.
    let term: Proc = Proc::Choose(std::sync::Arc::new(Proc::Choose(std::sync::Arc::new(Proc::PVar(mettail_runtime::OrdVar(mettail_runtime::Var::Free(mettail_runtime::get_or_create_var("a"))))), vec![Proc::PVar(mettail_runtime::OrdVar(mettail_runtime::Var::Free(mettail_runtime::get_or_create_var("a")))), Proc::PVar(mettail_runtime::OrdVar(mettail_runtime::Var::Free(mettail_runtime::get_or_create_var("a"))))])), vec![Proc::Choose(std::sync::Arc::new(Proc::PVar(mettail_runtime::OrdVar(mettail_runtime::Var::Free(mettail_runtime::get_or_create_var("a"))))), vec![Proc::PVar(mettail_runtime::OrdVar(mettail_runtime::Var::Free(mettail_runtime::get_or_create_var("a")))), Proc::PVar(mettail_runtime::OrdVar(mettail_runtime::Var::Free(mettail_runtime::get_or_create_var("a"))))]), Proc::Choose(std::sync::Arc::new(Proc::Choose(std::sync::Arc::new(Proc::PZero), vec![Proc::PZero])), vec![Proc::Choose(std::sync::Arc::new(Proc::PVar(mettail_runtime::OrdVar(mettail_runtime::Var::Free(mettail_runtime::get_or_create_var("a"))))), vec![Proc::PZero, Proc::PZero]), Proc::PVar(mettail_runtime::OrdVar(mettail_runtime::Var::Free(mettail_runtime::get_or_create_var("a"))))])]);

    // 2 — ANTI-VACUITY. The reconstructed term's normalised Debug must equal the
    //     text the corpus recorded, character for character. This is what makes
    //     "passes because it built the wrong term" impossible. Only
    //     `UniqueId(n)` and the ORDER of hash-container entries are quotiented
    //     out, and both are properties of the PROCESS rather than of the term:
    //     `UniqueId` comes from a global counter (and `FreeVar` equality is by
    //     unique_id alone, with the name fixing the identity through the var
    //     cache), and a `HashBag` is a multiset whose `PartialEq` ignores order.
    let recorded = "Choose(Choose(PVar(OrdVar(Free(FreeVar { unique_id: UniqueId(_), pretty_name: Some(\"a\") }))), [PVar(OrdVar(Free(FreeVar { unique_id: UniqueId(_), pretty_name: Some(\"a\") }))), PVar(OrdVar(Free(FreeVar { unique_id: UniqueId(_), pretty_name: Some(\"a\") })))]), [Choose(PVar(OrdVar(Free(FreeVar { unique_id: UniqueId(_), pretty_name: Some(\"a\") }))), [PVar(OrdVar(Free(FreeVar { unique_id: UniqueId(_), pretty_name: Some(\"a\") }))), PVar(OrdVar(Free(FreeVar { unique_id: UniqueId(_), pretty_name: Some(\"a\") })))]), Choose(Choose(PZero, [PZero]), [Choose(PVar(OrdVar(Free(FreeVar { unique_id: UniqueId(_), pretty_name: Some(\"a\") }))), [PZero, PZero]), PVar(OrdVar(Free(FreeVar { unique_id: UniqueId(_), pretty_name: Some(\"a\") })))])])";
    assert_eq!(
        canonicalize_debug(&format!("{:?}", term)),
        recorded,
        "the reconstructed term is not the recorded counterexample"
    );

    // 3 — the properties the corpus's generated suite checks for this category.
    let _ = format!("{:?}", term);            // <cat>_debug_does_not_panic
    let _ = format!("{}", term);              // <cat>_display_does_not_panic
    assert_eq!(term.clone(), term);           // <cat>_clone_eq
}
