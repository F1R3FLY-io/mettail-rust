//! **Promoted counterexamples for `guardedrho`** — every seed its proptest corpus records,
//! as a named regression test.
//!
//! # Where these came from, and why they are here
//!
//! `languages/tests/gen_guardedrho_prop.proptest-regressions` holds 6 seed(s) for inputs
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
//!     target/generated/guardedrho/rust_ctor.rs \
//!     languages/tests/gen_guardedrho_prop.proptest-regressions
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
// Task #11: `guardedrho`'s grammar is a test FIXTURE, not a production language — its
// definition lives in `languages/tests/definitions/guarded_rho.rs` rather than in the `languages`
// library, so it is `#[path]`-included here. This binary is a CONSUMER: it deliberately does
// NOT invoke the `guardedrho_generated_tests!` wrapper, because the definition's DESIGNATED HOST is `languages/tests/guarded_rho_tests.rs` and is the sole
// invoker, so the generated suite stays single-instanced across the workspace.
#[path = "definitions/guarded_rho.rs"]
mod guardedrho;
use crate::guardedrho::*;

/// Corpus entry 0 — seed `cc b99239f2be9615d0e06bb121d41addb3d5839aadca0bc4fbdd01035c9177969c`.
///
/// Recorded counterexample, verbatim from the corpus:
/// ```text
/// term = PPar(HashBag { counts: {PVar(OrdVar(Free(FreeVar { unique_id: UniqueId(62),
/// pretty_name: Some("a") }))): 2}, total_count: 2 })
/// ```
#[test]
fn corpus_0_proc() {
    mettail_runtime::clear_var_cache();
    // 1 — the term CONSTRUCTS.
    let term: Proc = Proc::PPar(mettail_runtime::HashBag::from_iter(vec![Proc::PVar(mettail_runtime::OrdVar(mettail_runtime::Var::Free(mettail_runtime::get_or_create_var("a")))), Proc::PVar(mettail_runtime::OrdVar(mettail_runtime::Var::Free(mettail_runtime::get_or_create_var("a"))))]));

    // 2 — ANTI-VACUITY. The reconstructed term's normalised Debug must equal the
    //     text the corpus recorded, character for character. This is what makes
    //     "passes because it built the wrong term" impossible. Only
    //     `UniqueId(n)` and the ORDER of hash-container entries are quotiented
    //     out, and both are properties of the PROCESS rather than of the term:
    //     `UniqueId` comes from a global counter (and `FreeVar` equality is by
    //     unique_id alone, with the name fixing the identity through the var
    //     cache), and a `HashBag` is a multiset whose `PartialEq` ignores order.
    let recorded = "PPar(HashBag { counts: {PVar(OrdVar(Free(FreeVar { unique_id: UniqueId(_), pretty_name: Some(\"a\") }))): 2}, total_count: 2 })";
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

/// Corpus entry 1 — seed `cc e0fadd71f9ee4b4df177076c69d995576e88f246776830995717437431e84109`.
///
/// Recorded counterexample, verbatim from the corpus:
/// ```text
/// term = NQuote(PVar(OrdVar(Free(FreeVar { unique_id: UniqueId(32), pretty_name: Some("a")
/// }))))
/// ```
#[test]
fn corpus_1_name() {
    mettail_runtime::clear_var_cache();
    // 1 — the term CONSTRUCTS.
    let term: Name = Name::NQuote(std::sync::Arc::new(Proc::PVar(mettail_runtime::OrdVar(mettail_runtime::Var::Free(mettail_runtime::get_or_create_var("a"))))));

    // 2 — ANTI-VACUITY. The reconstructed term's normalised Debug must equal the
    //     text the corpus recorded, character for character. This is what makes
    //     "passes because it built the wrong term" impossible. Only
    //     `UniqueId(n)` and the ORDER of hash-container entries are quotiented
    //     out, and both are properties of the PROCESS rather than of the term:
    //     `UniqueId` comes from a global counter (and `FreeVar` equality is by
    //     unique_id alone, with the name fixing the identity through the var
    //     cache), and a `HashBag` is a multiset whose `PartialEq` ignores order.
    let recorded = "NQuote(PVar(OrdVar(Free(FreeVar { unique_id: UniqueId(_), pretty_name: Some(\"a\") }))))";
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

/// Corpus entry 2 — seed `cc 54597bb61dd57800c1bbee58aecce18d6415534082d11bebcb603c3a3330cc59`.
///
/// Recorded counterexample, verbatim from the corpus:
/// ```text
/// term = NQuote(POutput(NVar(OrdVar(Free(FreeVar { unique_id: UniqueId(2), pretty_name:
/// Some("a") }))), POutput(NVar(OrdVar(Free(FreeVar { unique_id: UniqueId(2), pretty_name:
/// Some("a") }))), PVar(OrdVar(Free(FreeVar { unique_id: UniqueId(2), pretty_name: Some("a")
/// }))))))
/// ```
#[test]
fn corpus_2_name() {
    mettail_runtime::clear_var_cache();
    // 1 — the term CONSTRUCTS.
    let term: Name = Name::NQuote(std::sync::Arc::new(Proc::POutput(std::sync::Arc::new(Name::NVar(mettail_runtime::OrdVar(mettail_runtime::Var::Free(mettail_runtime::get_or_create_var("a"))))), std::sync::Arc::new(Proc::POutput(std::sync::Arc::new(Name::NVar(mettail_runtime::OrdVar(mettail_runtime::Var::Free(mettail_runtime::get_or_create_var("a"))))), std::sync::Arc::new(Proc::PVar(mettail_runtime::OrdVar(mettail_runtime::Var::Free(mettail_runtime::get_or_create_var("a"))))))))));

    // 2 — ANTI-VACUITY. The reconstructed term's normalised Debug must equal the
    //     text the corpus recorded, character for character. This is what makes
    //     "passes because it built the wrong term" impossible. Only
    //     `UniqueId(n)` and the ORDER of hash-container entries are quotiented
    //     out, and both are properties of the PROCESS rather than of the term:
    //     `UniqueId` comes from a global counter (and `FreeVar` equality is by
    //     unique_id alone, with the name fixing the identity through the var
    //     cache), and a `HashBag` is a multiset whose `PartialEq` ignores order.
    let recorded = "NQuote(POutput(NVar(OrdVar(Free(FreeVar { unique_id: UniqueId(_), pretty_name: Some(\"a\") }))), POutput(NVar(OrdVar(Free(FreeVar { unique_id: UniqueId(_), pretty_name: Some(\"a\") }))), PVar(OrdVar(Free(FreeVar { unique_id: UniqueId(_), pretty_name: Some(\"a\") }))))))";
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

/// Corpus entry 3 — seed `cc c5575211fd5a309bd511454a1dd6f7a205159827662dc6834f5b9147e212752b`.
///
/// Recorded counterexample, verbatim from the corpus:
/// ```text
/// term = PPar(HashBag { counts: {PPar(HashBag { counts: {PPar(HashBag { counts:
/// {PVar(OrdVar(Free(FreeVar { unique_id: UniqueId(0), pretty_name: Some("a") }))): 1},
/// total_count: 1 }): 1}, total_count: 1 }): 1}, total_count: 1 })
/// ```
#[test]
fn corpus_3_proc() {
    mettail_runtime::clear_var_cache();
    // 1 — the term CONSTRUCTS.
    let term: Proc = Proc::PPar(mettail_runtime::HashBag::from_iter(vec![Proc::PPar(mettail_runtime::HashBag::from_iter(vec![Proc::PPar(mettail_runtime::HashBag::from_iter(vec![Proc::PVar(mettail_runtime::OrdVar(mettail_runtime::Var::Free(mettail_runtime::get_or_create_var("a"))))]))]))]));

    // 2 — ANTI-VACUITY. The reconstructed term's normalised Debug must equal the
    //     text the corpus recorded, character for character. This is what makes
    //     "passes because it built the wrong term" impossible. Only
    //     `UniqueId(n)` and the ORDER of hash-container entries are quotiented
    //     out, and both are properties of the PROCESS rather than of the term:
    //     `UniqueId` comes from a global counter (and `FreeVar` equality is by
    //     unique_id alone, with the name fixing the identity through the var
    //     cache), and a `HashBag` is a multiset whose `PartialEq` ignores order.
    let recorded = "PPar(HashBag { counts: {PPar(HashBag { counts: {PPar(HashBag { counts: {PVar(OrdVar(Free(FreeVar { unique_id: UniqueId(_), pretty_name: Some(\"a\") }))): 1}, total_count: 1 }): 1}, total_count: 1 }): 1}, total_count: 1 })";
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

/// Corpus entry 4 — seed `cc 487b65229ebb05629118f5fc365067eec3a7ca2cf6a4713942614dbf398eb828`.
///
/// Recorded counterexample, verbatim from the corpus:
/// ```text
/// term = POutput(NQuote(POutput(NVar(OrdVar(Free(FreeVar { unique_id: UniqueId(0),
/// pretty_name: Some("a") }))), PVar(OrdVar(Free(FreeVar { unique_id: UniqueId(0), pretty_name:
/// Some("a") }))))), POutput(NQuote(PNil), POutput(NVar(OrdVar(Free(FreeVar { unique_id:
/// UniqueId(0), pretty_name: Some("a") }))), PNil)))
/// ```
#[test]
fn corpus_4_proc() {
    mettail_runtime::clear_var_cache();
    // 1 — the term CONSTRUCTS.
    let term: Proc = Proc::POutput(std::sync::Arc::new(Name::NQuote(std::sync::Arc::new(Proc::POutput(std::sync::Arc::new(Name::NVar(mettail_runtime::OrdVar(mettail_runtime::Var::Free(mettail_runtime::get_or_create_var("a"))))), std::sync::Arc::new(Proc::PVar(mettail_runtime::OrdVar(mettail_runtime::Var::Free(mettail_runtime::get_or_create_var("a"))))))))), std::sync::Arc::new(Proc::POutput(std::sync::Arc::new(Name::NQuote(std::sync::Arc::new(Proc::PNil))), std::sync::Arc::new(Proc::POutput(std::sync::Arc::new(Name::NVar(mettail_runtime::OrdVar(mettail_runtime::Var::Free(mettail_runtime::get_or_create_var("a"))))), std::sync::Arc::new(Proc::PNil))))));

    // 2 — ANTI-VACUITY. The reconstructed term's normalised Debug must equal the
    //     text the corpus recorded, character for character. This is what makes
    //     "passes because it built the wrong term" impossible. Only
    //     `UniqueId(n)` and the ORDER of hash-container entries are quotiented
    //     out, and both are properties of the PROCESS rather than of the term:
    //     `UniqueId` comes from a global counter (and `FreeVar` equality is by
    //     unique_id alone, with the name fixing the identity through the var
    //     cache), and a `HashBag` is a multiset whose `PartialEq` ignores order.
    let recorded = "POutput(NQuote(POutput(NVar(OrdVar(Free(FreeVar { unique_id: UniqueId(_), pretty_name: Some(\"a\") }))), PVar(OrdVar(Free(FreeVar { unique_id: UniqueId(_), pretty_name: Some(\"a\") }))))), POutput(NQuote(PNil), POutput(NVar(OrdVar(Free(FreeVar { unique_id: UniqueId(_), pretty_name: Some(\"a\") }))), PNil)))";
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

/// Corpus entry 5 — seed `cc f7157b253f6c18941cf6b5815d295497f28ff57330933a4cd58c2185cd97ccc7`.
///
/// Recorded counterexample, verbatim from the corpus:
/// ```text
/// term = PPar(HashBag { counts: {PPar(HashBag { counts: {PPar(HashBag { counts: {PNil: 1},
/// total_count: 1 }): 1, PPar(HashBag { counts: {}, total_count: 0 }): 1}, total_count: 2 }):
/// 1, POutput(NQuote(PVar(OrdVar(Free(FreeVar { unique_id: UniqueId(0), pretty_name: Some("a")
/// })))), PNil): 1}, total_count: 2 })
/// ```
#[test]
fn corpus_5_proc() {
    mettail_runtime::clear_var_cache();
    // 1 — the term CONSTRUCTS.
    let term: Proc = Proc::PPar(mettail_runtime::HashBag::from_iter(vec![Proc::PPar(mettail_runtime::HashBag::from_iter(vec![Proc::PPar(mettail_runtime::HashBag::from_iter(vec![Proc::PNil])), Proc::PPar(mettail_runtime::HashBag::from_iter(vec![]))])), Proc::POutput(std::sync::Arc::new(Name::NQuote(std::sync::Arc::new(Proc::PVar(mettail_runtime::OrdVar(mettail_runtime::Var::Free(mettail_runtime::get_or_create_var("a"))))))), std::sync::Arc::new(Proc::PNil))]));

    // 2 — ANTI-VACUITY. The reconstructed term's normalised Debug must equal the
    //     text the corpus recorded, character for character. This is what makes
    //     "passes because it built the wrong term" impossible. Only
    //     `UniqueId(n)` and the ORDER of hash-container entries are quotiented
    //     out, and both are properties of the PROCESS rather than of the term:
    //     `UniqueId` comes from a global counter (and `FreeVar` equality is by
    //     unique_id alone, with the name fixing the identity through the var
    //     cache), and a `HashBag` is a multiset whose `PartialEq` ignores order.
    let recorded = "PPar(HashBag { counts: {POutput(NQuote(PVar(OrdVar(Free(FreeVar { unique_id: UniqueId(_), pretty_name: Some(\"a\") })))), PNil): 1, PPar(HashBag { counts: {PPar(HashBag { counts: {PNil: 1}, total_count: 1 }): 1, PPar(HashBag { counts: {}, total_count: 0 }): 1}, total_count: 2 }): 1}, total_count: 2 })";
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
