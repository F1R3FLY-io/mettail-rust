//! **Promoted counterexamples for `ambient`** — every seed its proptest corpus records,
//! as a named regression test.
//!
//! # Where these came from, and why they are here
//!
//! `languages/tests/gen_ambient_prop.proptest-regressions` holds 4 seed(s) for inputs
//! that ONCE FALSIFIED a property of this grammar, each with the shrunk counterexample
//! recorded beside it. proptest replays those seeds — but only while the corpus stays where
//! the language name puts it, and only as an anonymous seed nobody can name in a bug report.
//! A named `#[test]` per entry gives each counterexample an identity, a failure message and
//! a place in the ordinary test run.
//!
//! # How the term was recovered
//!
//! NOT by replaying the seed. proptest persists the seed of the case's FIRST generated
//! input and separately records the SHRUNK value's `Debug`, so replay reconstructs a
//! different, larger term (measured: `testkit/src/ctor.rs`). The `# shrinks to` text is the
//! only complete record, and `testkit`'s harvester reads it back through the constructor
//! schema the `rust_ctor` pass emits:
//!
//! ```text
//! cargo run -p testkit --bin harvest_proptest_corpus -- \
//!     target/generated/ambient/rust_ctor.rs \
//!     languages/tests/gen_ambient_prop.proptest-regressions
//! ```
//!
//! # The three assertions, and which one carries the weight
//!
//! 1. the term CONSTRUCTS;
//! 2. ★ its **normalised `Debug` equals the corpus-recorded text**, carried here as a
//!    literal. This is the anti-vacuity core: a test that merely constructed *some* term
//!    would pass while proving nothing, and this assertion makes that impossible. Only
//!    `UniqueId(n)` is normalised — it is drawn from a process-global counter and is not a
//!    property of the term (`FreeVar` equality is by `unique_id` alone, and the generated
//!    strategies mint every variable through the thread-local name cache, so the NAME fixes
//!    the identity);
//! 3. the properties the generated suite checks for this category.
//!
//! # RED proof
//!
//! Mutate one constructor in any test below — swap `PZero` for a sibling, perturb an
//! integer — and assertion 2 goes RED, while every other test in the file still passes. The
//! unmutated terms' `Debug` matches its recorded text exactly, which is the control.

#![allow(clippy::needless_borrow)]

use mettail_testkit::ctor::canonicalize_debug;
use mettail_languages::ambient::*;

/// Corpus entry 0 — seed `cc 9bfae72a801d1c8f01b47ab5aa3cf9a621f2e5ccead50b27dcbf448e23e16e81`.
///
/// Recorded counterexample, verbatim from the corpus:
/// ```text
/// term = PNew(Scope { pattern: Binder(FreeVar { unique_id: UniqueId(61), pretty_name:
/// Some("a6") }), body: PZero })
/// ```
#[test]
fn corpus_0_proc() {
    mettail_runtime::clear_var_cache();
    // 1 — the term CONSTRUCTS.
    let term: Proc = Proc::PNew(mettail_runtime::Scope::from_parts_unsafe(mettail_runtime::Binder(mettail_runtime::get_or_create_var("a6")), std::sync::Arc::new(Proc::PZero)));

    // 2 — ANTI-VACUITY. The reconstructed term's normalised Debug must equal the
    //     text the corpus recorded, character for character. This is what makes
    //     "passes because it built the wrong term" impossible. Only
    //     `UniqueId(n)` and the ORDER of hash-container entries are quotiented
    //     out, and both are properties of the PROCESS rather than of the term:
    //     `UniqueId` comes from a global counter (and `FreeVar` equality is by
    //     unique_id alone, with the name fixing the identity through the var
    //     cache), and a `HashBag` is a multiset whose `PartialEq` ignores order.
    let recorded = "PNew(Scope { pattern: Binder(FreeVar { unique_id: UniqueId(_), pretty_name: Some(\"a6\") }), body: PZero })";
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

/// Corpus entry 1 — seed `cc 38b3d53c001bc4816eb5b8a2ba37fd589c849885d2495dc3a1da9dc6adcd5f03`.
///
/// Recorded counterexample, verbatim from the corpus:
/// ```text
/// term = PPar(HashBag { counts: {PVar(OrdVar(Free(FreeVar { unique_id: UniqueId(38),
/// pretty_name: Some("a") }))): 3}, total_count: 3 })
/// ```
#[test]
fn corpus_1_proc() {
    mettail_runtime::clear_var_cache();
    // 1 — the term CONSTRUCTS.
    let term: Proc = Proc::PPar(mettail_runtime::HashBag::from_iter(vec![Proc::PVar(mettail_runtime::OrdVar(mettail_runtime::Var::Free(mettail_runtime::get_or_create_var("a")))), Proc::PVar(mettail_runtime::OrdVar(mettail_runtime::Var::Free(mettail_runtime::get_or_create_var("a")))), Proc::PVar(mettail_runtime::OrdVar(mettail_runtime::Var::Free(mettail_runtime::get_or_create_var("a"))))]));

    // 2 — ANTI-VACUITY. The reconstructed term's normalised Debug must equal the
    //     text the corpus recorded, character for character. This is what makes
    //     "passes because it built the wrong term" impossible. Only
    //     `UniqueId(n)` and the ORDER of hash-container entries are quotiented
    //     out, and both are properties of the PROCESS rather than of the term:
    //     `UniqueId` comes from a global counter (and `FreeVar` equality is by
    //     unique_id alone, with the name fixing the identity through the var
    //     cache), and a `HashBag` is a multiset whose `PartialEq` ignores order.
    let recorded = "PPar(HashBag { counts: {PVar(OrdVar(Free(FreeVar { unique_id: UniqueId(_), pretty_name: Some(\"a\") }))): 3}, total_count: 3 })";
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

/// Corpus entry 2 — seed `cc e650096cad602d9d0e020c15ea4b0b231596fbd08770e0bd4393c604e7a3832b`.
///
/// Recorded counterexample, verbatim from the corpus:
/// ```text
/// term = PIn(NVar(OrdVar(Free(FreeVar { unique_id: UniqueId(1), pretty_name: Some("a") }))),
/// PPar(HashBag { counts: {PAmb(NVar(OrdVar(Free(FreeVar { unique_id: UniqueId(1), pretty_name:
/// Some("a") }))), PZero): 1, PIn(NVar(OrdVar(Free(FreeVar { unique_id: UniqueId(1),
/// pretty_name: Some("a") }))), PVar(OrdVar(Free(FreeVar { unique_id: UniqueId(1), pretty_name:
/// Some("a") })))): 1}, total_count: 2 }))
/// ```
#[test]
fn corpus_2_proc() {
    mettail_runtime::clear_var_cache();
    // 1 — the term CONSTRUCTS.
    let term: Proc = Proc::PIn(std::sync::Arc::new(Name::NVar(mettail_runtime::OrdVar(mettail_runtime::Var::Free(mettail_runtime::get_or_create_var("a"))))), std::sync::Arc::new(Proc::PPar(mettail_runtime::HashBag::from_iter(vec![Proc::PAmb(std::sync::Arc::new(Name::NVar(mettail_runtime::OrdVar(mettail_runtime::Var::Free(mettail_runtime::get_or_create_var("a"))))), std::sync::Arc::new(Proc::PZero)), Proc::PIn(std::sync::Arc::new(Name::NVar(mettail_runtime::OrdVar(mettail_runtime::Var::Free(mettail_runtime::get_or_create_var("a"))))), std::sync::Arc::new(Proc::PVar(mettail_runtime::OrdVar(mettail_runtime::Var::Free(mettail_runtime::get_or_create_var("a"))))))]))));

    // 2 — ANTI-VACUITY. The reconstructed term's normalised Debug must equal the
    //     text the corpus recorded, character for character. This is what makes
    //     "passes because it built the wrong term" impossible. Only
    //     `UniqueId(n)` and the ORDER of hash-container entries are quotiented
    //     out, and both are properties of the PROCESS rather than of the term:
    //     `UniqueId` comes from a global counter (and `FreeVar` equality is by
    //     unique_id alone, with the name fixing the identity through the var
    //     cache), and a `HashBag` is a multiset whose `PartialEq` ignores order.
    let recorded = "PIn(NVar(OrdVar(Free(FreeVar { unique_id: UniqueId(_), pretty_name: Some(\"a\") }))), PPar(HashBag { counts: {PAmb(NVar(OrdVar(Free(FreeVar { unique_id: UniqueId(_), pretty_name: Some(\"a\") }))), PZero): 1, PIn(NVar(OrdVar(Free(FreeVar { unique_id: UniqueId(_), pretty_name: Some(\"a\") }))), PVar(OrdVar(Free(FreeVar { unique_id: UniqueId(_), pretty_name: Some(\"a\") })))): 1}, total_count: 2 }))";
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

/// Corpus entry 3 — seed `cc c4628a0ef770882e9eb63675c8e7d8542e2d71c9bcc24b4c537b4e163f313bc7`.
///
/// Recorded counterexample, verbatim from the corpus:
/// ```text
/// term = PPar(HashBag { counts: {PPar(HashBag { counts: {PPar(HashBag { counts:
/// {PVar(OrdVar(Free(FreeVar { unique_id: UniqueId(0), pretty_name: Some("a") }))): 3},
/// total_count: 3 }): 3}, total_count: 3 }): 3}, total_count: 3 })
/// ```
#[test]
fn corpus_3_proc() {
    mettail_runtime::clear_var_cache();
    // 1 — the term CONSTRUCTS.
    let term: Proc = Proc::PPar(mettail_runtime::HashBag::from_iter(vec![Proc::PPar(mettail_runtime::HashBag::from_iter(vec![Proc::PPar(mettail_runtime::HashBag::from_iter(vec![Proc::PVar(mettail_runtime::OrdVar(mettail_runtime::Var::Free(mettail_runtime::get_or_create_var("a")))), Proc::PVar(mettail_runtime::OrdVar(mettail_runtime::Var::Free(mettail_runtime::get_or_create_var("a")))), Proc::PVar(mettail_runtime::OrdVar(mettail_runtime::Var::Free(mettail_runtime::get_or_create_var("a"))))])), Proc::PPar(mettail_runtime::HashBag::from_iter(vec![Proc::PVar(mettail_runtime::OrdVar(mettail_runtime::Var::Free(mettail_runtime::get_or_create_var("a")))), Proc::PVar(mettail_runtime::OrdVar(mettail_runtime::Var::Free(mettail_runtime::get_or_create_var("a")))), Proc::PVar(mettail_runtime::OrdVar(mettail_runtime::Var::Free(mettail_runtime::get_or_create_var("a"))))])), Proc::PPar(mettail_runtime::HashBag::from_iter(vec![Proc::PVar(mettail_runtime::OrdVar(mettail_runtime::Var::Free(mettail_runtime::get_or_create_var("a")))), Proc::PVar(mettail_runtime::OrdVar(mettail_runtime::Var::Free(mettail_runtime::get_or_create_var("a")))), Proc::PVar(mettail_runtime::OrdVar(mettail_runtime::Var::Free(mettail_runtime::get_or_create_var("a"))))]))])), Proc::PPar(mettail_runtime::HashBag::from_iter(vec![Proc::PPar(mettail_runtime::HashBag::from_iter(vec![Proc::PVar(mettail_runtime::OrdVar(mettail_runtime::Var::Free(mettail_runtime::get_or_create_var("a")))), Proc::PVar(mettail_runtime::OrdVar(mettail_runtime::Var::Free(mettail_runtime::get_or_create_var("a")))), Proc::PVar(mettail_runtime::OrdVar(mettail_runtime::Var::Free(mettail_runtime::get_or_create_var("a"))))])), Proc::PPar(mettail_runtime::HashBag::from_iter(vec![Proc::PVar(mettail_runtime::OrdVar(mettail_runtime::Var::Free(mettail_runtime::get_or_create_var("a")))), Proc::PVar(mettail_runtime::OrdVar(mettail_runtime::Var::Free(mettail_runtime::get_or_create_var("a")))), Proc::PVar(mettail_runtime::OrdVar(mettail_runtime::Var::Free(mettail_runtime::get_or_create_var("a"))))])), Proc::PPar(mettail_runtime::HashBag::from_iter(vec![Proc::PVar(mettail_runtime::OrdVar(mettail_runtime::Var::Free(mettail_runtime::get_or_create_var("a")))), Proc::PVar(mettail_runtime::OrdVar(mettail_runtime::Var::Free(mettail_runtime::get_or_create_var("a")))), Proc::PVar(mettail_runtime::OrdVar(mettail_runtime::Var::Free(mettail_runtime::get_or_create_var("a"))))]))])), Proc::PPar(mettail_runtime::HashBag::from_iter(vec![Proc::PPar(mettail_runtime::HashBag::from_iter(vec![Proc::PVar(mettail_runtime::OrdVar(mettail_runtime::Var::Free(mettail_runtime::get_or_create_var("a")))), Proc::PVar(mettail_runtime::OrdVar(mettail_runtime::Var::Free(mettail_runtime::get_or_create_var("a")))), Proc::PVar(mettail_runtime::OrdVar(mettail_runtime::Var::Free(mettail_runtime::get_or_create_var("a"))))])), Proc::PPar(mettail_runtime::HashBag::from_iter(vec![Proc::PVar(mettail_runtime::OrdVar(mettail_runtime::Var::Free(mettail_runtime::get_or_create_var("a")))), Proc::PVar(mettail_runtime::OrdVar(mettail_runtime::Var::Free(mettail_runtime::get_or_create_var("a")))), Proc::PVar(mettail_runtime::OrdVar(mettail_runtime::Var::Free(mettail_runtime::get_or_create_var("a"))))])), Proc::PPar(mettail_runtime::HashBag::from_iter(vec![Proc::PVar(mettail_runtime::OrdVar(mettail_runtime::Var::Free(mettail_runtime::get_or_create_var("a")))), Proc::PVar(mettail_runtime::OrdVar(mettail_runtime::Var::Free(mettail_runtime::get_or_create_var("a")))), Proc::PVar(mettail_runtime::OrdVar(mettail_runtime::Var::Free(mettail_runtime::get_or_create_var("a"))))]))]))]));

    // 2 — ANTI-VACUITY. The reconstructed term's normalised Debug must equal the
    //     text the corpus recorded, character for character. This is what makes
    //     "passes because it built the wrong term" impossible. Only
    //     `UniqueId(n)` and the ORDER of hash-container entries are quotiented
    //     out, and both are properties of the PROCESS rather than of the term:
    //     `UniqueId` comes from a global counter (and `FreeVar` equality is by
    //     unique_id alone, with the name fixing the identity through the var
    //     cache), and a `HashBag` is a multiset whose `PartialEq` ignores order.
    let recorded = "PPar(HashBag { counts: {PPar(HashBag { counts: {PPar(HashBag { counts: {PVar(OrdVar(Free(FreeVar { unique_id: UniqueId(_), pretty_name: Some(\"a\") }))): 3}, total_count: 3 }): 3}, total_count: 3 }): 3}, total_count: 3 })";
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
