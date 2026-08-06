//! **Promoted counterexamples for `class2hashmapsmoke`** — every seed its proptest corpus records,
//! as a named regression test.
//!
//! # Where these came from, and why they are here
//!
//! `languages/tests/gen_class2hashmapsmoke_prop.proptest-regressions` holds 1 seed(s) for inputs
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
//!     target/generated/class2hashmapsmoke/rust_ctor.rs \
//!     languages/tests/gen_class2hashmapsmoke_prop.proptest-regressions
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
// Task #11: `class2hashmapsmoke`'s grammar is a test FIXTURE, not a production language — its
// definition lives in `languages/tests/definitions/class2hashmapsmoke.rs` rather than in the `languages`
// library, so it is `#[path]`-included here. This binary is a CONSUMER: it deliberately does
// NOT invoke the `class2hashmapsmoke_generated_tests!` wrapper, because the definition's designated host is its own smoke-test binary and is the sole
// invoker, so the generated suite stays single-instanced across the workspace.
#[path = "definitions/class2hashmapsmoke.rs"]
mod class2hashmapsmoke;
use crate::class2hashmapsmoke::*;

/// Corpus entry 0 — seed `cc e23be3330d1108d91361e6b614df26ebf22b0dbc06e958e70d27c78b7e714ee6`.
///
/// Recorded counterexample, verbatim from the corpus:
/// ```text
/// term = ChooseMap(PZero, HashMapLit({PVar(OrdVar(Free(FreeVar { unique_id: UniqueId(0),
/// pretty_name: Some("a") }))): ChooseMap(ChooseMap(PVar(OrdVar(Free(FreeVar { unique_id:
/// UniqueId(0), pretty_name: Some("a") }))), HashMapLit({PVar(OrdVar(Free(FreeVar { unique_id:
/// UniqueId(0), pretty_name: Some("a") }))): PZero, PZero: PVar(OrdVar(Free(FreeVar {
/// unique_id: UniqueId(0), pretty_name: Some("a") })))})), HashMapLit({PZero:
/// ChooseMap(PVar(OrdVar(Free(FreeVar { unique_id: UniqueId(0), pretty_name: Some("a") }))),
/// HashMapLit({PZero: PVar(OrdVar(Free(FreeVar { unique_id: UniqueId(0), pretty_name: Some("a")
/// }))), PVar(OrdVar(Free(FreeVar { unique_id: UniqueId(0), pretty_name: Some("a") }))):
/// PZero}))}))}))
/// ```
#[test]
fn corpus_0_proc() {
    mettail_runtime::clear_var_cache();
    // 1 — the term CONSTRUCTS.
    let term: Proc = Proc::ChooseMap(
        std::sync::Arc::new(Proc::PZero),
        mettail_runtime::HashMapLit::from_iter(vec![(
            Proc::PVar(mettail_runtime::OrdVar(mettail_runtime::Var::Free(
                mettail_runtime::get_or_create_var("a"),
            ))),
            Proc::ChooseMap(
                std::sync::Arc::new(Proc::ChooseMap(
                    std::sync::Arc::new(Proc::PVar(mettail_runtime::OrdVar(
                        mettail_runtime::Var::Free(mettail_runtime::get_or_create_var("a")),
                    ))),
                    mettail_runtime::HashMapLit::from_iter(vec![
                        (
                            Proc::PVar(mettail_runtime::OrdVar(mettail_runtime::Var::Free(
                                mettail_runtime::get_or_create_var("a"),
                            ))),
                            Proc::PZero,
                        ),
                        (
                            Proc::PZero,
                            Proc::PVar(mettail_runtime::OrdVar(mettail_runtime::Var::Free(
                                mettail_runtime::get_or_create_var("a"),
                            ))),
                        ),
                    ]),
                )),
                mettail_runtime::HashMapLit::from_iter(vec![(
                    Proc::PZero,
                    Proc::ChooseMap(
                        std::sync::Arc::new(Proc::PVar(mettail_runtime::OrdVar(
                            mettail_runtime::Var::Free(mettail_runtime::get_or_create_var("a")),
                        ))),
                        mettail_runtime::HashMapLit::from_iter(vec![
                            (
                                Proc::PZero,
                                Proc::PVar(mettail_runtime::OrdVar(mettail_runtime::Var::Free(
                                    mettail_runtime::get_or_create_var("a"),
                                ))),
                            ),
                            (
                                Proc::PVar(mettail_runtime::OrdVar(mettail_runtime::Var::Free(
                                    mettail_runtime::get_or_create_var("a"),
                                ))),
                                Proc::PZero,
                            ),
                        ]),
                    ),
                )]),
            ),
        )]),
    );

    // 2 — ANTI-VACUITY. The reconstructed term's normalised Debug must equal the
    //     text the corpus recorded, character for character. This is what makes
    //     "passes because it built the wrong term" impossible. Only
    //     `UniqueId(n)` and the ORDER of hash-container entries are quotiented
    //     out, and both are properties of the PROCESS rather than of the term:
    //     `UniqueId` comes from a global counter (and `FreeVar` equality is by
    //     unique_id alone, with the name fixing the identity through the var
    //     cache), and a `HashBag` is a multiset whose `PartialEq` ignores order.
    let recorded = "ChooseMap(PZero, HashMapLit({PVar(OrdVar(Free(FreeVar { unique_id: UniqueId(_), pretty_name: Some(\"a\") }))): ChooseMap(ChooseMap(PVar(OrdVar(Free(FreeVar { unique_id: UniqueId(_), pretty_name: Some(\"a\") }))), HashMapLit({PVar(OrdVar(Free(FreeVar { unique_id: UniqueId(_), pretty_name: Some(\"a\") }))): PZero, PZero: PVar(OrdVar(Free(FreeVar { unique_id: UniqueId(_), pretty_name: Some(\"a\") })))})), HashMapLit({PZero: ChooseMap(PVar(OrdVar(Free(FreeVar { unique_id: UniqueId(_), pretty_name: Some(\"a\") }))), HashMapLit({PVar(OrdVar(Free(FreeVar { unique_id: UniqueId(_), pretty_name: Some(\"a\") }))): PZero, PZero: PVar(OrdVar(Free(FreeVar { unique_id: UniqueId(_), pretty_name: Some(\"a\") })))}))}))}))";
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
