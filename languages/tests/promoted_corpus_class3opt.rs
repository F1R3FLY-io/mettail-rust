//! **Promoted counterexamples for `class3opt`** — every seed its proptest corpus records,
//! as a named regression test.
//!
//! # Where these came from, and why they are here
//!
//! `languages/tests/gen_class3opt_prop.proptest-regressions` holds 4 seed(s) for inputs
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
//!     target/generated/class3opt/rust_ctor.rs \
//!     languages/tests/gen_class3opt_prop.proptest-regressions
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
// Task #11: `class3opt`'s grammar is a test FIXTURE, not a production language — its
// definition lives in `languages/tests/definitions/class3opt.rs` rather than in the `languages`
// library, so it is `#[path]`-included here. This binary is a CONSUMER: it deliberately does
// NOT invoke the `class3opt_generated_tests!` wrapper, because the definition's designated host is its own smoke-test binary and is the sole
// invoker, so the generated suite stays single-instanced across the workspace.
#[path = "definitions/class3opt.rs"]
mod class3opt;
use crate::class3opt::*;

/// Corpus entry 0 — seed `cc c4f190ae0c9d6f064d561015e253f834b3a0c823a90492d803098ba102d9ca7c`.
///
/// Recorded counterexample, verbatim from the corpus:
/// ```text
/// term = PInputsOptTagged([], Some([PZero]), Scope { pattern: [Binder(FreeVar { unique_id:
/// UniqueId(11), pretty_name: Some("a0") }), Binder(FreeVar { unique_id: UniqueId(12),
/// pretty_name: Some("a1") })], body: PInputsOptTagged([], Some([PZero]), Scope { pattern:
/// [Binder(FreeVar { unique_id: UniqueId(11), pretty_name: Some("a0") }), Binder(FreeVar {
/// unique_id: UniqueId(12), pretty_name: Some("a1") })], body: PInputsOptTagged([],
/// Some([PZero]), Scope { pattern: [Binder(FreeVar { unique_id: UniqueId(11), pretty_name:
/// Some("a0") }), Binder(FreeVar { unique_id: UniqueId(12), pretty_name: Some("a1") })], body:
/// PVar(OrdVar(Free(FreeVar { unique_id: UniqueId(10), pretty_name: Some("a") }))) }) }) })
/// ```
#[test]
fn corpus_0_proc() {
    mettail_runtime::clear_var_cache();
    // 1 — the term CONSTRUCTS.
    let term: Proc = Proc::PInputsOptTagged(
        vec![],
        Some(vec![Proc::PZero]),
        mettail_runtime::Scope::from_parts_unsafe(
            vec![
                mettail_runtime::Binder(mettail_runtime::get_or_create_var("a0")),
                mettail_runtime::Binder(mettail_runtime::get_or_create_var("a1")),
            ],
            std::sync::Arc::new(Proc::PInputsOptTagged(
                vec![],
                Some(vec![Proc::PZero]),
                mettail_runtime::Scope::from_parts_unsafe(
                    vec![
                        mettail_runtime::Binder(mettail_runtime::get_or_create_var("a0")),
                        mettail_runtime::Binder(mettail_runtime::get_or_create_var("a1")),
                    ],
                    std::sync::Arc::new(Proc::PInputsOptTagged(
                        vec![],
                        Some(vec![Proc::PZero]),
                        mettail_runtime::Scope::from_parts_unsafe(
                            vec![
                                mettail_runtime::Binder(mettail_runtime::get_or_create_var("a0")),
                                mettail_runtime::Binder(mettail_runtime::get_or_create_var("a1")),
                            ],
                            std::sync::Arc::new(Proc::PVar(mettail_runtime::OrdVar(
                                mettail_runtime::Var::Free(mettail_runtime::get_or_create_var("a")),
                            ))),
                        ),
                    )),
                ),
            )),
        ),
    );

    // 2 — ANTI-VACUITY. The reconstructed term's normalised Debug must equal the
    //     text the corpus recorded, character for character. This is what makes
    //     "passes because it built the wrong term" impossible. Only
    //     `UniqueId(n)` and the ORDER of hash-container entries are quotiented
    //     out, and both are properties of the PROCESS rather than of the term:
    //     `UniqueId` comes from a global counter (and `FreeVar` equality is by
    //     unique_id alone, with the name fixing the identity through the var
    //     cache), and a `HashBag` is a multiset whose `PartialEq` ignores order.
    let recorded = "PInputsOptTagged([], Some([PZero]), Scope { pattern: [Binder(FreeVar { unique_id: UniqueId(_), pretty_name: Some(\"a0\") }), Binder(FreeVar { unique_id: UniqueId(_), pretty_name: Some(\"a1\") })], body: PInputsOptTagged([], Some([PZero]), Scope { pattern: [Binder(FreeVar { unique_id: UniqueId(_), pretty_name: Some(\"a0\") }), Binder(FreeVar { unique_id: UniqueId(_), pretty_name: Some(\"a1\") })], body: PInputsOptTagged([], Some([PZero]), Scope { pattern: [Binder(FreeVar { unique_id: UniqueId(_), pretty_name: Some(\"a0\") }), Binder(FreeVar { unique_id: UniqueId(_), pretty_name: Some(\"a1\") })], body: PVar(OrdVar(Free(FreeVar { unique_id: UniqueId(_), pretty_name: Some(\"a\") }))) }) }) })";
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

/// Corpus entry 1 — seed `cc 1fb2c8da61eae4b455ff931f4a437a61d650976043035c78f87d99c7bf845118`.
///
/// Recorded counterexample, verbatim from the corpus:
/// ```text
/// term = NQuote(PInputsOptTagged([], Some([PInputsOptTagged([], Some([PVar(OrdVar(Free(FreeVar
/// { unique_id: UniqueId(3), pretty_name: Some("a") }))), PVar(OrdVar(Free(FreeVar { unique_id:
/// UniqueId(3), pretty_name: Some("a") }))), PVar(OrdVar(Free(FreeVar { unique_id: UniqueId(3),
/// pretty_name: Some("a") })))]), Scope { pattern: [Binder(FreeVar { unique_id: UniqueId(61),
/// pretty_name: Some("a0") }), Binder(FreeVar { unique_id: UniqueId(131), pretty_name:
/// Some("a1") })], body: PVar(OrdVar(Free(FreeVar { unique_id: UniqueId(3), pretty_name:
/// Some("a") }))) }), PZero, PVar(OrdVar(Free(FreeVar { unique_id: UniqueId(3), pretty_name:
/// Some("a") })))]), Scope { pattern: [Binder(FreeVar { unique_id: UniqueId(61), pretty_name:
/// Some("a0") }), Binder(FreeVar { unique_id: UniqueId(131), pretty_name: Some("a1") }),
/// Binder(FreeVar { unique_id: UniqueId(132), pretty_name: Some("a2") })], body: PZero }))
/// ```
#[test]
fn corpus_1_name() {
    mettail_runtime::clear_var_cache();
    // 1 — the term CONSTRUCTS.
    let term: Name = Name::NQuote(std::sync::Arc::new(Proc::PInputsOptTagged(
        vec![],
        Some(vec![
            Proc::PInputsOptTagged(
                vec![],
                Some(vec![
                    Proc::PVar(mettail_runtime::OrdVar(mettail_runtime::Var::Free(
                        mettail_runtime::get_or_create_var("a"),
                    ))),
                    Proc::PVar(mettail_runtime::OrdVar(mettail_runtime::Var::Free(
                        mettail_runtime::get_or_create_var("a"),
                    ))),
                    Proc::PVar(mettail_runtime::OrdVar(mettail_runtime::Var::Free(
                        mettail_runtime::get_or_create_var("a"),
                    ))),
                ]),
                mettail_runtime::Scope::from_parts_unsafe(
                    vec![
                        mettail_runtime::Binder(mettail_runtime::get_or_create_var("a0")),
                        mettail_runtime::Binder(mettail_runtime::get_or_create_var("a1")),
                    ],
                    std::sync::Arc::new(Proc::PVar(mettail_runtime::OrdVar(
                        mettail_runtime::Var::Free(mettail_runtime::get_or_create_var("a")),
                    ))),
                ),
            ),
            Proc::PZero,
            Proc::PVar(mettail_runtime::OrdVar(mettail_runtime::Var::Free(
                mettail_runtime::get_or_create_var("a"),
            ))),
        ]),
        mettail_runtime::Scope::from_parts_unsafe(
            vec![
                mettail_runtime::Binder(mettail_runtime::get_or_create_var("a0")),
                mettail_runtime::Binder(mettail_runtime::get_or_create_var("a1")),
                mettail_runtime::Binder(mettail_runtime::get_or_create_var("a2")),
            ],
            std::sync::Arc::new(Proc::PZero),
        ),
    )));

    // 2 — ANTI-VACUITY. The reconstructed term's normalised Debug must equal the
    //     text the corpus recorded, character for character. This is what makes
    //     "passes because it built the wrong term" impossible. Only
    //     `UniqueId(n)` and the ORDER of hash-container entries are quotiented
    //     out, and both are properties of the PROCESS rather than of the term:
    //     `UniqueId` comes from a global counter (and `FreeVar` equality is by
    //     unique_id alone, with the name fixing the identity through the var
    //     cache), and a `HashBag` is a multiset whose `PartialEq` ignores order.
    let recorded = "NQuote(PInputsOptTagged([], Some([PInputsOptTagged([], Some([PVar(OrdVar(Free(FreeVar { unique_id: UniqueId(_), pretty_name: Some(\"a\") }))), PVar(OrdVar(Free(FreeVar { unique_id: UniqueId(_), pretty_name: Some(\"a\") }))), PVar(OrdVar(Free(FreeVar { unique_id: UniqueId(_), pretty_name: Some(\"a\") })))]), Scope { pattern: [Binder(FreeVar { unique_id: UniqueId(_), pretty_name: Some(\"a0\") }), Binder(FreeVar { unique_id: UniqueId(_), pretty_name: Some(\"a1\") })], body: PVar(OrdVar(Free(FreeVar { unique_id: UniqueId(_), pretty_name: Some(\"a\") }))) }), PZero, PVar(OrdVar(Free(FreeVar { unique_id: UniqueId(_), pretty_name: Some(\"a\") })))]), Scope { pattern: [Binder(FreeVar { unique_id: UniqueId(_), pretty_name: Some(\"a0\") }), Binder(FreeVar { unique_id: UniqueId(_), pretty_name: Some(\"a1\") }), Binder(FreeVar { unique_id: UniqueId(_), pretty_name: Some(\"a2\") })], body: PZero }))";
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

/// Corpus entry 2 — seed `cc c0c65c4ac8c6560576402d983817aeb68725db3ae5de4e29bb6858b8692060ba`.
///
/// Recorded counterexample, verbatim from the corpus:
/// ```text
/// term = NQuote(PInputsOptTagged([NQuote(PVar(OrdVar(Free(FreeVar { unique_id: UniqueId(1),
/// pretty_name: Some("a") })))), NQuote(PVar(OrdVar(Free(FreeVar { unique_id: UniqueId(1),
/// pretty_name: Some("a") }))))], Some([PInputsOptTagged([NVar(OrdVar(Free(FreeVar { unique_id:
/// UniqueId(1), pretty_name: Some("a") }))), NVar(OrdVar(Free(FreeVar { unique_id: UniqueId(1),
/// pretty_name: Some("a") })))], Some([PZero]), Scope { pattern: [Binder(FreeVar { unique_id:
/// UniqueId(0), pretty_name: Some("a0") }), Binder(FreeVar { unique_id: UniqueId(2),
/// pretty_name: Some("a1") }), Binder(FreeVar { unique_id: UniqueId(3), pretty_name: Some("a2")
/// })], body: PVar(OrdVar(Free(FreeVar { unique_id: UniqueId(1), pretty_name: Some("a") })))
/// })]), Scope { pattern: [Binder(FreeVar { unique_id: UniqueId(0), pretty_name: Some("a0") }),
/// Binder(FreeVar { unique_id: UniqueId(2), pretty_name: Some("a1") }), Binder(FreeVar {
/// unique_id: UniqueId(3), pretty_name: Some("a2") })], body:
/// PInputsOptTagged([NVar(OrdVar(Free(FreeVar { unique_id: UniqueId(1), pretty_name: Some("a")
/// }))), NVar(OrdVar(Free(FreeVar { unique_id: UniqueId(1), pretty_name: Some("a") })))], None,
/// Scope { pattern: [Binder(FreeVar { unique_id: UniqueId(0), pretty_name: Some("a0") }),
/// Binder(FreeVar { unique_id: UniqueId(2), pretty_name: Some("a1") }), Binder(FreeVar {
/// unique_id: UniqueId(3), pretty_name: Some("a2") })], body: PVar(OrdVar(Free(FreeVar {
/// unique_id: UniqueId(1), pretty_name: Some("a") }))) }) }))
/// ```
#[test]
fn corpus_2_name() {
    mettail_runtime::clear_var_cache();
    // 1 — the term CONSTRUCTS.
    let term: Name = Name::NQuote(std::sync::Arc::new(Proc::PInputsOptTagged(
        vec![
            Name::NQuote(std::sync::Arc::new(Proc::PVar(mettail_runtime::OrdVar(
                mettail_runtime::Var::Free(mettail_runtime::get_or_create_var("a")),
            )))),
            Name::NQuote(std::sync::Arc::new(Proc::PVar(mettail_runtime::OrdVar(
                mettail_runtime::Var::Free(mettail_runtime::get_or_create_var("a")),
            )))),
        ],
        Some(vec![Proc::PInputsOptTagged(
            vec![
                Name::NVar(mettail_runtime::OrdVar(mettail_runtime::Var::Free(
                    mettail_runtime::get_or_create_var("a"),
                ))),
                Name::NVar(mettail_runtime::OrdVar(mettail_runtime::Var::Free(
                    mettail_runtime::get_or_create_var("a"),
                ))),
            ],
            Some(vec![Proc::PZero]),
            mettail_runtime::Scope::from_parts_unsafe(
                vec![
                    mettail_runtime::Binder(mettail_runtime::get_or_create_var("a0")),
                    mettail_runtime::Binder(mettail_runtime::get_or_create_var("a1")),
                    mettail_runtime::Binder(mettail_runtime::get_or_create_var("a2")),
                ],
                std::sync::Arc::new(Proc::PVar(mettail_runtime::OrdVar(
                    mettail_runtime::Var::Free(mettail_runtime::get_or_create_var("a")),
                ))),
            ),
        )]),
        mettail_runtime::Scope::from_parts_unsafe(
            vec![
                mettail_runtime::Binder(mettail_runtime::get_or_create_var("a0")),
                mettail_runtime::Binder(mettail_runtime::get_or_create_var("a1")),
                mettail_runtime::Binder(mettail_runtime::get_or_create_var("a2")),
            ],
            std::sync::Arc::new(Proc::PInputsOptTagged(
                vec![
                    Name::NVar(mettail_runtime::OrdVar(mettail_runtime::Var::Free(
                        mettail_runtime::get_or_create_var("a"),
                    ))),
                    Name::NVar(mettail_runtime::OrdVar(mettail_runtime::Var::Free(
                        mettail_runtime::get_or_create_var("a"),
                    ))),
                ],
                None,
                mettail_runtime::Scope::from_parts_unsafe(
                    vec![
                        mettail_runtime::Binder(mettail_runtime::get_or_create_var("a0")),
                        mettail_runtime::Binder(mettail_runtime::get_or_create_var("a1")),
                        mettail_runtime::Binder(mettail_runtime::get_or_create_var("a2")),
                    ],
                    std::sync::Arc::new(Proc::PVar(mettail_runtime::OrdVar(
                        mettail_runtime::Var::Free(mettail_runtime::get_or_create_var("a")),
                    ))),
                ),
            )),
        ),
    )));

    // 2 — ANTI-VACUITY. The reconstructed term's normalised Debug must equal the
    //     text the corpus recorded, character for character. This is what makes
    //     "passes because it built the wrong term" impossible. Only
    //     `UniqueId(n)` and the ORDER of hash-container entries are quotiented
    //     out, and both are properties of the PROCESS rather than of the term:
    //     `UniqueId` comes from a global counter (and `FreeVar` equality is by
    //     unique_id alone, with the name fixing the identity through the var
    //     cache), and a `HashBag` is a multiset whose `PartialEq` ignores order.
    let recorded = "NQuote(PInputsOptTagged([NQuote(PVar(OrdVar(Free(FreeVar { unique_id: UniqueId(_), pretty_name: Some(\"a\") })))), NQuote(PVar(OrdVar(Free(FreeVar { unique_id: UniqueId(_), pretty_name: Some(\"a\") }))))], Some([PInputsOptTagged([NVar(OrdVar(Free(FreeVar { unique_id: UniqueId(_), pretty_name: Some(\"a\") }))), NVar(OrdVar(Free(FreeVar { unique_id: UniqueId(_), pretty_name: Some(\"a\") })))], Some([PZero]), Scope { pattern: [Binder(FreeVar { unique_id: UniqueId(_), pretty_name: Some(\"a0\") }), Binder(FreeVar { unique_id: UniqueId(_), pretty_name: Some(\"a1\") }), Binder(FreeVar { unique_id: UniqueId(_), pretty_name: Some(\"a2\") })], body: PVar(OrdVar(Free(FreeVar { unique_id: UniqueId(_), pretty_name: Some(\"a\") }))) })]), Scope { pattern: [Binder(FreeVar { unique_id: UniqueId(_), pretty_name: Some(\"a0\") }), Binder(FreeVar { unique_id: UniqueId(_), pretty_name: Some(\"a1\") }), Binder(FreeVar { unique_id: UniqueId(_), pretty_name: Some(\"a2\") })], body: PInputsOptTagged([NVar(OrdVar(Free(FreeVar { unique_id: UniqueId(_), pretty_name: Some(\"a\") }))), NVar(OrdVar(Free(FreeVar { unique_id: UniqueId(_), pretty_name: Some(\"a\") })))], None, Scope { pattern: [Binder(FreeVar { unique_id: UniqueId(_), pretty_name: Some(\"a0\") }), Binder(FreeVar { unique_id: UniqueId(_), pretty_name: Some(\"a1\") }), Binder(FreeVar { unique_id: UniqueId(_), pretty_name: Some(\"a2\") })], body: PVar(OrdVar(Free(FreeVar { unique_id: UniqueId(_), pretty_name: Some(\"a\") }))) }) }))";
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

/// Corpus entry 3 — seed `cc 24f23f2d0a2e5253cd144b04b97d3e7147f1c78f9e4b30af383094b400892211`.
///
/// Recorded counterexample, verbatim from the corpus:
/// ```text
/// term = PInputsOptTagged([NVar(OrdVar(Free(FreeVar { unique_id: UniqueId(0), pretty_name:
/// Some("a") }))), NVar(OrdVar(Free(FreeVar { unique_id: UniqueId(0), pretty_name: Some("a")
/// })))], Some([PZero, PInputsOptTagged([NVar(OrdVar(Free(FreeVar { unique_id: UniqueId(0),
/// pretty_name: Some("a") }))), NVar(OrdVar(Free(FreeVar { unique_id: UniqueId(0), pretty_name:
/// Some("a") })))], Some([PZero, PInputsOptTagged([NVar(OrdVar(Free(FreeVar { unique_id:
/// UniqueId(0), pretty_name: Some("a") }))), NVar(OrdVar(Free(FreeVar { unique_id: UniqueId(0),
/// pretty_name: Some("a") })))], None, Scope { pattern: [Binder(FreeVar { unique_id:
/// UniqueId(1), pretty_name: Some("a0") })], body: PVar(OrdVar(Free(FreeVar { unique_id:
/// UniqueId(0), pretty_name: Some("a") }))) })]), Scope { pattern: [Binder(FreeVar { unique_id:
/// UniqueId(1), pretty_name: Some("a0") })], body: PInputsOptTagged([NVar(OrdVar(Free(FreeVar {
/// unique_id: UniqueId(0), pretty_name: Some("a") }))), NVar(OrdVar(Free(FreeVar { unique_id:
/// UniqueId(0), pretty_name: Some("a") })))], None, Scope { pattern: [Binder(FreeVar {
/// unique_id: UniqueId(1), pretty_name: Some("a0") })], body: PVar(OrdVar(Free(FreeVar {
/// unique_id: UniqueId(0), pretty_name: Some("a") }))) }) })]), Scope { pattern:
/// [Binder(FreeVar { unique_id: UniqueId(1), pretty_name: Some("a0") })], body:
/// PInputsOptTagged([NVar(OrdVar(Free(FreeVar { unique_id: UniqueId(0), pretty_name: Some("a")
/// }))), NVar(OrdVar(Free(FreeVar { unique_id: UniqueId(0), pretty_name: Some("a") })))],
/// Some([PZero, PInputsOptTagged([NVar(OrdVar(Free(FreeVar { unique_id: UniqueId(0),
/// pretty_name: Some("a") }))), NVar(OrdVar(Free(FreeVar { unique_id: UniqueId(0), pretty_name:
/// Some("a") })))], None, Scope { pattern: [Binder(FreeVar { unique_id: UniqueId(1),
/// pretty_name: Some("a0") })], body: PVar(OrdVar(Free(FreeVar { unique_id: UniqueId(0),
/// pretty_name: Some("a") }))) })]), Scope { pattern: [Binder(FreeVar { unique_id: UniqueId(1),
/// pretty_name: Some("a0") })], body: PInputsOptTagged([NVar(OrdVar(Free(FreeVar { unique_id:
/// UniqueId(0), pretty_name: Some("a") }))), NVar(OrdVar(Free(FreeVar { unique_id: UniqueId(0),
/// pretty_name: Some("a") })))], None, Scope { pattern: [Binder(FreeVar { unique_id:
/// UniqueId(1), pretty_name: Some("a0") })], body: PVar(OrdVar(Free(FreeVar { unique_id:
/// UniqueId(0), pretty_name: Some("a") }))) }) }) })
/// ```
#[test]
fn corpus_3_proc() {
    mettail_runtime::clear_var_cache();
    // 1 — the term CONSTRUCTS.
    let term: Proc = Proc::PInputsOptTagged(
        vec![
            Name::NVar(mettail_runtime::OrdVar(mettail_runtime::Var::Free(
                mettail_runtime::get_or_create_var("a"),
            ))),
            Name::NVar(mettail_runtime::OrdVar(mettail_runtime::Var::Free(
                mettail_runtime::get_or_create_var("a"),
            ))),
        ],
        Some(vec![
            Proc::PZero,
            Proc::PInputsOptTagged(
                vec![
                    Name::NVar(mettail_runtime::OrdVar(mettail_runtime::Var::Free(
                        mettail_runtime::get_or_create_var("a"),
                    ))),
                    Name::NVar(mettail_runtime::OrdVar(mettail_runtime::Var::Free(
                        mettail_runtime::get_or_create_var("a"),
                    ))),
                ],
                Some(vec![
                    Proc::PZero,
                    Proc::PInputsOptTagged(
                        vec![
                            Name::NVar(mettail_runtime::OrdVar(mettail_runtime::Var::Free(
                                mettail_runtime::get_or_create_var("a"),
                            ))),
                            Name::NVar(mettail_runtime::OrdVar(mettail_runtime::Var::Free(
                                mettail_runtime::get_or_create_var("a"),
                            ))),
                        ],
                        None,
                        mettail_runtime::Scope::from_parts_unsafe(
                            vec![mettail_runtime::Binder(mettail_runtime::get_or_create_var("a0"))],
                            std::sync::Arc::new(Proc::PVar(mettail_runtime::OrdVar(
                                mettail_runtime::Var::Free(mettail_runtime::get_or_create_var("a")),
                            ))),
                        ),
                    ),
                ]),
                mettail_runtime::Scope::from_parts_unsafe(
                    vec![mettail_runtime::Binder(mettail_runtime::get_or_create_var("a0"))],
                    std::sync::Arc::new(Proc::PInputsOptTagged(
                        vec![
                            Name::NVar(mettail_runtime::OrdVar(mettail_runtime::Var::Free(
                                mettail_runtime::get_or_create_var("a"),
                            ))),
                            Name::NVar(mettail_runtime::OrdVar(mettail_runtime::Var::Free(
                                mettail_runtime::get_or_create_var("a"),
                            ))),
                        ],
                        None,
                        mettail_runtime::Scope::from_parts_unsafe(
                            vec![mettail_runtime::Binder(mettail_runtime::get_or_create_var("a0"))],
                            std::sync::Arc::new(Proc::PVar(mettail_runtime::OrdVar(
                                mettail_runtime::Var::Free(mettail_runtime::get_or_create_var("a")),
                            ))),
                        ),
                    )),
                ),
            ),
        ]),
        mettail_runtime::Scope::from_parts_unsafe(
            vec![mettail_runtime::Binder(mettail_runtime::get_or_create_var("a0"))],
            std::sync::Arc::new(Proc::PInputsOptTagged(
                vec![
                    Name::NVar(mettail_runtime::OrdVar(mettail_runtime::Var::Free(
                        mettail_runtime::get_or_create_var("a"),
                    ))),
                    Name::NVar(mettail_runtime::OrdVar(mettail_runtime::Var::Free(
                        mettail_runtime::get_or_create_var("a"),
                    ))),
                ],
                Some(vec![
                    Proc::PZero,
                    Proc::PInputsOptTagged(
                        vec![
                            Name::NVar(mettail_runtime::OrdVar(mettail_runtime::Var::Free(
                                mettail_runtime::get_or_create_var("a"),
                            ))),
                            Name::NVar(mettail_runtime::OrdVar(mettail_runtime::Var::Free(
                                mettail_runtime::get_or_create_var("a"),
                            ))),
                        ],
                        None,
                        mettail_runtime::Scope::from_parts_unsafe(
                            vec![mettail_runtime::Binder(mettail_runtime::get_or_create_var("a0"))],
                            std::sync::Arc::new(Proc::PVar(mettail_runtime::OrdVar(
                                mettail_runtime::Var::Free(mettail_runtime::get_or_create_var("a")),
                            ))),
                        ),
                    ),
                ]),
                mettail_runtime::Scope::from_parts_unsafe(
                    vec![mettail_runtime::Binder(mettail_runtime::get_or_create_var("a0"))],
                    std::sync::Arc::new(Proc::PInputsOptTagged(
                        vec![
                            Name::NVar(mettail_runtime::OrdVar(mettail_runtime::Var::Free(
                                mettail_runtime::get_or_create_var("a"),
                            ))),
                            Name::NVar(mettail_runtime::OrdVar(mettail_runtime::Var::Free(
                                mettail_runtime::get_or_create_var("a"),
                            ))),
                        ],
                        None,
                        mettail_runtime::Scope::from_parts_unsafe(
                            vec![mettail_runtime::Binder(mettail_runtime::get_or_create_var("a0"))],
                            std::sync::Arc::new(Proc::PVar(mettail_runtime::OrdVar(
                                mettail_runtime::Var::Free(mettail_runtime::get_or_create_var("a")),
                            ))),
                        ),
                    )),
                ),
            )),
        ),
    );

    // 2 — ANTI-VACUITY. The reconstructed term's normalised Debug must equal the
    //     text the corpus recorded, character for character. This is what makes
    //     "passes because it built the wrong term" impossible. Only
    //     `UniqueId(n)` and the ORDER of hash-container entries are quotiented
    //     out, and both are properties of the PROCESS rather than of the term:
    //     `UniqueId` comes from a global counter (and `FreeVar` equality is by
    //     unique_id alone, with the name fixing the identity through the var
    //     cache), and a `HashBag` is a multiset whose `PartialEq` ignores order.
    let recorded = "PInputsOptTagged([NVar(OrdVar(Free(FreeVar { unique_id: UniqueId(_), pretty_name: Some(\"a\") }))), NVar(OrdVar(Free(FreeVar { unique_id: UniqueId(_), pretty_name: Some(\"a\") })))], Some([PZero, PInputsOptTagged([NVar(OrdVar(Free(FreeVar { unique_id: UniqueId(_), pretty_name: Some(\"a\") }))), NVar(OrdVar(Free(FreeVar { unique_id: UniqueId(_), pretty_name: Some(\"a\") })))], Some([PZero, PInputsOptTagged([NVar(OrdVar(Free(FreeVar { unique_id: UniqueId(_), pretty_name: Some(\"a\") }))), NVar(OrdVar(Free(FreeVar { unique_id: UniqueId(_), pretty_name: Some(\"a\") })))], None, Scope { pattern: [Binder(FreeVar { unique_id: UniqueId(_), pretty_name: Some(\"a0\") })], body: PVar(OrdVar(Free(FreeVar { unique_id: UniqueId(_), pretty_name: Some(\"a\") }))) })]), Scope { pattern: [Binder(FreeVar { unique_id: UniqueId(_), pretty_name: Some(\"a0\") })], body: PInputsOptTagged([NVar(OrdVar(Free(FreeVar { unique_id: UniqueId(_), pretty_name: Some(\"a\") }))), NVar(OrdVar(Free(FreeVar { unique_id: UniqueId(_), pretty_name: Some(\"a\") })))], None, Scope { pattern: [Binder(FreeVar { unique_id: UniqueId(_), pretty_name: Some(\"a0\") })], body: PVar(OrdVar(Free(FreeVar { unique_id: UniqueId(_), pretty_name: Some(\"a\") }))) }) })]), Scope { pattern: [Binder(FreeVar { unique_id: UniqueId(_), pretty_name: Some(\"a0\") })], body: PInputsOptTagged([NVar(OrdVar(Free(FreeVar { unique_id: UniqueId(_), pretty_name: Some(\"a\") }))), NVar(OrdVar(Free(FreeVar { unique_id: UniqueId(_), pretty_name: Some(\"a\") })))], Some([PZero, PInputsOptTagged([NVar(OrdVar(Free(FreeVar { unique_id: UniqueId(_), pretty_name: Some(\"a\") }))), NVar(OrdVar(Free(FreeVar { unique_id: UniqueId(_), pretty_name: Some(\"a\") })))], None, Scope { pattern: [Binder(FreeVar { unique_id: UniqueId(_), pretty_name: Some(\"a0\") })], body: PVar(OrdVar(Free(FreeVar { unique_id: UniqueId(_), pretty_name: Some(\"a\") }))) })]), Scope { pattern: [Binder(FreeVar { unique_id: UniqueId(_), pretty_name: Some(\"a0\") })], body: PInputsOptTagged([NVar(OrdVar(Free(FreeVar { unique_id: UniqueId(_), pretty_name: Some(\"a\") }))), NVar(OrdVar(Free(FreeVar { unique_id: UniqueId(_), pretty_name: Some(\"a\") })))], None, Scope { pattern: [Binder(FreeVar { unique_id: UniqueId(_), pretty_name: Some(\"a0\") })], body: PVar(OrdVar(Free(FreeVar { unique_id: UniqueId(_), pretty_name: Some(\"a\") }))) }) }) })";
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
