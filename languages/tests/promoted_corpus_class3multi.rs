//! **Promoted counterexamples for `class3multi`** — every seed its proptest corpus records,
//! as a named regression test.
//!
//! # Where these came from, and why they are here
//!
//! `languages/tests/gen_class3multi_prop.proptest-regressions` holds 4 seed(s) for inputs
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
//!     target/generated/class3multi/rust_ctor.rs \
//!     languages/tests/gen_class3multi_prop.proptest-regressions
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
// Task #11: `class3multi`'s grammar is a test FIXTURE, not a production language — its
// definition lives in `languages/tests/definitions/class3multi.rs` rather than in the `languages`
// library, so it is `#[path]`-included here. This binary is a CONSUMER: it deliberately does
// NOT invoke the `class3multi_generated_tests!` wrapper, because the definition's designated host is its own smoke-test binary and is the sole
// invoker, so the generated suite stays single-instanced across the workspace.
#[path = "definitions/class3multi.rs"]
mod class3multi;
use crate::class3multi::*;

/// Corpus entry 0 — seed `cc 2049c30c273b3c597d7602a158732f03f5af9f9623f0e208b7ba4f60eb9f0cc5`.
///
/// Recorded counterexample, verbatim from the corpus:
/// ```text
/// term = NQuote(TaggedInputs([], [NVar(OrdVar(Free(FreeVar { unique_id: UniqueId(16),
/// pretty_name: Some("a") }))), NVar(OrdVar(Free(FreeVar { unique_id: UniqueId(16),
/// pretty_name: Some("a") })))], Scope { pattern: [Binder(FreeVar { unique_id: UniqueId(13),
/// pretty_name: Some("a0") }), Binder(FreeVar { unique_id: UniqueId(14), pretty_name:
/// Some("a1") }), Binder(FreeVar { unique_id: UniqueId(15), pretty_name: Some("a2") })], body:
/// TaggedInputs([], [NVar(OrdVar(Free(FreeVar { unique_id: UniqueId(16), pretty_name: Some("a")
/// }))), NVar(OrdVar(Free(FreeVar { unique_id: UniqueId(16), pretty_name: Some("a") })))],
/// Scope { pattern: [Binder(FreeVar { unique_id: UniqueId(13), pretty_name: Some("a0") })],
/// body: PZero }) }))
/// ```
#[test]
fn corpus_0_name() {
    mettail_runtime::clear_var_cache();
    // 1 — the term CONSTRUCTS.
    let term: Name = Name::NQuote(std::sync::Arc::new(Proc::TaggedInputs(
        vec![],
        vec![
            Name::NVar(mettail_runtime::OrdVar(mettail_runtime::Var::Free(
                mettail_runtime::get_or_create_var("a"),
            ))),
            Name::NVar(mettail_runtime::OrdVar(mettail_runtime::Var::Free(
                mettail_runtime::get_or_create_var("a"),
            ))),
        ],
        mettail_runtime::Scope::from_parts_unsafe(
            vec![
                mettail_runtime::Binder(mettail_runtime::get_or_create_var("a0")),
                mettail_runtime::Binder(mettail_runtime::get_or_create_var("a1")),
                mettail_runtime::Binder(mettail_runtime::get_or_create_var("a2")),
            ],
            std::sync::Arc::new(Proc::TaggedInputs(
                vec![],
                vec![
                    Name::NVar(mettail_runtime::OrdVar(mettail_runtime::Var::Free(
                        mettail_runtime::get_or_create_var("a"),
                    ))),
                    Name::NVar(mettail_runtime::OrdVar(mettail_runtime::Var::Free(
                        mettail_runtime::get_or_create_var("a"),
                    ))),
                ],
                mettail_runtime::Scope::from_parts_unsafe(
                    vec![mettail_runtime::Binder(mettail_runtime::get_or_create_var("a0"))],
                    std::sync::Arc::new(Proc::PZero),
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
    let recorded = "NQuote(TaggedInputs([], [NVar(OrdVar(Free(FreeVar { unique_id: UniqueId(_), pretty_name: Some(\"a\") }))), NVar(OrdVar(Free(FreeVar { unique_id: UniqueId(_), pretty_name: Some(\"a\") })))], Scope { pattern: [Binder(FreeVar { unique_id: UniqueId(_), pretty_name: Some(\"a0\") }), Binder(FreeVar { unique_id: UniqueId(_), pretty_name: Some(\"a1\") }), Binder(FreeVar { unique_id: UniqueId(_), pretty_name: Some(\"a2\") })], body: TaggedInputs([], [NVar(OrdVar(Free(FreeVar { unique_id: UniqueId(_), pretty_name: Some(\"a\") }))), NVar(OrdVar(Free(FreeVar { unique_id: UniqueId(_), pretty_name: Some(\"a\") })))], Scope { pattern: [Binder(FreeVar { unique_id: UniqueId(_), pretty_name: Some(\"a0\") })], body: PZero }) }))";
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

/// Corpus entry 1 — seed `cc 495a96b8261570ea3a39202646cdd094f83fe45767b62090ececeabb1036fcfc`.
///
/// Recorded counterexample, verbatim from the corpus:
/// ```text
/// term = TaggedInputs([PZero, PZero], [NVar(OrdVar(Free(FreeVar { unique_id: UniqueId(6),
/// pretty_name: Some("a") })))], Scope { pattern: [Binder(FreeVar { unique_id: UniqueId(7),
/// pretty_name: Some("a0") })], body: TaggedInputs([TaggedInputs([], [], Scope { pattern:
/// [Binder(FreeVar { unique_id: UniqueId(7), pretty_name: Some("a0") }), Binder(FreeVar {
/// unique_id: UniqueId(8), pretty_name: Some("a1") })], body: PZero }), PZero], [], Scope {
/// pattern: [Binder(FreeVar { unique_id: UniqueId(7), pretty_name: Some("a0") }),
/// Binder(FreeVar { unique_id: UniqueId(8), pretty_name: Some("a1") }), Binder(FreeVar {
/// unique_id: UniqueId(9), pretty_name: Some("a2") })], body: TaggedInputs([PZero, PZero],
/// [NVar(OrdVar(Free(FreeVar { unique_id: UniqueId(6), pretty_name: Some("a") })))], Scope {
/// pattern: [Binder(FreeVar { unique_id: UniqueId(7), pretty_name: Some("a0") })], body: PZero
/// }) }) })
/// ```
#[test]
fn corpus_1_proc() {
    mettail_runtime::clear_var_cache();
    // 1 — the term CONSTRUCTS.
    let term: Proc = Proc::TaggedInputs(
        vec![Proc::PZero, Proc::PZero],
        vec![Name::NVar(mettail_runtime::OrdVar(mettail_runtime::Var::Free(
            mettail_runtime::get_or_create_var("a"),
        )))],
        mettail_runtime::Scope::from_parts_unsafe(
            vec![mettail_runtime::Binder(mettail_runtime::get_or_create_var("a0"))],
            std::sync::Arc::new(Proc::TaggedInputs(
                vec![
                    Proc::TaggedInputs(
                        vec![],
                        vec![],
                        mettail_runtime::Scope::from_parts_unsafe(
                            vec![
                                mettail_runtime::Binder(mettail_runtime::get_or_create_var("a0")),
                                mettail_runtime::Binder(mettail_runtime::get_or_create_var("a1")),
                            ],
                            std::sync::Arc::new(Proc::PZero),
                        ),
                    ),
                    Proc::PZero,
                ],
                vec![],
                mettail_runtime::Scope::from_parts_unsafe(
                    vec![
                        mettail_runtime::Binder(mettail_runtime::get_or_create_var("a0")),
                        mettail_runtime::Binder(mettail_runtime::get_or_create_var("a1")),
                        mettail_runtime::Binder(mettail_runtime::get_or_create_var("a2")),
                    ],
                    std::sync::Arc::new(Proc::TaggedInputs(
                        vec![Proc::PZero, Proc::PZero],
                        vec![Name::NVar(mettail_runtime::OrdVar(mettail_runtime::Var::Free(
                            mettail_runtime::get_or_create_var("a"),
                        )))],
                        mettail_runtime::Scope::from_parts_unsafe(
                            vec![mettail_runtime::Binder(mettail_runtime::get_or_create_var("a0"))],
                            std::sync::Arc::new(Proc::PZero),
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
    let recorded = "TaggedInputs([PZero, PZero], [NVar(OrdVar(Free(FreeVar { unique_id: UniqueId(_), pretty_name: Some(\"a\") })))], Scope { pattern: [Binder(FreeVar { unique_id: UniqueId(_), pretty_name: Some(\"a0\") })], body: TaggedInputs([TaggedInputs([], [], Scope { pattern: [Binder(FreeVar { unique_id: UniqueId(_), pretty_name: Some(\"a0\") }), Binder(FreeVar { unique_id: UniqueId(_), pretty_name: Some(\"a1\") })], body: PZero }), PZero], [], Scope { pattern: [Binder(FreeVar { unique_id: UniqueId(_), pretty_name: Some(\"a0\") }), Binder(FreeVar { unique_id: UniqueId(_), pretty_name: Some(\"a1\") }), Binder(FreeVar { unique_id: UniqueId(_), pretty_name: Some(\"a2\") })], body: TaggedInputs([PZero, PZero], [NVar(OrdVar(Free(FreeVar { unique_id: UniqueId(_), pretty_name: Some(\"a\") })))], Scope { pattern: [Binder(FreeVar { unique_id: UniqueId(_), pretty_name: Some(\"a0\") })], body: PZero }) }) })";
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

/// Corpus entry 2 — seed `cc 1bcde8ac43f53874b07e7e26b0dfa372ffbb8ea7d46faad41434dde1213a4efa`.
///
/// Recorded counterexample, verbatim from the corpus:
/// ```text
/// term = TaggedInputs([TaggedInputs([], [], Scope { pattern: [Binder(FreeVar { unique_id:
/// UniqueId(1), pretty_name: Some("a0") })], body: TaggedInputs([PVar(OrdVar(Free(FreeVar {
/// unique_id: UniqueId(0), pretty_name: Some("a") })))], [], Scope { pattern: [Binder(FreeVar {
/// unique_id: UniqueId(1), pretty_name: Some("a0") })], body: PVar(OrdVar(Free(FreeVar {
/// unique_id: UniqueId(0), pretty_name: Some("a") }))) }) })], [NVar(OrdVar(Free(FreeVar {
/// unique_id: UniqueId(0), pretty_name: Some("a") }))), NQuote(PZero)], Scope { pattern:
/// [Binder(FreeVar { unique_id: UniqueId(1), pretty_name: Some("a0") })], body:
/// TaggedInputs([PVar(OrdVar(Free(FreeVar { unique_id: UniqueId(0), pretty_name: Some("a")
/// })))], [], Scope { pattern: [Binder(FreeVar { unique_id: UniqueId(1), pretty_name:
/// Some("a0") })], body: PVar(OrdVar(Free(FreeVar { unique_id: UniqueId(0), pretty_name:
/// Some("a") }))) }) })
/// ```
#[test]
fn corpus_2_proc() {
    mettail_runtime::clear_var_cache();
    // 1 — the term CONSTRUCTS.
    let term: Proc = Proc::TaggedInputs(
        vec![Proc::TaggedInputs(
            vec![],
            vec![],
            mettail_runtime::Scope::from_parts_unsafe(
                vec![mettail_runtime::Binder(mettail_runtime::get_or_create_var("a0"))],
                std::sync::Arc::new(Proc::TaggedInputs(
                    vec![Proc::PVar(mettail_runtime::OrdVar(mettail_runtime::Var::Free(
                        mettail_runtime::get_or_create_var("a"),
                    )))],
                    vec![],
                    mettail_runtime::Scope::from_parts_unsafe(
                        vec![mettail_runtime::Binder(mettail_runtime::get_or_create_var("a0"))],
                        std::sync::Arc::new(Proc::PVar(mettail_runtime::OrdVar(
                            mettail_runtime::Var::Free(mettail_runtime::get_or_create_var("a")),
                        ))),
                    ),
                )),
            ),
        )],
        vec![
            Name::NVar(mettail_runtime::OrdVar(mettail_runtime::Var::Free(
                mettail_runtime::get_or_create_var("a"),
            ))),
            Name::NQuote(std::sync::Arc::new(Proc::PZero)),
        ],
        mettail_runtime::Scope::from_parts_unsafe(
            vec![mettail_runtime::Binder(mettail_runtime::get_or_create_var("a0"))],
            std::sync::Arc::new(Proc::TaggedInputs(
                vec![Proc::PVar(mettail_runtime::OrdVar(mettail_runtime::Var::Free(
                    mettail_runtime::get_or_create_var("a"),
                )))],
                vec![],
                mettail_runtime::Scope::from_parts_unsafe(
                    vec![mettail_runtime::Binder(mettail_runtime::get_or_create_var("a0"))],
                    std::sync::Arc::new(Proc::PVar(mettail_runtime::OrdVar(
                        mettail_runtime::Var::Free(mettail_runtime::get_or_create_var("a")),
                    ))),
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
    let recorded = "TaggedInputs([TaggedInputs([], [], Scope { pattern: [Binder(FreeVar { unique_id: UniqueId(_), pretty_name: Some(\"a0\") })], body: TaggedInputs([PVar(OrdVar(Free(FreeVar { unique_id: UniqueId(_), pretty_name: Some(\"a\") })))], [], Scope { pattern: [Binder(FreeVar { unique_id: UniqueId(_), pretty_name: Some(\"a0\") })], body: PVar(OrdVar(Free(FreeVar { unique_id: UniqueId(_), pretty_name: Some(\"a\") }))) }) })], [NVar(OrdVar(Free(FreeVar { unique_id: UniqueId(_), pretty_name: Some(\"a\") }))), NQuote(PZero)], Scope { pattern: [Binder(FreeVar { unique_id: UniqueId(_), pretty_name: Some(\"a0\") })], body: TaggedInputs([PVar(OrdVar(Free(FreeVar { unique_id: UniqueId(_), pretty_name: Some(\"a\") })))], [], Scope { pattern: [Binder(FreeVar { unique_id: UniqueId(_), pretty_name: Some(\"a0\") })], body: PVar(OrdVar(Free(FreeVar { unique_id: UniqueId(_), pretty_name: Some(\"a\") }))) }) })";
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

/// Corpus entry 3 — seed `cc e62de4cbf291bea342ac5f3ad8cfa51d18d2bda9043bb0e523958966f02193f5`.
///
/// Recorded counterexample, verbatim from the corpus:
/// ```text
/// term = TaggedInputs([TaggedInputs([TaggedInputs([PVar(OrdVar(Free(FreeVar { unique_id:
/// UniqueId(2), pretty_name: Some("a") }))), PVar(OrdVar(Free(FreeVar { unique_id: UniqueId(2),
/// pretty_name: Some("a") })))], [NVar(OrdVar(Free(FreeVar { unique_id: UniqueId(2),
/// pretty_name: Some("a") }))), NVar(OrdVar(Free(FreeVar { unique_id: UniqueId(2), pretty_name:
/// Some("a") })))], Scope { pattern: [Binder(FreeVar { unique_id: UniqueId(0), pretty_name:
/// Some("a0") }), Binder(FreeVar { unique_id: UniqueId(1), pretty_name: Some("a1") }),
/// Binder(FreeVar { unique_id: UniqueId(3), pretty_name: Some("a2") })], body:
/// PVar(OrdVar(Free(FreeVar { unique_id: UniqueId(2), pretty_name: Some("a") }))) }),
/// TaggedInputs([PVar(OrdVar(Free(FreeVar { unique_id: UniqueId(2), pretty_name: Some("a")
/// }))), PVar(OrdVar(Free(FreeVar { unique_id: UniqueId(2), pretty_name: Some("a") })))],
/// [NVar(OrdVar(Free(FreeVar { unique_id: UniqueId(2), pretty_name: Some("a") }))),
/// NVar(OrdVar(Free(FreeVar { unique_id: UniqueId(2), pretty_name: Some("a") })))], Scope {
/// pattern: [Binder(FreeVar { unique_id: UniqueId(0), pretty_name: Some("a0") }),
/// Binder(FreeVar { unique_id: UniqueId(1), pretty_name: Some("a1") }), Binder(FreeVar {
/// unique_id: UniqueId(3), pretty_name: Some("a2") })], body: PVar(OrdVar(Free(FreeVar {
/// unique_id: UniqueId(2), pretty_name: Some("a") }))) })], [NQuote(PVar(OrdVar(Free(FreeVar {
/// unique_id: UniqueId(2), pretty_name: Some("a") })))), NQuote(PVar(OrdVar(Free(FreeVar {
/// unique_id: UniqueId(2), pretty_name: Some("a") }))))], Scope { pattern: [Binder(FreeVar {
/// unique_id: UniqueId(0), pretty_name: Some("a0") }), Binder(FreeVar { unique_id: UniqueId(1),
/// pretty_name: Some("a1") }), Binder(FreeVar { unique_id: UniqueId(3), pretty_name: Some("a2")
/// })], body: TaggedInputs([PVar(OrdVar(Free(FreeVar { unique_id: UniqueId(2), pretty_name:
/// Some("a") }))), PVar(OrdVar(Free(FreeVar { unique_id: UniqueId(2), pretty_name: Some("a")
/// })))], [NVar(OrdVar(Free(FreeVar { unique_id: UniqueId(2), pretty_name: Some("a") }))),
/// NVar(OrdVar(Free(FreeVar { unique_id: UniqueId(2), pretty_name: Some("a") })))], Scope {
/// pattern: [Binder(FreeVar { unique_id: UniqueId(0), pretty_name: Some("a0") }),
/// Binder(FreeVar { unique_id: UniqueId(1), pretty_name: Some("a1") }), Binder(FreeVar {
/// unique_id: UniqueId(3), pretty_name: Some("a2") })], body: PVar(OrdVar(Free(FreeVar {
/// unique_id: UniqueId(2), pretty_name: Some("a") }))) }) }),
/// TaggedInputs([TaggedInputs([PVar(OrdVar(Free(FreeVar { unique_id: UniqueId(2), pretty_name:
/// Some("a") }))), PVar(OrdVar(Free(FreeVar { unique_id: UniqueId(2), pretty_name: Some("a")
/// })))], [NVar(OrdVar(Free(FreeVar { unique_id: UniqueId(2), pretty_name: Some("a") }))),
/// NVar(OrdVar(Free(FreeVar { unique_id: UniqueId(2), pretty_name: Some("a") })))], Scope {
/// pattern: [Binder(FreeVar { unique_id: UniqueId(0), pretty_name: Some("a0") }),
/// Binder(FreeVar { unique_id: UniqueId(1), pretty_name: Some("a1") }), Binder(FreeVar {
/// unique_id: UniqueId(3), pretty_name: Some("a2") })], body: PVar(OrdVar(Free(FreeVar {
/// unique_id: UniqueId(2), pretty_name: Some("a") }))) }),
/// TaggedInputs([PVar(OrdVar(Free(FreeVar { unique_id: UniqueId(2), pretty_name: Some("a")
/// }))), PVar(OrdVar(Free(FreeVar { unique_id: UniqueId(2), pretty_name: Some("a") })))],
/// [NVar(OrdVar(Free(FreeVar { unique_id: UniqueId(2), pretty_name: Some("a") }))),
/// NVar(OrdVar(Free(FreeVar { unique_id: UniqueId(2), pretty_name: Some("a") })))], Scope {
/// pattern: [Binder(FreeVar { unique_id: UniqueId(0), pretty_name: Some("a0") }),
/// Binder(FreeVar { unique_id: UniqueId(1), pretty_name: Some("a1") }), Binder(FreeVar {
/// unique_id: UniqueId(3), pretty_name: Some("a2") })], body: PVar(OrdVar(Free(FreeVar {
/// unique_id: UniqueId(2), pretty_name: Some("a") }))) })], [NQuote(PVar(OrdVar(Free(FreeVar {
/// unique_id: UniqueId(2), pretty_name: Some("a") })))), NQuote(PVar(OrdVar(Free(FreeVar {
/// unique_id: UniqueId(2), pretty_name: Some("a") }))))], Scope { pattern: [Binder(FreeVar {
/// unique_id: UniqueId(0), pretty_name: Some("a0") }), Binder(FreeVar { unique_id: UniqueId(1),
/// pretty_name: Some("a1") }), Binder(FreeVar { unique_id: UniqueId(3), pretty_name: Some("a2")
/// })], body: TaggedInputs([PVar(OrdVar(Free(FreeVar { unique_id: UniqueId(2), pretty_name:
/// Some("a") }))), PVar(OrdVar(Free(FreeVar { unique_id: UniqueId(2), pretty_name: Some("a")
/// })))], [NVar(OrdVar(Free(FreeVar { unique_id: UniqueId(2), pretty_name: Some("a") }))),
/// NVar(OrdVar(Free(FreeVar { unique_id: UniqueId(2), pretty_name: Some("a") })))], Scope {
/// pattern: [Binder(FreeVar { unique_id: UniqueId(0), pretty_name: Some("a0") }),
/// Binder(FreeVar { unique_id: UniqueId(1), pretty_name: Some("a1") }), Binder(FreeVar {
/// unique_id: UniqueId(3), pretty_name: Some("a2") })], body: PVar(OrdVar(Free(FreeVar {
/// unique_id: UniqueId(2), pretty_name: Some("a") }))) }) })],
/// [NQuote(TaggedInputs([PVar(OrdVar(Free(FreeVar { unique_id: UniqueId(2), pretty_name:
/// Some("a") }))), PVar(OrdVar(Free(FreeVar { unique_id: UniqueId(2), pretty_name: Some("a")
/// })))], [NVar(OrdVar(Free(FreeVar { unique_id: UniqueId(2), pretty_name: Some("a") }))),
/// NVar(OrdVar(Free(FreeVar { unique_id: UniqueId(2), pretty_name: Some("a") })))], Scope {
/// pattern: [Binder(FreeVar { unique_id: UniqueId(0), pretty_name: Some("a0") }),
/// Binder(FreeVar { unique_id: UniqueId(1), pretty_name: Some("a1") }), Binder(FreeVar {
/// unique_id: UniqueId(3), pretty_name: Some("a2") })], body: PVar(OrdVar(Free(FreeVar {
/// unique_id: UniqueId(2), pretty_name: Some("a") }))) })),
/// NQuote(TaggedInputs([PVar(OrdVar(Free(FreeVar { unique_id: UniqueId(2), pretty_name:
/// Some("a") }))), PVar(OrdVar(Free(FreeVar { unique_id: UniqueId(2), pretty_name: Some("a")
/// })))], [NVar(OrdVar(Free(FreeVar { unique_id: UniqueId(2), pretty_name: Some("a") }))),
/// NVar(OrdVar(Free(FreeVar { unique_id: UniqueId(2), pretty_name: Some("a") })))], Scope {
/// pattern: [Binder(FreeVar { unique_id: UniqueId(0), pretty_name: Some("a0") }),
/// Binder(FreeVar { unique_id: UniqueId(1), pretty_name: Some("a1") }), Binder(FreeVar {
/// unique_id: UniqueId(3), pretty_name: Some("a2") })], body: PVar(OrdVar(Free(FreeVar {
/// unique_id: UniqueId(2), pretty_name: Some("a") }))) }))], Scope { pattern: [Binder(FreeVar {
/// unique_id: UniqueId(0), pretty_name: Some("a0") }), Binder(FreeVar { unique_id: UniqueId(1),
/// pretty_name: Some("a1") }), Binder(FreeVar { unique_id: UniqueId(3), pretty_name: Some("a2")
/// })], body: TaggedInputs([TaggedInputs([PVar(OrdVar(Free(FreeVar { unique_id: UniqueId(2),
/// pretty_name: Some("a") }))), PVar(OrdVar(Free(FreeVar { unique_id: UniqueId(2), pretty_name:
/// Some("a") })))], [NVar(OrdVar(Free(FreeVar { unique_id: UniqueId(2), pretty_name: Some("a")
/// }))), NVar(OrdVar(Free(FreeVar { unique_id: UniqueId(2), pretty_name: Some("a") })))], Scope
/// { pattern: [Binder(FreeVar { unique_id: UniqueId(0), pretty_name: Some("a0") }),
/// Binder(FreeVar { unique_id: UniqueId(1), pretty_name: Some("a1") }), Binder(FreeVar {
/// unique_id: UniqueId(3), pretty_name: Some("a2") })], body: PVar(OrdVar(Free(FreeVar {
/// unique_id: UniqueId(2), pretty_name: Some("a") }))) }),
/// TaggedInputs([PVar(OrdVar(Free(FreeVar { unique_id: UniqueId(2), pretty_name: Some("a")
/// }))), PVar(OrdVar(Free(FreeVar { unique_id: UniqueId(2), pretty_name: Some("a") })))],
/// [NVar(OrdVar(Free(FreeVar { unique_id: UniqueId(2), pretty_name: Some("a") }))),
/// NVar(OrdVar(Free(FreeVar { unique_id: UniqueId(2), pretty_name: Some("a") })))], Scope {
/// pattern: [Binder(FreeVar { unique_id: UniqueId(0), pretty_name: Some("a0") }),
/// Binder(FreeVar { unique_id: UniqueId(1), pretty_name: Some("a1") }), Binder(FreeVar {
/// unique_id: UniqueId(3), pretty_name: Some("a2") })], body: PVar(OrdVar(Free(FreeVar {
/// unique_id: UniqueId(2), pretty_name: Some("a") }))) })], [NQuote(PVar(OrdVar(Free(FreeVar {
/// unique_id: UniqueId(2), pretty_name: Some("a") })))), NQuote(PVar(OrdVar(Free(FreeVar {
/// unique_id: UniqueId(2), pretty_name: Some("a") }))))], Scope { pattern: [Binder(FreeVar {
/// unique_id: UniqueId(0), pretty_name: Some("a0") }), Binder(FreeVar { unique_id: UniqueId(1),
/// pretty_name: Some("a1") }), Binder(FreeVar { unique_id: UniqueId(3), pretty_name: Some("a2")
/// })], body: TaggedInputs([PVar(OrdVar(Free(FreeVar { unique_id: UniqueId(2), pretty_name:
/// Some("a") }))), PVar(OrdVar(Free(FreeVar { unique_id: UniqueId(2), pretty_name: Some("a")
/// })))], [NVar(OrdVar(Free(FreeVar { unique_id: UniqueId(2), pretty_name: Some("a") }))),
/// NVar(OrdVar(Free(FreeVar { unique_id: UniqueId(2), pretty_name: Some("a") })))], Scope {
/// pattern: [Binder(FreeVar { unique_id: UniqueId(0), pretty_name: Some("a0") }),
/// Binder(FreeVar { unique_id: UniqueId(1), pretty_name: Some("a1") }), Binder(FreeVar {
/// unique_id: UniqueId(3), pretty_name: Some("a2") })], body: PVar(OrdVar(Free(FreeVar {
/// unique_id: UniqueId(2), pretty_name: Some("a") }))) }) }) })
/// ```
#[test]
fn corpus_3_proc() {
    mettail_runtime::clear_var_cache();
    // 1 — the term CONSTRUCTS.
    let term: Proc = Proc::TaggedInputs(
        vec![
            Proc::TaggedInputs(
                vec![
                    Proc::TaggedInputs(
                        vec![
                            Proc::PVar(mettail_runtime::OrdVar(mettail_runtime::Var::Free(
                                mettail_runtime::get_or_create_var("a"),
                            ))),
                            Proc::PVar(mettail_runtime::OrdVar(mettail_runtime::Var::Free(
                                mettail_runtime::get_or_create_var("a"),
                            ))),
                        ],
                        vec![
                            Name::NVar(mettail_runtime::OrdVar(mettail_runtime::Var::Free(
                                mettail_runtime::get_or_create_var("a"),
                            ))),
                            Name::NVar(mettail_runtime::OrdVar(mettail_runtime::Var::Free(
                                mettail_runtime::get_or_create_var("a"),
                            ))),
                        ],
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
                    ),
                    Proc::TaggedInputs(
                        vec![
                            Proc::PVar(mettail_runtime::OrdVar(mettail_runtime::Var::Free(
                                mettail_runtime::get_or_create_var("a"),
                            ))),
                            Proc::PVar(mettail_runtime::OrdVar(mettail_runtime::Var::Free(
                                mettail_runtime::get_or_create_var("a"),
                            ))),
                        ],
                        vec![
                            Name::NVar(mettail_runtime::OrdVar(mettail_runtime::Var::Free(
                                mettail_runtime::get_or_create_var("a"),
                            ))),
                            Name::NVar(mettail_runtime::OrdVar(mettail_runtime::Var::Free(
                                mettail_runtime::get_or_create_var("a"),
                            ))),
                        ],
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
                    ),
                ],
                vec![
                    Name::NQuote(std::sync::Arc::new(Proc::PVar(mettail_runtime::OrdVar(
                        mettail_runtime::Var::Free(mettail_runtime::get_or_create_var("a")),
                    )))),
                    Name::NQuote(std::sync::Arc::new(Proc::PVar(mettail_runtime::OrdVar(
                        mettail_runtime::Var::Free(mettail_runtime::get_or_create_var("a")),
                    )))),
                ],
                mettail_runtime::Scope::from_parts_unsafe(
                    vec![
                        mettail_runtime::Binder(mettail_runtime::get_or_create_var("a0")),
                        mettail_runtime::Binder(mettail_runtime::get_or_create_var("a1")),
                        mettail_runtime::Binder(mettail_runtime::get_or_create_var("a2")),
                    ],
                    std::sync::Arc::new(Proc::TaggedInputs(
                        vec![
                            Proc::PVar(mettail_runtime::OrdVar(mettail_runtime::Var::Free(
                                mettail_runtime::get_or_create_var("a"),
                            ))),
                            Proc::PVar(mettail_runtime::OrdVar(mettail_runtime::Var::Free(
                                mettail_runtime::get_or_create_var("a"),
                            ))),
                        ],
                        vec![
                            Name::NVar(mettail_runtime::OrdVar(mettail_runtime::Var::Free(
                                mettail_runtime::get_or_create_var("a"),
                            ))),
                            Name::NVar(mettail_runtime::OrdVar(mettail_runtime::Var::Free(
                                mettail_runtime::get_or_create_var("a"),
                            ))),
                        ],
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
            ),
            Proc::TaggedInputs(
                vec![
                    Proc::TaggedInputs(
                        vec![
                            Proc::PVar(mettail_runtime::OrdVar(mettail_runtime::Var::Free(
                                mettail_runtime::get_or_create_var("a"),
                            ))),
                            Proc::PVar(mettail_runtime::OrdVar(mettail_runtime::Var::Free(
                                mettail_runtime::get_or_create_var("a"),
                            ))),
                        ],
                        vec![
                            Name::NVar(mettail_runtime::OrdVar(mettail_runtime::Var::Free(
                                mettail_runtime::get_or_create_var("a"),
                            ))),
                            Name::NVar(mettail_runtime::OrdVar(mettail_runtime::Var::Free(
                                mettail_runtime::get_or_create_var("a"),
                            ))),
                        ],
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
                    ),
                    Proc::TaggedInputs(
                        vec![
                            Proc::PVar(mettail_runtime::OrdVar(mettail_runtime::Var::Free(
                                mettail_runtime::get_or_create_var("a"),
                            ))),
                            Proc::PVar(mettail_runtime::OrdVar(mettail_runtime::Var::Free(
                                mettail_runtime::get_or_create_var("a"),
                            ))),
                        ],
                        vec![
                            Name::NVar(mettail_runtime::OrdVar(mettail_runtime::Var::Free(
                                mettail_runtime::get_or_create_var("a"),
                            ))),
                            Name::NVar(mettail_runtime::OrdVar(mettail_runtime::Var::Free(
                                mettail_runtime::get_or_create_var("a"),
                            ))),
                        ],
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
                    ),
                ],
                vec![
                    Name::NQuote(std::sync::Arc::new(Proc::PVar(mettail_runtime::OrdVar(
                        mettail_runtime::Var::Free(mettail_runtime::get_or_create_var("a")),
                    )))),
                    Name::NQuote(std::sync::Arc::new(Proc::PVar(mettail_runtime::OrdVar(
                        mettail_runtime::Var::Free(mettail_runtime::get_or_create_var("a")),
                    )))),
                ],
                mettail_runtime::Scope::from_parts_unsafe(
                    vec![
                        mettail_runtime::Binder(mettail_runtime::get_or_create_var("a0")),
                        mettail_runtime::Binder(mettail_runtime::get_or_create_var("a1")),
                        mettail_runtime::Binder(mettail_runtime::get_or_create_var("a2")),
                    ],
                    std::sync::Arc::new(Proc::TaggedInputs(
                        vec![
                            Proc::PVar(mettail_runtime::OrdVar(mettail_runtime::Var::Free(
                                mettail_runtime::get_or_create_var("a"),
                            ))),
                            Proc::PVar(mettail_runtime::OrdVar(mettail_runtime::Var::Free(
                                mettail_runtime::get_or_create_var("a"),
                            ))),
                        ],
                        vec![
                            Name::NVar(mettail_runtime::OrdVar(mettail_runtime::Var::Free(
                                mettail_runtime::get_or_create_var("a"),
                            ))),
                            Name::NVar(mettail_runtime::OrdVar(mettail_runtime::Var::Free(
                                mettail_runtime::get_or_create_var("a"),
                            ))),
                        ],
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
            ),
        ],
        vec![
            Name::NQuote(std::sync::Arc::new(Proc::TaggedInputs(
                vec![
                    Proc::PVar(mettail_runtime::OrdVar(mettail_runtime::Var::Free(
                        mettail_runtime::get_or_create_var("a"),
                    ))),
                    Proc::PVar(mettail_runtime::OrdVar(mettail_runtime::Var::Free(
                        mettail_runtime::get_or_create_var("a"),
                    ))),
                ],
                vec![
                    Name::NVar(mettail_runtime::OrdVar(mettail_runtime::Var::Free(
                        mettail_runtime::get_or_create_var("a"),
                    ))),
                    Name::NVar(mettail_runtime::OrdVar(mettail_runtime::Var::Free(
                        mettail_runtime::get_or_create_var("a"),
                    ))),
                ],
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
            ))),
            Name::NQuote(std::sync::Arc::new(Proc::TaggedInputs(
                vec![
                    Proc::PVar(mettail_runtime::OrdVar(mettail_runtime::Var::Free(
                        mettail_runtime::get_or_create_var("a"),
                    ))),
                    Proc::PVar(mettail_runtime::OrdVar(mettail_runtime::Var::Free(
                        mettail_runtime::get_or_create_var("a"),
                    ))),
                ],
                vec![
                    Name::NVar(mettail_runtime::OrdVar(mettail_runtime::Var::Free(
                        mettail_runtime::get_or_create_var("a"),
                    ))),
                    Name::NVar(mettail_runtime::OrdVar(mettail_runtime::Var::Free(
                        mettail_runtime::get_or_create_var("a"),
                    ))),
                ],
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
            ))),
        ],
        mettail_runtime::Scope::from_parts_unsafe(
            vec![
                mettail_runtime::Binder(mettail_runtime::get_or_create_var("a0")),
                mettail_runtime::Binder(mettail_runtime::get_or_create_var("a1")),
                mettail_runtime::Binder(mettail_runtime::get_or_create_var("a2")),
            ],
            std::sync::Arc::new(Proc::TaggedInputs(
                vec![
                    Proc::TaggedInputs(
                        vec![
                            Proc::PVar(mettail_runtime::OrdVar(mettail_runtime::Var::Free(
                                mettail_runtime::get_or_create_var("a"),
                            ))),
                            Proc::PVar(mettail_runtime::OrdVar(mettail_runtime::Var::Free(
                                mettail_runtime::get_or_create_var("a"),
                            ))),
                        ],
                        vec![
                            Name::NVar(mettail_runtime::OrdVar(mettail_runtime::Var::Free(
                                mettail_runtime::get_or_create_var("a"),
                            ))),
                            Name::NVar(mettail_runtime::OrdVar(mettail_runtime::Var::Free(
                                mettail_runtime::get_or_create_var("a"),
                            ))),
                        ],
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
                    ),
                    Proc::TaggedInputs(
                        vec![
                            Proc::PVar(mettail_runtime::OrdVar(mettail_runtime::Var::Free(
                                mettail_runtime::get_or_create_var("a"),
                            ))),
                            Proc::PVar(mettail_runtime::OrdVar(mettail_runtime::Var::Free(
                                mettail_runtime::get_or_create_var("a"),
                            ))),
                        ],
                        vec![
                            Name::NVar(mettail_runtime::OrdVar(mettail_runtime::Var::Free(
                                mettail_runtime::get_or_create_var("a"),
                            ))),
                            Name::NVar(mettail_runtime::OrdVar(mettail_runtime::Var::Free(
                                mettail_runtime::get_or_create_var("a"),
                            ))),
                        ],
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
                    ),
                ],
                vec![
                    Name::NQuote(std::sync::Arc::new(Proc::PVar(mettail_runtime::OrdVar(
                        mettail_runtime::Var::Free(mettail_runtime::get_or_create_var("a")),
                    )))),
                    Name::NQuote(std::sync::Arc::new(Proc::PVar(mettail_runtime::OrdVar(
                        mettail_runtime::Var::Free(mettail_runtime::get_or_create_var("a")),
                    )))),
                ],
                mettail_runtime::Scope::from_parts_unsafe(
                    vec![
                        mettail_runtime::Binder(mettail_runtime::get_or_create_var("a0")),
                        mettail_runtime::Binder(mettail_runtime::get_or_create_var("a1")),
                        mettail_runtime::Binder(mettail_runtime::get_or_create_var("a2")),
                    ],
                    std::sync::Arc::new(Proc::TaggedInputs(
                        vec![
                            Proc::PVar(mettail_runtime::OrdVar(mettail_runtime::Var::Free(
                                mettail_runtime::get_or_create_var("a"),
                            ))),
                            Proc::PVar(mettail_runtime::OrdVar(mettail_runtime::Var::Free(
                                mettail_runtime::get_or_create_var("a"),
                            ))),
                        ],
                        vec![
                            Name::NVar(mettail_runtime::OrdVar(mettail_runtime::Var::Free(
                                mettail_runtime::get_or_create_var("a"),
                            ))),
                            Name::NVar(mettail_runtime::OrdVar(mettail_runtime::Var::Free(
                                mettail_runtime::get_or_create_var("a"),
                            ))),
                        ],
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
    let recorded = "TaggedInputs([TaggedInputs([TaggedInputs([PVar(OrdVar(Free(FreeVar { unique_id: UniqueId(_), pretty_name: Some(\"a\") }))), PVar(OrdVar(Free(FreeVar { unique_id: UniqueId(_), pretty_name: Some(\"a\") })))], [NVar(OrdVar(Free(FreeVar { unique_id: UniqueId(_), pretty_name: Some(\"a\") }))), NVar(OrdVar(Free(FreeVar { unique_id: UniqueId(_), pretty_name: Some(\"a\") })))], Scope { pattern: [Binder(FreeVar { unique_id: UniqueId(_), pretty_name: Some(\"a0\") }), Binder(FreeVar { unique_id: UniqueId(_), pretty_name: Some(\"a1\") }), Binder(FreeVar { unique_id: UniqueId(_), pretty_name: Some(\"a2\") })], body: PVar(OrdVar(Free(FreeVar { unique_id: UniqueId(_), pretty_name: Some(\"a\") }))) }), TaggedInputs([PVar(OrdVar(Free(FreeVar { unique_id: UniqueId(_), pretty_name: Some(\"a\") }))), PVar(OrdVar(Free(FreeVar { unique_id: UniqueId(_), pretty_name: Some(\"a\") })))], [NVar(OrdVar(Free(FreeVar { unique_id: UniqueId(_), pretty_name: Some(\"a\") }))), NVar(OrdVar(Free(FreeVar { unique_id: UniqueId(_), pretty_name: Some(\"a\") })))], Scope { pattern: [Binder(FreeVar { unique_id: UniqueId(_), pretty_name: Some(\"a0\") }), Binder(FreeVar { unique_id: UniqueId(_), pretty_name: Some(\"a1\") }), Binder(FreeVar { unique_id: UniqueId(_), pretty_name: Some(\"a2\") })], body: PVar(OrdVar(Free(FreeVar { unique_id: UniqueId(_), pretty_name: Some(\"a\") }))) })], [NQuote(PVar(OrdVar(Free(FreeVar { unique_id: UniqueId(_), pretty_name: Some(\"a\") })))), NQuote(PVar(OrdVar(Free(FreeVar { unique_id: UniqueId(_), pretty_name: Some(\"a\") }))))], Scope { pattern: [Binder(FreeVar { unique_id: UniqueId(_), pretty_name: Some(\"a0\") }), Binder(FreeVar { unique_id: UniqueId(_), pretty_name: Some(\"a1\") }), Binder(FreeVar { unique_id: UniqueId(_), pretty_name: Some(\"a2\") })], body: TaggedInputs([PVar(OrdVar(Free(FreeVar { unique_id: UniqueId(_), pretty_name: Some(\"a\") }))), PVar(OrdVar(Free(FreeVar { unique_id: UniqueId(_), pretty_name: Some(\"a\") })))], [NVar(OrdVar(Free(FreeVar { unique_id: UniqueId(_), pretty_name: Some(\"a\") }))), NVar(OrdVar(Free(FreeVar { unique_id: UniqueId(_), pretty_name: Some(\"a\") })))], Scope { pattern: [Binder(FreeVar { unique_id: UniqueId(_), pretty_name: Some(\"a0\") }), Binder(FreeVar { unique_id: UniqueId(_), pretty_name: Some(\"a1\") }), Binder(FreeVar { unique_id: UniqueId(_), pretty_name: Some(\"a2\") })], body: PVar(OrdVar(Free(FreeVar { unique_id: UniqueId(_), pretty_name: Some(\"a\") }))) }) }), TaggedInputs([TaggedInputs([PVar(OrdVar(Free(FreeVar { unique_id: UniqueId(_), pretty_name: Some(\"a\") }))), PVar(OrdVar(Free(FreeVar { unique_id: UniqueId(_), pretty_name: Some(\"a\") })))], [NVar(OrdVar(Free(FreeVar { unique_id: UniqueId(_), pretty_name: Some(\"a\") }))), NVar(OrdVar(Free(FreeVar { unique_id: UniqueId(_), pretty_name: Some(\"a\") })))], Scope { pattern: [Binder(FreeVar { unique_id: UniqueId(_), pretty_name: Some(\"a0\") }), Binder(FreeVar { unique_id: UniqueId(_), pretty_name: Some(\"a1\") }), Binder(FreeVar { unique_id: UniqueId(_), pretty_name: Some(\"a2\") })], body: PVar(OrdVar(Free(FreeVar { unique_id: UniqueId(_), pretty_name: Some(\"a\") }))) }), TaggedInputs([PVar(OrdVar(Free(FreeVar { unique_id: UniqueId(_), pretty_name: Some(\"a\") }))), PVar(OrdVar(Free(FreeVar { unique_id: UniqueId(_), pretty_name: Some(\"a\") })))], [NVar(OrdVar(Free(FreeVar { unique_id: UniqueId(_), pretty_name: Some(\"a\") }))), NVar(OrdVar(Free(FreeVar { unique_id: UniqueId(_), pretty_name: Some(\"a\") })))], Scope { pattern: [Binder(FreeVar { unique_id: UniqueId(_), pretty_name: Some(\"a0\") }), Binder(FreeVar { unique_id: UniqueId(_), pretty_name: Some(\"a1\") }), Binder(FreeVar { unique_id: UniqueId(_), pretty_name: Some(\"a2\") })], body: PVar(OrdVar(Free(FreeVar { unique_id: UniqueId(_), pretty_name: Some(\"a\") }))) })], [NQuote(PVar(OrdVar(Free(FreeVar { unique_id: UniqueId(_), pretty_name: Some(\"a\") })))), NQuote(PVar(OrdVar(Free(FreeVar { unique_id: UniqueId(_), pretty_name: Some(\"a\") }))))], Scope { pattern: [Binder(FreeVar { unique_id: UniqueId(_), pretty_name: Some(\"a0\") }), Binder(FreeVar { unique_id: UniqueId(_), pretty_name: Some(\"a1\") }), Binder(FreeVar { unique_id: UniqueId(_), pretty_name: Some(\"a2\") })], body: TaggedInputs([PVar(OrdVar(Free(FreeVar { unique_id: UniqueId(_), pretty_name: Some(\"a\") }))), PVar(OrdVar(Free(FreeVar { unique_id: UniqueId(_), pretty_name: Some(\"a\") })))], [NVar(OrdVar(Free(FreeVar { unique_id: UniqueId(_), pretty_name: Some(\"a\") }))), NVar(OrdVar(Free(FreeVar { unique_id: UniqueId(_), pretty_name: Some(\"a\") })))], Scope { pattern: [Binder(FreeVar { unique_id: UniqueId(_), pretty_name: Some(\"a0\") }), Binder(FreeVar { unique_id: UniqueId(_), pretty_name: Some(\"a1\") }), Binder(FreeVar { unique_id: UniqueId(_), pretty_name: Some(\"a2\") })], body: PVar(OrdVar(Free(FreeVar { unique_id: UniqueId(_), pretty_name: Some(\"a\") }))) }) })], [NQuote(TaggedInputs([PVar(OrdVar(Free(FreeVar { unique_id: UniqueId(_), pretty_name: Some(\"a\") }))), PVar(OrdVar(Free(FreeVar { unique_id: UniqueId(_), pretty_name: Some(\"a\") })))], [NVar(OrdVar(Free(FreeVar { unique_id: UniqueId(_), pretty_name: Some(\"a\") }))), NVar(OrdVar(Free(FreeVar { unique_id: UniqueId(_), pretty_name: Some(\"a\") })))], Scope { pattern: [Binder(FreeVar { unique_id: UniqueId(_), pretty_name: Some(\"a0\") }), Binder(FreeVar { unique_id: UniqueId(_), pretty_name: Some(\"a1\") }), Binder(FreeVar { unique_id: UniqueId(_), pretty_name: Some(\"a2\") })], body: PVar(OrdVar(Free(FreeVar { unique_id: UniqueId(_), pretty_name: Some(\"a\") }))) })), NQuote(TaggedInputs([PVar(OrdVar(Free(FreeVar { unique_id: UniqueId(_), pretty_name: Some(\"a\") }))), PVar(OrdVar(Free(FreeVar { unique_id: UniqueId(_), pretty_name: Some(\"a\") })))], [NVar(OrdVar(Free(FreeVar { unique_id: UniqueId(_), pretty_name: Some(\"a\") }))), NVar(OrdVar(Free(FreeVar { unique_id: UniqueId(_), pretty_name: Some(\"a\") })))], Scope { pattern: [Binder(FreeVar { unique_id: UniqueId(_), pretty_name: Some(\"a0\") }), Binder(FreeVar { unique_id: UniqueId(_), pretty_name: Some(\"a1\") }), Binder(FreeVar { unique_id: UniqueId(_), pretty_name: Some(\"a2\") })], body: PVar(OrdVar(Free(FreeVar { unique_id: UniqueId(_), pretty_name: Some(\"a\") }))) }))], Scope { pattern: [Binder(FreeVar { unique_id: UniqueId(_), pretty_name: Some(\"a0\") }), Binder(FreeVar { unique_id: UniqueId(_), pretty_name: Some(\"a1\") }), Binder(FreeVar { unique_id: UniqueId(_), pretty_name: Some(\"a2\") })], body: TaggedInputs([TaggedInputs([PVar(OrdVar(Free(FreeVar { unique_id: UniqueId(_), pretty_name: Some(\"a\") }))), PVar(OrdVar(Free(FreeVar { unique_id: UniqueId(_), pretty_name: Some(\"a\") })))], [NVar(OrdVar(Free(FreeVar { unique_id: UniqueId(_), pretty_name: Some(\"a\") }))), NVar(OrdVar(Free(FreeVar { unique_id: UniqueId(_), pretty_name: Some(\"a\") })))], Scope { pattern: [Binder(FreeVar { unique_id: UniqueId(_), pretty_name: Some(\"a0\") }), Binder(FreeVar { unique_id: UniqueId(_), pretty_name: Some(\"a1\") }), Binder(FreeVar { unique_id: UniqueId(_), pretty_name: Some(\"a2\") })], body: PVar(OrdVar(Free(FreeVar { unique_id: UniqueId(_), pretty_name: Some(\"a\") }))) }), TaggedInputs([PVar(OrdVar(Free(FreeVar { unique_id: UniqueId(_), pretty_name: Some(\"a\") }))), PVar(OrdVar(Free(FreeVar { unique_id: UniqueId(_), pretty_name: Some(\"a\") })))], [NVar(OrdVar(Free(FreeVar { unique_id: UniqueId(_), pretty_name: Some(\"a\") }))), NVar(OrdVar(Free(FreeVar { unique_id: UniqueId(_), pretty_name: Some(\"a\") })))], Scope { pattern: [Binder(FreeVar { unique_id: UniqueId(_), pretty_name: Some(\"a0\") }), Binder(FreeVar { unique_id: UniqueId(_), pretty_name: Some(\"a1\") }), Binder(FreeVar { unique_id: UniqueId(_), pretty_name: Some(\"a2\") })], body: PVar(OrdVar(Free(FreeVar { unique_id: UniqueId(_), pretty_name: Some(\"a\") }))) })], [NQuote(PVar(OrdVar(Free(FreeVar { unique_id: UniqueId(_), pretty_name: Some(\"a\") })))), NQuote(PVar(OrdVar(Free(FreeVar { unique_id: UniqueId(_), pretty_name: Some(\"a\") }))))], Scope { pattern: [Binder(FreeVar { unique_id: UniqueId(_), pretty_name: Some(\"a0\") }), Binder(FreeVar { unique_id: UniqueId(_), pretty_name: Some(\"a1\") }), Binder(FreeVar { unique_id: UniqueId(_), pretty_name: Some(\"a2\") })], body: TaggedInputs([PVar(OrdVar(Free(FreeVar { unique_id: UniqueId(_), pretty_name: Some(\"a\") }))), PVar(OrdVar(Free(FreeVar { unique_id: UniqueId(_), pretty_name: Some(\"a\") })))], [NVar(OrdVar(Free(FreeVar { unique_id: UniqueId(_), pretty_name: Some(\"a\") }))), NVar(OrdVar(Free(FreeVar { unique_id: UniqueId(_), pretty_name: Some(\"a\") })))], Scope { pattern: [Binder(FreeVar { unique_id: UniqueId(_), pretty_name: Some(\"a0\") }), Binder(FreeVar { unique_id: UniqueId(_), pretty_name: Some(\"a1\") }), Binder(FreeVar { unique_id: UniqueId(_), pretty_name: Some(\"a2\") })], body: PVar(OrdVar(Free(FreeVar { unique_id: UniqueId(_), pretty_name: Some(\"a\") }))) }) }) })";
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
