//! **Promoted counterexamples for `mixedmath`** — every seed its proptest corpus records,
//! as a named regression test.
//!
//! # Where these came from, and why they are here
//!
//! `languages/tests/gen_mixedmath_prop.proptest-regressions` holds 5 seed(s) for inputs
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
//!     target/generated/mixedmath/rust_ctor.rs \
//!     languages/tests/gen_mixedmath_prop.proptest-regressions
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
use mettail_languages::mixedmath::*;

/// Corpus entry 0 — seed `cc 55243275cb0735e73e5aac1dc35a6344001526af1fa8b51a26b6f6833124b4b1`.
///
/// Recorded counterexample, verbatim from the corpus:
/// ```text
/// term = Or(And(Not(BoolLit(false)), And(BoolLit(true), BoolLit(false))),
/// And(Not(BoolLit(false)), And(BoolLit(true), BoolLit(false))))
/// ```
#[test]
fn corpus_0_bool() {
    mettail_runtime::clear_var_cache();
    // 1 — the term CONSTRUCTS.
    let term: Bool = Bool::Or(std::sync::Arc::new(Bool::And(std::sync::Arc::new(Bool::Not(std::sync::Arc::new(Bool::BoolLit(false)))), std::sync::Arc::new(Bool::And(std::sync::Arc::new(Bool::BoolLit(true)), std::sync::Arc::new(Bool::BoolLit(false)))))), std::sync::Arc::new(Bool::And(std::sync::Arc::new(Bool::Not(std::sync::Arc::new(Bool::BoolLit(false)))), std::sync::Arc::new(Bool::And(std::sync::Arc::new(Bool::BoolLit(true)), std::sync::Arc::new(Bool::BoolLit(false)))))));

    // 2 — ANTI-VACUITY. The reconstructed term's normalised Debug must equal the
    //     text the corpus recorded, character for character. This is what makes
    //     "passes because it built the wrong term" impossible. Only
    //     `UniqueId(n)` and the ORDER of hash-container entries are quotiented
    //     out, and both are properties of the PROCESS rather than of the term:
    //     `UniqueId` comes from a global counter (and `FreeVar` equality is by
    //     unique_id alone, with the name fixing the identity through the var
    //     cache), and a `HashBag` is a multiset whose `PartialEq` ignores order.
    let recorded = "Or(And(Not(BoolLit(false)), And(BoolLit(true), BoolLit(false))), And(Not(BoolLit(false)), And(BoolLit(true), BoolLit(false))))";
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

/// Corpus entry 1 — seed `cc 7c310f4aea81c44ae1de305caa4d4952498c5b775d1a521902572e30a0f5341e`.
///
/// Recorded counterexample, verbatim from the corpus:
/// ```text
/// term = SubInt(AddInt(Neg(NumLit(2080078972)), AddInt(NumLit(75727876), NumLit(2080078972))),
/// AddInt(Neg(NumLit(2080078972)), AddInt(NumLit(75727876), NumLit(2080078972))))
/// ```
#[test]
fn corpus_1_int() {
    mettail_runtime::clear_var_cache();
    // 1 — the term CONSTRUCTS.
    let term: Int = Int::SubInt(std::sync::Arc::new(Int::AddInt(std::sync::Arc::new(Int::Neg(std::sync::Arc::new(Int::NumLit(2080078972i32)))), std::sync::Arc::new(Int::AddInt(std::sync::Arc::new(Int::NumLit(75727876i32)), std::sync::Arc::new(Int::NumLit(2080078972i32)))))), std::sync::Arc::new(Int::AddInt(std::sync::Arc::new(Int::Neg(std::sync::Arc::new(Int::NumLit(2080078972i32)))), std::sync::Arc::new(Int::AddInt(std::sync::Arc::new(Int::NumLit(75727876i32)), std::sync::Arc::new(Int::NumLit(2080078972i32)))))));

    // 2 — ANTI-VACUITY. The reconstructed term's normalised Debug must equal the
    //     text the corpus recorded, character for character. This is what makes
    //     "passes because it built the wrong term" impossible. Only
    //     `UniqueId(n)` and the ORDER of hash-container entries are quotiented
    //     out, and both are properties of the PROCESS rather than of the term:
    //     `UniqueId` comes from a global counter (and `FreeVar` equality is by
    //     unique_id alone, with the name fixing the identity through the var
    //     cache), and a `HashBag` is a multiset whose `PartialEq` ignores order.
    let recorded = "SubInt(AddInt(Neg(NumLit(2080078972)), AddInt(NumLit(75727876), NumLit(2080078972))), AddInt(Neg(NumLit(2080078972)), AddInt(NumLit(75727876), NumLit(2080078972))))";
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

/// Corpus entry 2 — seed `cc d3275d6953e2fb4f4ede533e4a612cacca453e19134401bf79e3984632118db9`.
///
/// Recorded counterexample, verbatim from the corpus:
/// ```text
/// term = Not(BoolLit(true))
/// ```
#[test]
fn corpus_2_bool() {
    mettail_runtime::clear_var_cache();
    // 1 — the term CONSTRUCTS.
    let term: Bool = Bool::Not(std::sync::Arc::new(Bool::BoolLit(true)));

    // 2 — ANTI-VACUITY. The reconstructed term's normalised Debug must equal the
    //     text the corpus recorded, character for character. This is what makes
    //     "passes because it built the wrong term" impossible. Only
    //     `UniqueId(n)` and the ORDER of hash-container entries are quotiented
    //     out, and both are properties of the PROCESS rather than of the term:
    //     `UniqueId` comes from a global counter (and `FreeVar` equality is by
    //     unique_id alone, with the name fixing the identity through the var
    //     cache), and a `HashBag` is a multiset whose `PartialEq` ignores order.
    let recorded = "Not(BoolLit(true))";
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

/// Corpus entry 3 — seed `cc 79ffe0cbd6058576ad3de297479bec321f14c2f15569c8853c7eea1d92d4d03d`.
///
/// Recorded counterexample, verbatim from the corpus:
/// ```text
/// term = Neg(NumLit(1280068684))
/// ```
#[test]
fn corpus_3_int() {
    mettail_runtime::clear_var_cache();
    // 1 — the term CONSTRUCTS.
    let term: Int = Int::Neg(std::sync::Arc::new(Int::NumLit(1280068684i32)));

    // 2 — ANTI-VACUITY. The reconstructed term's normalised Debug must equal the
    //     text the corpus recorded, character for character. This is what makes
    //     "passes because it built the wrong term" impossible. Only
    //     `UniqueId(n)` and the ORDER of hash-container entries are quotiented
    //     out, and both are properties of the PROCESS rather than of the term:
    //     `UniqueId` comes from a global counter (and `FreeVar` equality is by
    //     unique_id alone, with the name fixing the identity through the var
    //     cache), and a `HashBag` is a multiset whose `PartialEq` ignores order.
    let recorded = "Neg(NumLit(1280068684))";
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

/// Corpus entry 4 — seed `cc c241cec83bfc578f43c5ea1d35f50110ca4ee8a8f2985d6d2adae01062a096b1`.
///
/// Recorded counterexample, verbatim from the corpus:
/// ```text
/// term = BoolToInt(Or(And(BoolLit(true), BoolLit(false)), And(BoolLit(true), BoolLit(false))))
/// ```
#[test]
fn corpus_4_int() {
    mettail_runtime::clear_var_cache();
    // 1 — the term CONSTRUCTS.
    let term: Int = Int::BoolToInt(std::sync::Arc::new(Bool::Or(std::sync::Arc::new(Bool::And(std::sync::Arc::new(Bool::BoolLit(true)), std::sync::Arc::new(Bool::BoolLit(false)))), std::sync::Arc::new(Bool::And(std::sync::Arc::new(Bool::BoolLit(true)), std::sync::Arc::new(Bool::BoolLit(false)))))));

    // 2 — ANTI-VACUITY. The reconstructed term's normalised Debug must equal the
    //     text the corpus recorded, character for character. This is what makes
    //     "passes because it built the wrong term" impossible. Only
    //     `UniqueId(n)` and the ORDER of hash-container entries are quotiented
    //     out, and both are properties of the PROCESS rather than of the term:
    //     `UniqueId` comes from a global counter (and `FreeVar` equality is by
    //     unique_id alone, with the name fixing the identity through the var
    //     cache), and a `HashBag` is a multiset whose `PartialEq` ignores order.
    let recorded = "BoolToInt(Or(And(BoolLit(true), BoolLit(false)), And(BoolLit(true), BoolLit(false))))";
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
