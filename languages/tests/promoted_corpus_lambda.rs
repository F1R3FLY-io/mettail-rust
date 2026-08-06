//! **Promoted counterexamples for `lambda`** — every seed its proptest corpus records,
//! as a named regression test.
//!
//! # Where these came from, and why they are here
//!
//! `languages/tests/gen_lambda_prop.proptest-regressions` holds 1 seed(s) for inputs
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
//!     target/generated/lambda/rust_ctor.rs \
//!     languages/tests/gen_lambda_prop.proptest-regressions
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

use mettail_languages::lambda::*;
use mettail_testkit::ctor::canonicalize_debug;

/// Corpus entry 0 — seed `cc 26e407afd81f0052b974f06ea693f77b40edaa0c3e76df80010c4706fb32b5cb`.
///
/// Recorded counterexample, verbatim from the corpus:
/// ```text
/// term = Lam(Scope { pattern: Binder(FreeVar { unique_id: UniqueId(82), pretty_name:
/// Some("a6") }), body: TVar(OrdVar(Free(FreeVar { unique_id: UniqueId(79), pretty_name:
/// Some("a") }))) })
/// ```
#[test]
fn corpus_0_term() {
    mettail_runtime::clear_var_cache();
    // 1 — the term CONSTRUCTS.
    let term: Term = Term::Lam(mettail_runtime::Scope::from_parts_unsafe(
        mettail_runtime::Binder(mettail_runtime::get_or_create_var("a6")),
        std::sync::Arc::new(Term::TVar(mettail_runtime::OrdVar(mettail_runtime::Var::Free(
            mettail_runtime::get_or_create_var("a"),
        )))),
    ));

    // 2 — ANTI-VACUITY. The reconstructed term's normalised Debug must equal the
    //     text the corpus recorded, character for character. This is what makes
    //     "passes because it built the wrong term" impossible. Only
    //     `UniqueId(n)` and the ORDER of hash-container entries are quotiented
    //     out, and both are properties of the PROCESS rather than of the term:
    //     `UniqueId` comes from a global counter (and `FreeVar` equality is by
    //     unique_id alone, with the name fixing the identity through the var
    //     cache), and a `HashBag` is a multiset whose `PartialEq` ignores order.
    let recorded = "Lam(Scope { pattern: Binder(FreeVar { unique_id: UniqueId(_), pretty_name: Some(\"a6\") }), body: TVar(OrdVar(Free(FreeVar { unique_id: UniqueId(_), pretty_name: Some(\"a\") }))) })";
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
