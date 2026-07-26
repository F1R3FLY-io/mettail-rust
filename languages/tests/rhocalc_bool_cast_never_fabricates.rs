//! **`bool(s)` must ERROR on an unparseable string, never answer the value `false`.**
//!
//! # The defect
//!
//! The `ToBool` fold's string arm read `s.parse::<bool>().unwrap_or(false)`. Rust's
//! `FromStr for bool` accepts exactly two spellings, `"true"` and `"false"`, so every other
//! string — `"True"`, `"1"`, `"yes"`, `""` — folded to the **value** `false`.
//!
//! # Why the obvious test cannot see it
//!
//! Checking only the final value cannot distinguish *"the operator errored"* from
//! *"the operator answered false"*: both look like "not true" at every consumer, and f1r3node's
//! own `guard_passes` collapses error, non-boolean and `false` into a single "do not commit".
//! That collapse is exactly what let the fabrication survive. So each assertion below tests the
//! **discriminated** outcome — `Proc::Err` versus `CastBool(BoolLit(false))` — and a control row
//! pins the genuine `"false"` string as still answering `false`, so the two are demonstrably
//! distinguishable rather than merely differently spelled.
//!
//! # Why it is worse than a typical fabrication
//!
//! `bool(...)` feeds the GUARD lane. A `where bool(s)` clause is a semantic predicate, and a
//! fabricated `false` there is a fabricated **guard verdict** — it decides that a COMM does not
//! fire, on no evidence.
//!
//! The governing convention is `languages/src/rhocalc/runtime.rs`'s: *"A failed operator must
//! never invent a value — hence `Proc::Err`, never a fabricated `BoolLit`."* Every sibling arm
//! of the same `match` already obeyed it.

#![cfg(feature = "rhocalc")]

use std::sync::Arc;

use mettail_languages::rhocalc::*;

const DOVETAIL_ITERS: usize = 256;
const DOVETAIL_NODES: usize = 4_000_000;

fn to_term(p: &Proc) -> RhoCalcTerm {
    RhoCalcTerm(RhoCalcTermInner::Proc(p.clone()))
}

fn proc_from_term(term: &dyn mettail_runtime::Term) -> Option<Proc> {
    term.as_any().downcast_ref::<RhoCalcTerm>().and_then(|t| match &t.0 {
        RhoCalcTermInner::Proc(p) => Some(p.clone()),
        _ => None,
    })
}

/// Normalize `bool(<literal>)` through the real Dovetail fold engine.
fn fold_bool_of_string(s: &str) -> Option<Proc> {
    let literal = Proc::CastStr(Arc::new(Str::StringLit(s.to_string())));
    let call = Proc::ToBool(Arc::new(literal));
    let term = to_term(&call);
    match RhoCalcLanguage::dovetail_normal_term(&term, DOVETAIL_ITERS, DOVETAIL_NODES) {
        Ok(nf) => proc_from_term(nf.as_ref()),
        Err(_) => None,
    }
}

/// The three outcomes, DISCRIMINATED — which is the whole point of this file.
#[derive(Debug, PartialEq, Eq)]
enum Outcome {
    /// The fold answered the boolean value `b`.
    Answered(bool),
    /// The fold answered `Proc::Err` — it declined to invent a value.
    Errored,
    /// The fold did not reduce, or reduced to something else entirely.
    Other(String),
}

fn outcome(s: &str) -> Outcome {
    match fold_bool_of_string(s) {
        Some(Proc::CastBool(ref b)) => match b.as_ref() {
            Bool::BoolLit(v) => Outcome::Answered(*v),
            other => Outcome::Other(format!("{other:?}")),
        },
        Some(Proc::Err) => Outcome::Errored,
        Some(ref other) => Outcome::Other(format!("{other}")),
        None => Outcome::Other("dovetail declined to normalize".to_string()),
    }
}

/// ★ THE REGRESSION. Every string Rust's `FromStr for bool` rejects must ERROR.
#[test]
fn an_unparseable_string_errors_rather_than_answering_false() {
    for spelling in ["True", "FALSE", "1", "0", "yes", "no", "", " true", "true "] {
        assert_eq!(
            outcome(spelling),
            Outcome::Errored,
            "bool({spelling:?}) must be Proc::Err — answering the VALUE `false` fabricates a \
             verdict, and in a `where` clause that verdict decides whether a COMM fires"
        );
    }
}

/// The control: the two spellings that ARE booleans still answer, so the assertion above is a
/// statement about unparseable strings and not about `bool(...)` being broken outright.
#[test]
fn the_two_real_spellings_still_answer() {
    assert_eq!(outcome("true"), Outcome::Answered(true));
    assert_eq!(outcome("false"), Outcome::Answered(false));
}

/// The discrimination itself: `bool("false")` and `bool("yes")` must be DIFFERENT outcomes.
/// If a future edit reintroduces `unwrap_or(false)` they collapse into one, and this fails even
/// if someone weakens the row-by-row assertions above.
#[test]
fn errored_and_answered_false_are_distinguishable_outcomes() {
    let genuine_false = outcome("false");
    let unparseable = outcome("yes");
    assert_ne!(
        genuine_false, unparseable,
        "a fabricated `false` is indistinguishable from a real one at every consumer — that \
         indistinguishability IS the defect, so the two outcomes must differ here"
    );
    assert_eq!(genuine_false, Outcome::Answered(false));
    assert_eq!(unparseable, Outcome::Errored);
}

/// The sibling arms already obeyed the convention; pin that they still do, so the fix is
/// consistent with the rule rather than a local patch.
#[test]
fn the_numeric_arms_answer_and_the_non_literal_arms_error() {
    let int_call = Proc::ToBool(Arc::new(Proc::CastInt(Arc::new(Int::NumLit(0)))));
    let term = to_term(&int_call);
    let normalized = RhoCalcLanguage::dovetail_normal_term(&term, DOVETAIL_ITERS, DOVETAIL_NODES)
        .ok()
        .and_then(|nf| proc_from_term(nf.as_ref()));
    assert!(
        matches!(normalized, Some(Proc::CastBool(ref b)) if matches!(b.as_ref(), Bool::BoolLit(false))),
        "bool(0) answers `false` from a REAL numeric fact, not from a parse failure; got {normalized:?}"
    );

    // A process operand is not convertible at all — the `_` arm, which already answered `Err`.
    let process_call = Proc::ToBool(Arc::new(Proc::PZero));
    let term = to_term(&process_call);
    let normalized = RhoCalcLanguage::dovetail_normal_term(&term, DOVETAIL_ITERS, DOVETAIL_NODES)
        .ok()
        .and_then(|nf| proc_from_term(nf.as_ref()));
    assert!(
        matches!(normalized, Some(Proc::Err)),
        "bool(Nil) must error; got {normalized:?}"
    );
}
