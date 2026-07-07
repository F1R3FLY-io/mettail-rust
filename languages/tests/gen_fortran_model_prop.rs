//! Durable dual-mode test matrix — PART B: keyword reservation OPT-OUT
//! (`FortranModel`, `options { reserved_keywords: none }`).
//!
//! This is a HAND-WRITTEN, committed anti-regression suite (NOT auto-generated;
//! `FortranModel` sets `emit_tests: false` precisely so the `language!` macro
//! does not clobber this file). It proves that a language which opts OUT of
//! keyword reservation retains FULL AMBIGUITY: a keyword-shaped literal
//! terminal (`IF`) in channel/identifier position still yields BOTH the keyword
//! reading and the variable reading — Fortran's no-reserved-words property.
//!
//! The send pair `SendKw`/`SendVar` mirrors RhoCalc's `POutputNil`
//! (`@ Nil ! (q)`, literal keyword channel) vs `POutputQuoted`
//! (`@ n:Name ! (q)`, variable channel): `@Nil!(q)` forks between the keyword
//! `Nil` and a variable named `Nil`. Under RhoCalc's `reserved_keywords: auto`
//! that fork collapses to one reading; here, under `none`, it is retained
//! (empirically verified: `@IF!(x)` → 2 readings).
//!
//! Companion: `keyword_reservation_tests.rs` (RhoCalc, reservation ON).

#![allow(clippy::bool_assert_comparison)]

use mettail_languages::fortran_model::*;

/// The readings of `@<chan>!(x)` as a `Stmt`.
fn send_readings(chan: &str) -> Vec<Stmt> {
    let src = format!("@{chan}!(x)");
    Stmt::parse_via_wpda_all(&src)
        .unwrap_or_else(|e| panic!("FortranModel: `{src}` should parse as Stmt: {e:?}"))
}

/// B.1 — contextual_keyword_both_readings.
///
/// With reservation OFF, the keyword-shaped token `IF` in the channel position
/// of `@IF!(x)` yields BOTH readings: the LITERAL keyword send `SendKw` AND the
/// VARIABLE-channel send `SendVar(TVar("IF"), …)`. This is the load-bearing
/// full-ambiguity guarantee for Fortran-style languages.
#[test]
fn contextual_keyword_both_readings() {
    let readings = send_readings("IF");
    let has_keyword = readings.iter().any(|s| matches!(s, Stmt::SendKw(_)));
    let has_variable = readings.iter().any(|s| match s {
        Stmt::SendVar(chan, _) => matches!(chan.as_ref(), Term::TVar(_)),
        _ => false,
    });

    assert!(
        has_keyword,
        "OPT-OUT: `@IF!(x)` must retain the KEYWORD reading SendKw; got {readings:?}"
    );
    assert!(
        has_variable,
        "OPT-OUT: `@IF!(x)` must ALSO retain the VARIABLE-channel reading \
         SendVar(TVar(\"IF\"), …) because reservation is `none`; got {readings:?}"
    );
    assert!(
        readings.len() >= 2,
        "OPT-OUT: `@IF!(x)` must have >= 2 readings (keyword + variable); got {}: {readings:?}",
        readings.len()
    );
}

/// B.2 — fortran_do_archetype.
///
/// The canonical Fortran ambiguity: `DO(10, I) = 1 , 5` (a loop, two integer
/// bounds separated by a comma) and `DO(10, I) = 1.5` (an assignment with a
/// real right-hand side) BOTH parse. The DECISIVE part — a top-level comma vs.
/// a decimal point flipping loop ↔ assignment — is verbatim; the parentheses
/// are this WPDA's prefix-keyword-then-punctuation analog of fixed-form
/// `DO 10 I = …`.
#[test]
fn fortran_do_archetype() {
    // Loop form — comma → two integer bounds.
    let loop_form = Stmt::parse_via_wpda_all("DO(10, I) = 1 , 5")
        .expect("FortranModel: `DO(10, I) = 1 , 5` (loop) should parse");
    assert!(
        loop_form.iter().any(|s| matches!(s, Stmt::DoLoop(..))),
        "archetype: `DO(10, I) = 1 , 5` should have a DoLoop reading; got {loop_form:?}"
    );

    // Assignment form — real (decimal) right-hand side.
    let assign_form = Stmt::parse_via_wpda_all("DO(10, I) = 1.5")
        .expect("FortranModel: `DO(10, I) = 1.5` (assignment) should parse");
    assert!(
        assign_form.iter().any(|s| matches!(s, Stmt::DoAssign(..))),
        "archetype: `DO(10, I) = 1.5` should have a DoAssign reading; got {assign_form:?}"
    );
}

/// B.3 — ambiguity_set_materialized.
///
/// `parse_via_wpda_all` (the multi-result driver) MATERIALIZES the full
/// ambiguity set, not just the shortest-path winner. For `@IF!(x)` the set is
/// exactly the keyword send and the variable send.
#[test]
fn ambiguity_set_materialized() {
    let readings = send_readings("IF");
    let kw = readings.iter().filter(|s| matches!(s, Stmt::SendKw(_))).count();
    let var = readings
        .iter()
        .filter(|s| matches!(s, Stmt::SendVar(chan, _) if matches!(chan.as_ref(), Term::TVar(_))))
        .count();
    assert_eq!(kw, 1, "exactly one keyword send of `@IF!(x)`; got {readings:?}");
    assert_eq!(var, 1, "exactly one variable send of `@IF!(x)`; got {readings:?}");
    // The full set is precisely {SendVar(TVar), SendKw} — no spurious extras.
    assert_eq!(
        readings.len(),
        2,
        "the materialized ambiguity set for `@IF!(x)` is exactly \
         {{SendVar(TVar), SendKw}}; got {readings:?}"
    );
}

/// B.4 — optout_language_does_not_reserve.
///
/// Observable proxy for "the reserved set is empty": a keyword-shaped terminal
/// remains usable as an identifier, so `IF = 1.5` assigns to a *variable* named
/// `IF`. Under reservation this reading would be removed.
#[test]
fn optout_language_does_not_reserve() {
    let readings = Stmt::parse_via_wpda_all("IF = 1.5")
        .expect("FortranModel: `IF = 1.5` should parse (IF as a variable)");
    let assign_with_var = readings.iter().any(|s| match s {
        Stmt::Assign(lhs, _) => matches!(lhs.as_ref(), Term::TVar(_)),
        _ => false,
    });
    assert!(
        assign_with_var,
        "OPT-OUT: `IF = 1.5` must parse as an assignment whose LHS is the \
         variable `IF` (Term::TVar) — proving `IF` is NOT reserved; got {readings:?}"
    );

    // And the keyword-shaped token in the channel position of a send admits a
    // variable reading (the same no-reserved-words property, cross-checked).
    assert!(
        send_readings("IF")
            .iter()
            .any(|s| matches!(s, Stmt::SendVar(chan, _) if matches!(chan.as_ref(), Term::TVar(_)))),
        "OPT-OUT: `@IF!(x)` must admit a variable-channel reading"
    );
}
