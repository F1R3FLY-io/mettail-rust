//! GSLT omnibus conformance suite for **L2 `Monoid`** — the hand-written gate on
//! the production spec `languages/src/monoid.rs` (`omnibus.tex:430-449`), rung
//! two (types + terms + **equations**; `rewrites { }` is empty).
//!
//! The spec's own module header carries the clause-by-clause containment table
//! and the notation notes; this file carries the behaviour those clauses claim.
//!
//! The omnibus makes this rung load-bearing (:451-457): *"The equational theory
//! of a single operator … determines whether proximity to a resource confers
//! authority over it … Equations are not decoration."* The tests below therefore
//! do not merely check that the equations are *recorded* — they check that the
//! quotient they present is *computed*: `e * x` and `x * e` are identified with
//! `x`, and the two bracketings of a triple are identified with each other, by
//! the Dovetail e-graph saturation the macro generates from `equations {}`.
#![cfg(feature = "monoid")]

use mettail_languages::monoid::*;
use mettail_runtime::Language;

/// Iteration / node budget for the e-graph saturation used by the quotient
/// tests. Small on purpose: a monoid presentation must converge quickly, and a
/// bounded budget means a divergence would surface as a limit error, never as a
/// hung test binary.
const MAX_ITERS: usize = 32;
const MAX_NODES: usize = 100_000;

/// The three equations lower to SIX Dovetail rules — each equation becomes a
/// bidirectional pair `<Lang>::equation::<Name>::{forward,reverse}`
/// (`macros/src/gen/runtime/dovetail_report.rs:1331, 1351`).
fn equation_label(name: &str, direction: &str) -> String {
    format!("Monoid::equation::{name}::{direction}")
}

/// Saturate `src` in the Dovetail e-graph and return the labels of every rule
/// that fired, together with a rendering of the report for failure messages.
fn firings(src: &str) -> (Vec<String>, String) {
    let lang = MonoidLanguage;
    mettail_runtime::clear_var_cache();
    let term = lang
        .parse_term(src)
        .unwrap_or_else(|e| panic!("parse {src:?} failed: {e}"));
    let report = MonoidLanguage::dovetail_report_for(term.as_ref(), MAX_ITERS, MAX_NODES)
        .unwrap_or_else(|e| panic!("dovetail_report_for({src:?}) returned Err: {e}"));
    let labels: Vec<String> = report
        .rule_firings
        .iter()
        .filter_map(|f| f.label.clone())
        .collect();
    let rendered = format!(
        "complete={} roots={} firings={:?} terms={:?}",
        report.is_complete(),
        report.roots.len(),
        report.rule_firings,
        report
            .terms
            .iter()
            .map(|t| (t.op_display.clone(), t.source_display.clone(), t.is_root))
            .collect::<Vec<_>>()
    );
    (labels, rendered)
}

// ═══════════════════════════════════════════════════════════════════════════
// Conformance tests
// ═══════════════════════════════════════════════════════════════════════════

#[test]
fn monoid_language_resolves() {
    let lang = MonoidLanguage;
    assert_eq!(lang.name(), "Monoid");
}

/// Clause coverage: both term formers and all three equations are in metadata,
/// and (rung two) there are no rewrites.
#[test]
fn monoid_metadata_carries_every_doc_clause() {
    let lang = MonoidLanguage;
    let meta = lang.metadata();
    let names: Vec<&str> = meta.terms().iter().map(|t| t.name).collect();
    for clause in ["Unit", "Mul"] {
        assert!(names.contains(&clause), "omnibus clause {clause} missing; have {names:?}");
    }
    assert_eq!(
        meta.equations().len(),
        3,
        "the omnibus presents exactly three equations (Assoc, UnitL, UnitR); got {:?}",
        meta.equations()
            .iter()
            .map(|e| (e.lhs, e.rhs))
            .collect::<Vec<_>>()
    );
    assert!(meta.rewrites().is_empty(), "Monoid is rung two — `rewrites {{ }}` is empty");
}

/// `Unit` (:437) and `Mul` (:438) — the free-algebra surface parses and prints.
#[test]
fn monoid_terms_parse_and_round_trip() {
    mettail_runtime::clear_var_cache();
    for src in ["e", "e * e", "x * y", "x * y * z", "e * x * e"] {
        let t = M::parse(src).unwrap_or_else(|e| panic!("parse {src:?} failed: {e:?}"));
        let printed = format!("{t}");
        let reparsed = M::parse(&printed)
            .unwrap_or_else(|e| panic!("re-parse of display {printed:?} failed: {e:?}"));
        assert_eq!(reparsed, t, "display round-trip must be identity for {src:?}");
    }
}

/// `UnitL` (:443) — `e * x = x` is *computed*, not merely declared: the
/// left-unit equation FIRES in the e-graph, putting `e * x` and `x` in one
/// e-class.
#[test]
fn monoid_unit_left_is_quotiented() {
    let (labels, rendered) = firings("e * x");
    assert!(
        labels.contains(&equation_label("UnitL", "forward")),
        "UnitL must fire on `e * x` — it is what identifies it with `x`; report: {rendered}"
    );
}

/// `UnitR` (:444) — `x * e = x`.
#[test]
fn monoid_unit_right_is_quotiented() {
    let (labels, rendered) = firings("x * e");
    assert!(
        labels.contains(&equation_label("UnitR", "forward")),
        "UnitR must fire on `x * e`; report: {rendered}"
    );
}

/// `Assoc` (:442) — the two bracketings of a triple are identified. This is the
/// clause the omnibus calls out as the one that "determines whether proximity to
/// a resource confers authority over it".
#[test]
fn monoid_associativity_fires() {
    let (labels, rendered) = firings("(x * y) * z");
    assert!(
        labels
            .iter()
            .any(|l| l.starts_with("Monoid::equation::Assoc::")),
        "Assoc must fire on `(x * y) * z`, identifying it with `x * (y * z)`; report: {rendered}"
    );
}

/// The saturation converges: a monoid presentation over a bounded budget
/// reaches a COMPLETE report (not a cycle-cut / limit), for both a unit-bearing
/// and a purely associative term.
#[test]
fn monoid_saturation_is_complete() {
    for src in ["e * x", "x * e", "e * e", "(x * y) * z", "e * x * e"] {
        let lang = MonoidLanguage;
        mettail_runtime::clear_var_cache();
        let term = lang
            .parse_term(src)
            .unwrap_or_else(|e| panic!("parse {src:?}: {e}"));
        let report = MonoidLanguage::dovetail_report_for(term.as_ref(), MAX_ITERS, MAX_NODES)
            .unwrap_or_else(|e| panic!("dovetail_report_for({src:?}) returned Err: {e}"));
        assert!(!report.roots.is_empty(), "the report for {src:?} must carry at least one root");
        assert!(
            report.is_complete(),
            "the monoid presentation must saturate COMPLETELY for {src:?}; got {:?}",
            report.completeness
        );
    }
}
