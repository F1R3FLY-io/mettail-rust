//! Does the fixed-point scale-dedup exposure reach the CONSENSUS language?
//!
//! `languages/tests/fixedpoint_scale_dedup_ab.rs` witnesses the exposure in `calculator`, where
//! `DivFixed` is a `Fixed`-category `fold` rule. Rholang sites division at `Proc`
//! (`languages/src/rholang.rs:2075`, `Div . a:Proc, b:Proc |- a "/" b : Proc ![…] fold same`),
//! whose fixed arm calls `CanonicalFixedPoint::checked_div`. Because it is a `fold` rule it runs
//! on the same typed-Dovetail path, and `RholangDovetailOp::Fixed_FixedLit(CanonicalFixedPoint)`
//! is generated with the same `#[derive(Clone, PartialEq, Eq, Hash)]` — so the same hashcons
//! collapse (`dovetail/src/egraph.rs:292`) should apply.
//!
//! "Should" is not evidence. This file MEASURES it, because whether the exposure reaches the
//! consensus lane or stops at a demo language is the difference between a consensus-visible
//! defect and a mechanism-only one.
#![cfg(all(feature = "rholang", feature = "dovetail-codegen"))]

use mettail_languages::rholang::RholangLanguage;
use mettail_runtime::Language;

const MAX_ITERS: usize = 64;
const MAX_NODES: usize = 200_000;

fn normal_form(src: &str) -> Result<String, String> {
    mettail_runtime::clear_var_cache();
    let lang = RholangLanguage;
    let term = lang.parse_term(src).map_err(|e| format!("parse error: {e}"))?;
    let normal = RholangLanguage::dovetail_normal_term(term.as_ref(), MAX_ITERS, MAX_NODES)
        .map_err(|e| format!("dovetail_normal_term error: {e}"))?;
    Ok(format!("{normal}"))
}

/// Same five programs as the calculator A/B. The carrier `(x - x) - (y - y)` is rationally
/// `0p0`, and `0p0 + q` re-aligns to `q.places`, so the observable is exactly the quotient.
const P0: &str = "7.00p2 / 3.00p2";
const P0_SAME_SCALE: &str = "((7.00p2 - 7.00p2) - (3.00p2 - 3.00p2)) + (7.00p2 / 3.00p2)";
const P1_LOWER_SCALE_FIRST: &str = "((7.0p1 - 7.0p1) - (3.0p1 - 3.0p1)) + (7.00p2 / 3.00p2)";
const P2_LOWER_SCALE_LAST: &str = "(7.00p2 / 3.00p2) + ((7.0p1 - 7.0p1) - (3.0p1 - 3.0p1))";
const P3_DIFFERENT_VALUE: &str = "((5.0p1 - 5.0p1) - (2.0p1 - 2.0p1)) + (7.00p2 / 3.00p2)";

/// The Q-carriers, mirroring `fixedpoint_scale_dedup_ab.rs`: every binary operation has
/// equal-scale operands, so they survive a future scale-equality precondition (work item #186)
/// instead of turning this gate vacuously green. ⚠ BOTH divide operands need a lower-scale
/// sibling — a carrier supplying only one does not reproduce the defect at all (measured).
const Q0_SAME_SCALE: &str = "fixed((7.00p2 - 3.00p2), 2) + (7.00p2 / 3.00p2)";
const Q1_LOWER_SCALE_FIRST: &str = "fixed((7.0p1 - 3.0p1), 2) + (7.00p2 / 3.00p2)";
const Q2_LOWER_SCALE_LAST: &str = "(7.00p2 / 3.00p2) + fixed((7.0p1 - 3.0p1), 2)";
const Q3_DIFFERENT_VALUE: &str = "fixed((5.0p1 - 1.0p1), 2) + (7.00p2 / 3.00p2)";

/// Diagnostic: the whole A/B table for rholang in one run.
#[test]
fn rholang_ab_table_diagnostic() {
    let rows = [
        ("P0  baseline           ", P0),
        ("P0' same-scale sibling ", P0_SAME_SCALE),
        ("P1  lower-scale FIRST  ", P1_LOWER_SCALE_FIRST),
        ("P2  lower-scale LAST   ", P2_LOWER_SCALE_LAST),
        ("P3  different value    ", P3_DIFFERENT_VALUE),
        ("Q0  same-scale rescale ", Q0_SAME_SCALE),
        ("Q1  lower-scale FIRST  ", Q1_LOWER_SCALE_FIRST),
        ("Q2  lower-scale LAST   ", Q2_LOWER_SCALE_LAST),
        ("Q3  different value    ", Q3_DIFFERENT_VALUE),
    ];
    let mut report = String::new();
    for (name, src) in rows {
        let outcome = match normal_form(src) {
            Ok(nf) => nf,
            Err(e) => format!("<{e}>"),
        };
        report.push_str(&format!("{name} {src:<62} => {outcome}\n"));
    }
    eprintln!("\n=== rholang fixed-point scale dedup A/B ===\n{report}");
    assert!(
        normal_form(P0).is_ok(),
        "the rholang BASELINE must at least evaluate, else the instrument is broken:\n{report}"
    );
}

/// ★★ THE INVARIANT, IN THE CONSENSUS LANE — turned live 2026-07-30 by work item #200.
///
/// This replaces the two defect witnesses that stood here. Both were GREEN because the product
/// was wrong, and the consensus lane is where that mattered: two syntactically distinct but
/// semantically identical deploys disagreed with EACH OTHER on the same node, so the answer was
/// a function of the source text rather than of the term.
///
/// # ⚠ What it replaces — the retired witnesses, verbatim
///
/// `rholang_witness_equal_value_sibling_changes_the_quotient` asserted:
///
/// ```text
/// assert_eq!(p0,      "2.33p2", "baseline");
/// assert_eq!(p0_same, "2.33p2", "control (a-size): SAME-scale sibling must not move it");
/// assert_eq!(p3,      "2.33p2", "control (b-negative): DIFFERENT-VALUE sibling must not move it");
/// assert_eq!(p1,      "2.3p1",  "⚠ WITNESS in the consensus language: an equal-value
///                                lower-scale sibling changes the quotient computed by
///                                rholang's `Div` fold");
/// assert_ne!(p0, p1,            "⚠ 233/100 != 23/10 — a genuine value difference");
/// ```
///
/// `rholang_witness_the_quotient_depends_on_textual_order` asserted:
///
/// ```text
/// assert_eq!(p1, "2.3p1",  "siblings FIRST => the p1 representative survives");
/// assert_eq!(p2, "2.33p2", "siblings LAST => the p2 representative survives");
/// assert_ne!(p1, p2,       "⚠ WITNESS: two rholang programs differing ONLY in the order of two
///                           summands compute different quotients");
/// ```
#[test]
fn rholang_answer_must_not_depend_on_an_equal_value_sibling() {
    let p0 = normal_form(P0).expect("P0");
    let p0_same = normal_form(P0_SAME_SCALE).expect("P0'");
    let p1 = normal_form(P1_LOWER_SCALE_FIRST).expect("P1");
    let p2 = normal_form(P2_LOWER_SCALE_LAST).expect("P2");
    let p3 = normal_form(P3_DIFFERENT_VALUE).expect("P3");

    assert_eq!(p0, "2.33p2", "the baseline is unmoved");
    assert_eq!(
        p1, p0,
        "★ THE FIX, in the consensus lane: an equal-value lower-scale sibling no longer changes \
         the quotient computed by rholang's `Div` fold. This answered `2.3p1` before #200",
    );
    assert_eq!(
        p2, p1,
        "★ …nor does the ORDER. Two rholang programs differing only in the order of two \
         summands answered `2.3p1` and `2.33p2` before #200",
    );
    assert_eq!(p0_same, p0, "control (a-size): a SAME-scale sibling never moved it");
    assert_eq!(p3, p0, "control (b-negative): a DIFFERENT-VALUE sibling never moved it");
}

/// ★★ The same invariant on the precondition-safe Q-carriers. See the Q-constants' doc.
#[test]
fn rholang_answer_must_not_depend_on_an_equal_value_sibling_q_carriers() {
    let q0 = normal_form(Q0_SAME_SCALE).expect("Q0");
    let q1 = normal_form(Q1_LOWER_SCALE_FIRST).expect("Q1");
    let q2 = normal_form(Q2_LOWER_SCALE_LAST).expect("Q2");
    let q3 = normal_form(Q3_DIFFERENT_VALUE).expect("Q3");

    assert_eq!(q0, "6.33p2", "control: 4.00p2 + 2.33p2");
    assert_eq!(q1, q0, "★ THE FIX: `6.3p1` before #200 — measured, not assumed");
    assert_eq!(q2, q1, "★ …and order-independent");
    assert_eq!(q3, q0, "control (b-negative)");
}

/// ★★ `fixed(x, w)` — rholang's only scale-repair operator — was a NO-OP for every
/// value-preserving width, because the rescaled result was `Eq`-equal to its own input and the
/// extractor handed back the un-rescaled first-inserted representative. Work item #200 repairs
/// it. See `fixedpoint_scale_dedup_ab::the_rescale_operator_is_no_longer_erased_by_its_own_input`
/// for the full measured correlation table; this pins the consensus lane specifically, because
/// this is the escape hatch any future scale-equality precondition (work item #186) depends on.
#[test]
fn rholang_rescale_operator_is_no_longer_erased_by_its_own_input() {
    for (src, want) in [
        ("fixed(3.0p1, 2)", "3.00p2"),
        ("fixed(3p0, 2)", "3.00p2"),
        ("fixed(1.25p2, 4)", "1.2500p4"),
        ("fixed(1.20p2, 1)", "1.2p1"),
    ] {
        assert_eq!(
            normal_form(src).expect("the rescale must evaluate"),
            want,
            "`{src}` must actually rescale; before #200 it answered its own un-rescaled input",
        );
    }
    assert_eq!(
        normal_form("fixed(0p0, 2)").expect("rescale"),
        "0p0",
        "⚠ RESIDUAL, not this ruling's: `normalize_in_place` forces `places = 0` on true zero \
         at construction, so zero cannot be rescaled at any identity definition",
    );
}
