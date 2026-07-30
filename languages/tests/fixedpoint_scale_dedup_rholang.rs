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

/// Diagnostic: the whole A/B table for rholang in one run.
#[test]
fn rholang_ab_table_diagnostic() {
    let rows = [
        ("P0  baseline           ", P0),
        ("P0' same-scale sibling ", P0_SAME_SCALE),
        ("P1  lower-scale FIRST  ", P1_LOWER_SCALE_FIRST),
        ("P2  lower-scale LAST   ", P2_LOWER_SCALE_LAST),
        ("P3  different value    ", P3_DIFFERENT_VALUE),
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

/// ⚠ DEFECT WITNESS (consensus lane). Mirrors
/// `fixedpoint_scale_dedup_ab::witness_equal_value_sibling_changes_the_quotient`, but through
/// rholang's `Proc`-sited `Div`. See that file's banner for the RED form and the mechanism.
#[test]
fn rholang_witness_equal_value_sibling_changes_the_quotient() {
    let p0 = normal_form(P0).expect("P0 must evaluate");
    let p1 = normal_form(P1_LOWER_SCALE_FIRST).expect("P1 must evaluate");
    let p0_same = normal_form(P0_SAME_SCALE).expect("P0' must evaluate");
    let p3 = normal_form(P3_DIFFERENT_VALUE).expect("P3 must evaluate");

    assert_eq!(p0, "2.33p2", "baseline");
    assert_eq!(p0_same, "2.33p2", "control (a-size): SAME-scale sibling must not move it");
    assert_eq!(p3, "2.33p2", "control (b-negative): DIFFERENT-VALUE sibling must not move it");
    assert_eq!(
        p1, "2.3p1",
        "⚠ WITNESS in the consensus language: an equal-value lower-scale sibling changes the \
         quotient computed by rholang's `Div` fold"
    );
    assert_ne!(p0, p1, "⚠ 233/100 != 23/10 — a genuine value difference");
}

/// ⚠ DEFECT WITNESS (consensus lane) — and order-dependent.
#[test]
fn rholang_witness_the_quotient_depends_on_textual_order() {
    let p1 = normal_form(P1_LOWER_SCALE_FIRST).expect("P1 must evaluate");
    let p2 = normal_form(P2_LOWER_SCALE_LAST).expect("P2 must evaluate");
    assert_eq!(p1, "2.3p1", "siblings FIRST => the p1 representative survives");
    assert_eq!(p2, "2.33p2", "siblings LAST => the p2 representative survives");
    assert_ne!(
        p1, p2,
        "⚠ WITNESS: two rholang programs differing ONLY in the order of two summands compute \
         different quotients"
    );
}
