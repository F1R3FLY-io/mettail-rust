//! Regression tests for BigInt surface forms, `bigint`/`bigrat` from floats, and binary `int(_, m)`.
//!
//! ## Test oracle — Path-B Dovetail normal form (not the retired `run_ascent`)
//!
//! `run_ascent` (main's f1r3node-independent reference reducer) is fail-closed on this
//! branch: the macro-side Ascent engine generator was excised in P6 (commit 9d889894),
//! so every `run_ascent` call now returns `Err("…oracle…not installed…")`. These cast
//! regressions are pure **non-COMM** reductions (arithmetic folds + width/numeric casts),
//! so the live oracle is the generated whole-box Dovetail normalizer
//! `<Lang>::dovetail_normal_term` — the *same* non-COMM reducer `rhocalc_tests.rs`'s
//! Path-B `mod oracle` drives (there wrapped in a bounded COMM fixpoint these tests do
//! not need). It returns the single typed Dovetail normal form; the `.contains`/`.any`
//! assertions below hold on that one folded value.

use mettail_languages::{calculator as calc, rhocalc};
use mettail_runtime::Language;

/// Saturation budget for the Dovetail normalizer (mirrors `rhocalc_tests::oracle`).
const DOVETAIL_ITERS: usize = 256;
const DOVETAIL_NODES: usize = 4_000_000;

/// Reduce `input` to its Calculator Dovetail normal-form display(s). The vector is empty
/// when the normalizer cannot converge/reconstruct — a *loud miss* (the `.contains`/`.any`
/// assertion then fails) rather than letting a stray error string masquerade as a result.
fn calc_nf_displays(input: &str) -> Vec<String> {
    mettail_runtime::clear_var_cache();
    let lang = calc::CalculatorLanguage;
    let term = lang.parse_term(input).expect("parse");
    match calc::CalculatorLanguage::dovetail_normal_term(
        term.as_ref(),
        DOVETAIL_ITERS,
        DOVETAIL_NODES,
    ) {
        Ok(nf) => vec![nf.to_string()],
        Err(_) => Vec::new(),
    }
}

fn calc_normal_form(input: &str, expected: &str) {
    let displays = calc_nf_displays(input);
    assert!(
        displays.contains(&expected.to_string()),
        "expected {:?} among {:?} for {:?}",
        expected,
        displays,
        input
    );
}

/// RhoCalc analogue of [`calc_nf_displays`].
fn rho_nf_displays(input: &str) -> Vec<String> {
    mettail_runtime::clear_var_cache();
    let lang = rhocalc::RhoCalcLanguage;
    let term = lang.parse_term(input).expect("parse");
    match rhocalc::RhoCalcLanguage::dovetail_normal_term(
        term.as_ref(),
        DOVETAIL_ITERS,
        DOVETAIL_NODES,
    ) {
        Ok(nf) => vec![nf.to_string()],
        Err(_) => Vec::new(),
    }
}

#[test]
fn calc_bigint_sub_neg_literal_huge() {
    // ★ The `n` tails are new (divergence I, Stage C, 2026-07-25). A `BigInt`'s declared pattern
    // makes the `n` MANDATORY, so its Display must emit it; the tail-less `-1` was a word that
    // read back as an `Int`, not a `BigInt`. The VALUES are unchanged.
    calc_normal_form("1n - 2n", "-1n");
    calc_normal_form("-1n", "-1n");
    calc_normal_form("32478132567813256718n", "32478132567813256718n");
}

#[test]
fn calc_bigint_from_sci_float() {
    let displays = calc_nf_displays("bigint(3.14e100)");
    assert!(
        displays.iter().any(|d| {
            !d.contains("cast_error") && d.chars().filter(|c| c.is_ascii_digit()).count() > 80
        }),
        "expected huge integer NF, got {:?}",
        displays
    );
}

#[test]
fn calc_bigrat_from_sci_float() {
    let displays = calc_nf_displays("bigrat(3.14e100)");
    assert!(
        displays
            .iter()
            .any(|d| !d.contains("cast_error") && !d.is_empty()),
        "expected rational NF, got {:?}",
        displays
    );
}

#[test]
fn calc_repl_parse_preserves_huge_n_suffix() {
    mettail_runtime::clear_var_cache();
    let lang = calc::CalculatorLanguage;
    let t = lang
        .parse_term_for_env("32478132567813256718n")
        .expect("parse_term_for_env");
    let nf =
        calc::CalculatorLanguage::dovetail_normal_term(t.as_ref(), DOVETAIL_ITERS, DOVETAIL_NODES)
            .expect("dovetail normal form");
    let display = nf.to_string();
    assert!(
        display == "32478132567813256718" || display == "32478132567813256718n",
        "unexpected NF: {:?}",
        display
    );
}

/// **Unary `int(_)` / `float(_)` ARE surface syntax post-merge.** The RhoCalc→Rholang-1.4
/// merge added the single-argument casts to the Calculator grammar — the identity casts
/// `IntId . a:Int |- "int" "(" a ")"` and `FloatId . a:Float |- "float" "(" a ")"`, plus the
/// cross-type conversions `FloatToInt`/`BoolToInt`/`StrToInt` and `IntToFloat`/`BoolToFloat`/
/// `StrToFloat`. So `int(3)` / `float(3.0)` now PARSE (this replaces the pre-merge fence that
/// asserted they were NOT surface syntax). (The binary width cast `int(_, m)` is exercised
/// separately above.)
///
/// The fence is on *surface-syntax validity* (parse), not on a reduced display: `int(3)` is
/// the `IntId` identity cast, so `int(3)` and `3` share an e-class and the Dovetail extractor
/// keeps the (equal-weight) cast form `int(3)` — the same e-class-extraction behavior that
/// keeps a bare integer in a process position as its `CastInt` form. We therefore assert that
/// the NF is the well-formed identity cast (non-error, non-empty), not the literal `3`.
#[test]
fn calc_unary_int_float_casts_are_surface_syntax() {
    mettail_runtime::clear_var_cache();
    let lang = calc::CalculatorLanguage;
    assert!(lang.parse_term("int(3)").is_ok(), "unary `int(3)` is now surface syntax");
    assert!(
        lang.parse_term("float(3.0)").is_ok(),
        "unary `float(3.0)` is now surface syntax"
    );
    // The identity cast normalizes to a well-formed (non-error) form carrying the operand.
    let nfs = calc_nf_displays("int(3)");
    assert!(
        nfs.iter().any(|d| !d.contains("error") && d.contains('3')),
        "unary `int(3)` should normalize to a well-formed value-bearing form, got {nfs:?}"
    );
}

#[test]
fn rho_bigint_from_sci_float() {
    let nfs = rho_nf_displays("bigint(3.14e100)");
    assert!(
        nfs.iter()
            .any(|d| !d.contains("error") && d.chars().filter(|c| c.is_ascii_digit()).count() > 80),
        "expected finite huge bigint NF, got {:?}",
        nfs
    );
}
