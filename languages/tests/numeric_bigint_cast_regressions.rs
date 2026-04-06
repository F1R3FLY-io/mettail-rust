//! Regression tests for BigInt surface forms, `bigint`/`bigrat` from floats, and binary `int(_, m)`.

use mettail_languages::{calculator as calc, rhocalc};
use mettail_runtime::Language;

fn calc_nf_displays(input: &str) -> Vec<String> {
    mettail_runtime::clear_var_cache();
    let lang = calc::CalculatorLanguage;
    let term = lang.parse_term(input).expect("parse");
    let results = lang.run_ascent(term.as_ref()).expect("run_ascent");
    results
        .normal_forms()
        .iter()
        .map(|nf| nf.display.clone())
        .collect()
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

fn rho_run(input: &str) -> mettail_runtime::AscentResults {
    mettail_runtime::clear_var_cache();
    let lang = rhocalc::RhoCalcLanguage;
    let term = lang.parse_term(input).expect("parse");
    lang.run_ascent(term.as_ref()).expect("run_ascent")
}

#[test]
fn calc_bigint_sub_neg_literal_huge() {
    calc_normal_form("1n - 2n", "-1");
    calc_normal_form("-1n", "-1");
    calc_normal_form("32478132567813256718n", "32478132567813256718");
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
    let results = lang.run_ascent(t.as_ref()).expect("run");
    let ok = results
        .normal_forms()
        .iter()
        .any(|nf| nf.display == "32478132567813256718" || nf.display == "32478132567813256718n");
    assert!(ok, "unexpected NFs: {:?}", results.normal_forms());
}

#[test]
fn calc_unary_int_is_not_surface_syntax() {
    mettail_runtime::clear_var_cache();
    let lang = calc::CalculatorLanguage;
    assert!(lang.parse_term("int(3)").is_err());
    assert!(lang.parse_term("float(3.0)").is_err());
}

#[test]
fn rho_bigint_from_sci_float() {
    let results = rho_run("{bigint(3.14e100)}");
    let nfs: Vec<_> = results
        .normal_forms()
        .iter()
        .map(|nf| nf.display.clone())
        .collect();
    assert!(
        nfs.iter()
            .any(|d| !d.contains("error") && d.chars().filter(|c| c.is_ascii_digit()).count() > 80),
        "expected finite huge bigint NF, got {:?}",
        nfs
    );
}
