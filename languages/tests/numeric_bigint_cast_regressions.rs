//! Regression tests for BigInt surface forms, `bigint`/`bigrat` from floats, and binary `int(_, m)`.

use mettail_languages::{calculator as calc, rhocalc};
use mettail_runtime::Language;
use mettail_testkit::runtime_report::{report_semantic_outputs, run_ascent_oracle_report};

fn calc_nf_displays(input: &str) -> Vec<String> {
    mettail_runtime::clear_var_cache();
    let lang = calc::CalculatorLanguage;
    let term = lang.parse_term(input).expect("parse");
    let report = run_ascent_oracle_report(&lang, term.as_ref(), "calculator numeric cast eval")
        .expect("Ascent oracle");
    report_semantic_outputs(&report)
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

fn rho_nf_displays(input: &str) -> Vec<String> {
    mettail_runtime::clear_var_cache();
    let lang = rhocalc::RhoCalcLanguage;
    let term = lang.parse_term(input).expect("parse");
    let report = run_ascent_oracle_report(&lang, term.as_ref(), "rhocalc numeric cast eval")
        .expect("Ascent oracle");
    report_semantic_outputs(&report)
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
    let report =
        run_ascent_oracle_report(&lang, t.as_ref(), "calculator repl bigint eval").expect("run");
    let displays = report_semantic_outputs(&report);
    let ok = displays
        .iter()
        .any(|display| display == "32478132567813256718" || display == "32478132567813256718n");
    assert!(ok, "unexpected backend outputs: {:?}", displays);
}

#[test]
fn rho_bigint_from_sci_float() {
    let nfs = rho_nf_displays("{bigint(3.14e100)}");
    assert!(
        nfs.iter()
            .any(|d| !d.contains("error") && d.chars().filter(|c| c.is_ascii_digit()).count() > 80),
        "expected finite huge bigint NF, got {:?}",
        nfs
    );
}
