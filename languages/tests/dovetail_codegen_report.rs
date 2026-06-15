#![cfg(feature = "dovetail-codegen")]

use mettail_languages::basemath::BaseMathLanguage;
use mettail_languages::lambda::LambdaLanguage;
use mettail_runtime::{Language, RuntimeDovetailCompleteness};

#[test]
fn generated_dovetail_report_runs_structural_constructor_boundary() {
    let term = BaseMathLanguage
        .parse_term("1 + 2")
        .expect("BaseMath parses scalar addition");

    let report = BaseMathLanguage::dovetail_report_for(term.as_ref(), 8, 1_024)
        .expect("generated Dovetail report compiler should run");

    report
        .validate_shape()
        .expect("generated report must be structurally valid");
    assert_eq!(report.completeness, RuntimeDovetailCompleteness::Complete);
    assert!(
        report
            .terms
            .iter()
            .any(|record| record.is_root && record.op_display == "BaseMath::Num::Add"),
        "structural report should include the parsed Add root: {report:?}",
    );
    assert!(
        report
            .terms
            .iter()
            .any(|record| record.op_display == "BaseMath::Num::NumLit::1")
            && report
                .terms
                .iter()
                .any(|record| record.op_display == "BaseMath::Num::NumLit::2"),
        "structural report should include exact literal children: {report:?}",
    );
}

#[test]
fn generated_dovetail_compiler_stage_matches_language_metadata() {
    let stage = BaseMathLanguage::dovetail_compiler_stage();
    let fingerprint = BaseMathLanguage
        .metadata()
        .definition_fingerprint()
        .expect("generated metadata exposes a definition fingerprint");

    assert_eq!(stage.definition_fingerprint(), fingerprint);
}

#[test]
fn generated_dovetail_report_fails_closed_for_unlowered_binder_rules() {
    let term = LambdaLanguage
        .parse_term("x")
        .expect("Lambda parses an auto-generated variable term");

    let err = LambdaLanguage::dovetail_report_for(term.as_ref(), 8, 1_024)
        .expect_err("Lambda beta still requires binder/substitution lowering");

    assert!(
        err.contains("needs specialized lowering")
            && err.contains("substitution patterns require generated substitution lowering"),
        "unexpected Lambda fail-closed error: {err}",
    );
}
