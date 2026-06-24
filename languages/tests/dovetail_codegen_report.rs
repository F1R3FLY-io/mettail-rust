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
fn generated_dovetail_report_lowers_lambda_after_substitution_lowering() {
    // Before E1 (generalized substitution lowering / β-reduction in the Dovetail e-graph,
    // commit `e463895c`), a Lambda term failed closed at rule construction because its
    // substitution/β rules had no lowering. E1 made them lowerable, so a Lambda term now lowers in
    // the e-graph; a bare free variable has no redex and lowers to itself. This test guards that
    // E1 lowering stays wired (the prior fail-closed assertion went stale at E1).
    let term = LambdaLanguage
        .parse_term("x")
        .expect("Lambda parses an auto-generated variable term");

    let report = LambdaLanguage::dovetail_report_for(term.as_ref(), 8, 1_024)
        .expect("Lambda lowers in the Dovetail e-graph after substitution lowering (E1)");

    assert!(
        !report.terms.is_empty(),
        "the lowered Lambda variable report should carry at least one term record: {report:?}",
    );
}
