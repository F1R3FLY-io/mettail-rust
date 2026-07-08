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

    // Stage 3f routed BaseMath's native scalar fold
    //     `Add . a:Num, b:Num |- a "+" b : Num ![a + b] fold;`
    // onto the TYPED fold path (`has_native_fold_rewrite`), so `dovetail_report_for` — the production
    // `exec` reducer — now FIRES the `Add` fold and reduces `1 + 2` to its normal form `3`. (The
    // pre-3f untyped `EGraph<String>` path left the redex STRUCTURAL because a native-output fold
    // reduced nowhere there — an artifact of BaseMath having no working reducer on that path, not a
    // feature. The old `Add`-root + `NumLit::1`/`NumLit::2` child term records were that non-reducing
    // shape and went stale when the fold started firing.)
    //
    // The structural-constructor boundary over the parsed `Add` term is now witnessed — MORE strongly
    // than before — by the fold firing whose σ binds the Add's two `NumLit` operand children and whose
    // contractum is the reduced literal:
    //
    //     Num_Add   σ = { a ↦ NumLit(1), b ↦ NumLit(2) }   ⊢   contractum NumLit(3)
    //
    // and the extracted normal form is that `NumLit(3)`.

    // (1) The native `Add` fold fired exactly once over the parsed redex.
    assert!(
        report.rule_firings.iter().any(|firing| {
            firing.label.as_deref() == Some("BaseMath::fold::Num_Add") && firing.count == 1
        }),
        "typed report should record the Num_Add fold firing exactly once: {report:?}",
    );

    // (2) Its justification carries the structural-constructor boundary: σ binds the Add's two
    //     `NumLit` operand children, and the contractum is the reduced `NumLit(3)`.
    let add = report
        .rewrite_justifications
        .iter()
        .find(|justification| justification.rule_label == "Num_Add")
        .unwrap_or_else(|| panic!("typed report must justify the Num_Add firing: {report:?}"));
    let sigma_operand = |name: &str| {
        add.sigma
            .iter()
            .find(|(var, _)| var == name)
            .map(|(_, subterm)| subterm.constructor.as_str())
    };
    assert_eq!(
        sigma_operand("a"),
        Some("NumLit(1)"),
        "Num_Add σ should bind operand `a` to the parsed NumLit(1) child: {report:?}",
    );
    assert_eq!(
        sigma_operand("b"),
        Some("NumLit(2)"),
        "Num_Add σ should bind operand `b` to the parsed NumLit(2) child: {report:?}",
    );
    assert_eq!(
        add.contractum.as_ref().map(|c| c.constructor.as_str()),
        Some("NumLit(3)"),
        "Num_Add contractum should be the reduced NumLit(3): {report:?}",
    );

    // (3) The extracted normal-form root is that reduced literal.
    assert!(
        report
            .terms
            .iter()
            .any(|record| record.is_root && record.op_display == "BaseMath::Num::NumLit(3)"),
        "structural report should reduce to the NumLit(3) normal-form root: {report:?}",
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

#[test]
fn exec_dovetail_report_leaves_source_display_none_byte_identical() {
    // Perf-neutrality regression guard for the REPL `step` UX work: the production `exec` path
    // (`dovetail_report_for`) must stay byte-identical to the pre-stepper build — every term
    // record's `source_display` is `None`, because source reconstruction is gated behind
    // `record_source` (false on the exec path; only the step-only `dovetail_step_report` sets it).
    // This guards against a future change accidentally populating source on the exec path. (The
    // step path's source reconstruction is verified end-to-end by the REPL `step 1+2*3 → 7` check.)
    let term = BaseMathLanguage
        .parse_term("1 + 2")
        .expect("BaseMath parses scalar addition");

    let exec = BaseMathLanguage::dovetail_report_for(term.as_ref(), 8, 1_024)
        .expect("exec Dovetail report runs");
    assert!(
        exec.terms.iter().all(|record| record.source_display.is_none()),
        "exec report must leave source_display None on every record (byte-identical exec): {exec:?}",
    );
}
