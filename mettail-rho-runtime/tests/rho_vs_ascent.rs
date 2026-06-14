//! M-RHO.0.4: the differential oracle, executed against BOTH real backends.
//!
//! For each calculator Int operation this runs:
//!   - the ASCENT backend: `CalculatorLanguage::run_ascent(parse_term(input))` →
//!     its normal-form display strings, and
//!   - the RHO backend: the lowered Rholang contract (mettail-rho-codegen) on a
//!     real in-memory f1r3node RhoRuntime (mettail-rho-runtime),
//!
//! The test asserts the rho result is among the Ascent normal forms
//! (weight-erased = display-string comparison). This is the genuine two-backend
//! differential the exactness proof `OracleQuotientEquivalence.v` underwrites —
//! not a comparison against hand-written constants.

use mettail_ast::language::LanguageDef;
use mettail_languages::calculator::CalculatorLanguage;
use mettail_rho_codegen::{
    plan_rho_default_backend_with_evidence_audit, RhoAstSend, RhoCoverageEvidence,
    RhoDefaultBackendEvidence, RhoGuardCoverageEvidence,
};
use mettail_rho_runtime::PlannedRhoBackend;
use mettail_runtime::Language;
use std::collections::BTreeSet;

mod support;

const CALC_RUN_FRAGMENT: &str = r#"
    name: CalcRun,
    types { Proc }
    terms {
        AddInt . a:Int, b:Int |- a "+" b : Int ;
        SubInt . a:Int, b:Int |- a "-" b : Int ;
        MulInt . a:Int, b:Int |- a "*" b : Int ;
        DivInt . a:Int, b:Int |- a "/" b : Int ;
        ModInt . a:Int, b:Int |- a "%" b : Int ;
    }
"#;

fn passing_evidence() -> RhoDefaultBackendEvidence {
    RhoDefaultBackendEvidence {
        proofs_passed: true,
        proof_evidence_refs: vec![
            "formal/rocq/rho_bridge/theories/RhoBackendFlipGate.v".to_string()
        ],
        oracle_parity_passed: true,
        oracle_parity_evidence_refs: vec!["mettail-rho-runtime/tests/rho_vs_ascent.rs".to_string()],
        coverage_audit_passed: true,
        coverage_audit_evidence_refs: vec![
            "formal/rocq/rho_bridge/theories/RhoRejectedCoverage.v".to_string()
        ],
        scheduler_fairness_passed: true,
        scheduler_fairness_evidence_refs: vec![
            "formal/tla/rho_machine/RhoNetScheduler.tla".to_string()
        ],
        coverage: RhoCoverageEvidence::AllRulesLowered,
        guard_coverage: RhoGuardCoverageEvidence::NoGuardObligations,
    }
}

fn calculator_backend() -> PlannedRhoBackend {
    let def =
        syn::parse_str::<LanguageDef>(CALC_RUN_FRAGMENT).expect("calculator fragment must parse");
    let audit_policy = support::strict_evidence_audit_policy();
    let plan =
        plan_rho_default_backend_with_evidence_audit(&def, passing_evidence(), &audit_policy)
            .expect("all calculator Int scalar ops must pass the Rho-default gate");
    assert_eq!(
        plan.lowering.lowered,
        vec!["AddInt", "SubInt", "MulInt", "DivInt", "ModInt"],
        "all five Int binary scalar ops must lower"
    );
    assert!(plan.lowering.rejected.is_empty(), "no rule should be rejected here");
    PlannedRhoBackend::from_plan(plan).expect("audited Rho plan should build executable backend")
}

/// The Ascent backend's normal-form display strings for `input`.
fn ascent_normal_forms(lang: &CalculatorLanguage, input: &str) -> Vec<String> {
    let parsed = lang.parse_term(input).expect("calculator parse");
    let results = lang.run_ascent(parsed.as_ref()).expect("ascent eval");
    results
        .normal_forms()
        .iter()
        .map(|nf| nf.display.clone())
        .collect()
}

/// The rho backend's result of `@"op"!(a, b, @"OUT")` on a real RhoRuntime.
async fn rho_binary(backend: &PlannedRhoBackend, op: &str, a: i64, b: i64) -> i64 {
    let call = RhoAstSend::binary_int_call(op, a, b, "OUT").expect("rho binary call must build");
    let report = backend
        .run_with_call_and_observe_ints(call.par(), "OUT")
        .await
        .unwrap_or_else(|e| panic!("rho {op}({a},{b}): {e}"));
    assert_eq!(report.observed_count(), 1, "rho {op}({a},{b}) must yield exactly one int");
    report.values[0]
}

#[tokio::test]
async fn rho_backend_agrees_with_ascent_on_calculator_int_ops() {
    let lang = CalculatorLanguage;
    let backend = calculator_backend();

    // (Ascent input string, rho op label, operands). The calculator parses the
    // input to the matching constructor; both backends must agree on the result.
    let cases: &[(&str, &str, i64, i64)] = &[
        ("2 + 3", "AddInt", 2, 3),
        ("10 - 4", "SubInt", 10, 4),
        ("3 * 7", "MulInt", 3, 7),
        ("20 / 4", "DivInt", 20, 4),
        ("17 % 5", "ModInt", 17, 5),
    ];

    for &(input, op, a, b) in cases {
        let ascent = ascent_normal_forms(&lang, input);
        let rho = rho_binary(&backend, op, a, b).await;
        let rho_fingerprint = BTreeSet::from([rho.to_string()]);
        let ascent_fingerprint: BTreeSet<_> = ascent.iter().cloned().collect();
        assert!(
            rho_fingerprint.is_subset(&ascent_fingerprint),
            "DIVERGENCE on `{input}`: rho-backend = {rho}, Ascent normal forms = {ascent:?}"
        );
    }
}
