//! M-RHO.0.4: the differential oracle, executed against BOTH real backends.
//!
//! For each calculator Int operation this runs:
//!   - the explicit ASCENT oracle:
//!     `CalculatorLanguage::run_ascent(parse_term(input))` → its normal-form
//!     display strings, and
//!   - the RHO backend: the REAL `CalculatorLanguage` definition (reconstructed
//!     from `definition_source()`, so the plan fingerprint equals the generated
//!     one — no synthetic fragment) lowered to a Rholang contract
//!     (mettail-rho-codegen) on a real in-memory f1r3node RhoRuntime
//!     (mettail-rho-runtime),
//!
//! Both sides are therefore the SAME real language. The test asserts the rho
//! result is among the Ascent normal forms (weight-erased = display-string
//! comparison). This is the genuine two-backend differential the exactness proof
//! `OracleQuotientEquivalence.v` underwrites — not a comparison against
//! hand-written constants.

use mettail_ast::language::LanguageDef;
use mettail_languages::calculator::CalculatorLanguage;
use mettail_rho_codegen::{
    lower_language_def, plan_rho_default_backend, reconstruct_language_def, RhoAstSend,
    RhoCoverageEvidence, RhoDefaultBackendRequirements, RhoGuardCoverageEvidence,
    RhoRejectedRuleDisposition, RhoRejectedRuleDispositionKind,
};
use mettail_rho_runtime::PlannedRhoBackend;
use mettail_runtime::{Language, LanguageMetadata};
use std::collections::BTreeSet;

/// Reconstruct the REAL `CalculatorLanguage` augmented `LanguageDef` from its
/// generated `definition_source()` — the same identity path the production
/// installer uses, so the resulting plan's fingerprint equals the generated one.
fn calculator_def() -> LanguageDef {
    let source = CalculatorLanguage
        .metadata()
        .definition_source()
        .expect("generated CalculatorLanguage must expose its definition_source");
    reconstruct_language_def(source)
        .expect("CalculatorLanguage definition_source must reconstruct as a LanguageDef")
}

/// Map every scalar-lowering-rejected rule (big-numeric folds, casts, …) to an
/// exactly-once native-handler disposition (deduplicated; a label may appear in
/// several rejected categories).
fn native_handler_dispositions_for(def: &LanguageDef) -> Vec<RhoRejectedRuleDisposition> {
    lower_language_def(def)
        .rejected
        .iter()
        .cloned()
        .collect::<BTreeSet<String>>()
        .into_iter()
        .map(|label| {
            RhoRejectedRuleDisposition::new(label, RhoRejectedRuleDispositionKind::NativeHandler)
        })
        .collect()
}

fn calculator_requirements() -> RhoDefaultBackendRequirements {
    RhoDefaultBackendRequirements {
        coverage: RhoCoverageEvidence::CoveredRejectedRules(native_handler_dispositions_for(
            &calculator_def(),
        )),
        guard_coverage: RhoGuardCoverageEvidence::NoGuardObligations,
    }
}

/// Build the Rho-default backend plan from the REAL `CalculatorLanguage` def, so
/// BOTH sides of the differential are the real language: the Ascent side runs
/// `CalculatorLanguage::run_ascent` and the Rho side runs a plan whose
/// `definition_fingerprint()` equals `CalculatorLanguage`'s (no synthetic fragment).
fn calculator_backend() -> PlannedRhoBackend {
    let def = calculator_def();
    let plan = plan_rho_default_backend(&def, calculator_requirements())
        .expect("real Calculator def must pass the Rho-default gate with native-handler coverage");
    assert_eq!(plan.language_name(), "Calculator", "the Rho side must be the real Calculator");
    assert_eq!(
        plan.definition_fingerprint(),
        CalculatorLanguage
            .metadata()
            .definition_fingerprint()
            .expect("generated Calculator must expose its definition fingerprint"),
        "the Rho-side plan must be the REAL Calculator (fingerprint parity, no shim)"
    );
    for op in ["AddInt", "SubInt", "MulInt", "DivInt", "ModInt"] {
        assert!(
            plan.lowering.lowered.iter().any(|lowered| lowered == op),
            "the real Calculator plan must lower the Int op {op} the differential exercises"
        );
    }
    PlannedRhoBackend::from_plan(plan)
}

/// The explicit Ascent oracle's normal-form display strings for `input`.
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
