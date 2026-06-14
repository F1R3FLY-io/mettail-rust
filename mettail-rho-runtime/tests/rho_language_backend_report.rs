//! Verifies that a generated language can be wrapped as a Rho-default runtime
//! backend without making the generated language crate depend on
//! `mettail-rho-runtime`.

use mettail_ast::language::LanguageDef;
use mettail_languages::calculator::{
    Bool, CalculatorLanguage, CalculatorTerm, CalculatorTermInner, Int, Str,
};
use mettail_rho_codegen::{
    plan_rho_default_backend_with_evidence_audit, RhoAstLiteral, RhoAstSend, RhoCoverageEvidence,
    RhoDefaultBackendEvidence,
};
use mettail_rho_runtime::{PlannedRhoBackend, RhoBackendInvocation, RhoRuntimeBackedLanguage};
use mettail_runtime::{
    Language, RuntimeBackend, RuntimeBackendArtifact, RuntimeObservationValue, SeedFacts, Term,
};

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
        EqInt . a:Int, b:Int |- a "==" b : Bool ;
        Concat . a:Str, b:Str |- a "++" b : Str ;
    }
"#;

fn passing_evidence() -> RhoDefaultBackendEvidence {
    RhoDefaultBackendEvidence {
        proofs_passed: true,
        proof_evidence_refs: vec![
            "formal/rocq/rho_bridge/theories/RhoBackendFlipGate.v".to_string(),
            "formal/rocq/rho_bridge/theories/RuntimeBackendDispatch.v".to_string(),
        ],
        oracle_parity_passed: true,
        oracle_parity_evidence_refs: vec![
            "mettail-rho-runtime/tests/rho_language_backend_report.rs".to_string(),
        ],
        coverage_audit_passed: true,
        coverage_audit_evidence_refs: vec![
            "formal/rocq/rho_bridge/theories/RhoRejectedCoverage.v".to_string()
        ],
        scheduler_fairness_passed: true,
        scheduler_fairness_evidence_refs: vec![
            "formal/tla/rho_machine/RhoNetScheduler.tla".to_string()
        ],
        coverage: RhoCoverageEvidence::AllRulesLowered,
    }
}

fn calculator_backend() -> PlannedRhoBackend {
    let def =
        syn::parse_str::<LanguageDef>(CALC_RUN_FRAGMENT).expect("calculator fragment must parse");
    let audit_policy = support::strict_evidence_audit_policy();
    let plan =
        plan_rho_default_backend_with_evidence_audit(&def, passing_evidence(), &audit_policy)
            .expect("calculator Int scalar ops must pass the Rho-default gate");
    assert_eq!(
        plan.lowering.lowered,
        vec!["AddInt", "SubInt", "MulInt", "DivInt", "ModInt", "EqInt", "Concat"],
        "all binary Int, Bool, and Str scalar ops in this fragment must lower"
    );
    assert!(plan.lowering.rejected.is_empty(), "no rule should be rejected here");
    PlannedRhoBackend::from_plan(plan)
}

fn int_literal(term: &Int) -> Result<i64, String> {
    match term {
        Int::NumLit(value) => Ok(i64::from(*value)),
        other => Err(format!("Rho calculator bridge needs ground integer literals, got {other:?}")),
    }
}

fn binary_call(op: &str, left: &Int, right: &Int) -> Result<RhoBackendInvocation, String> {
    let left = int_literal(left)?;
    let right = int_literal(right)?;
    let call = RhoAstSend::binary_int_call(op, left, right, "OUT")
        .map_err(|err| format!("failed to build Rho AST call for {op}: {err:?}"))?
        .par()
        .clone();
    Ok(RhoBackendInvocation::RunWithCallAndObserveInts { call, out_channel: "OUT".to_string() })
}

fn binary_bool_call(op: &str, left: &Int, right: &Int) -> Result<RhoBackendInvocation, String> {
    let left = int_literal(left)?;
    let right = int_literal(right)?;
    let call = RhoAstSend::binary_int_call(op, left, right, "OUT")
        .map_err(|err| format!("failed to build Rho AST call for {op}: {err:?}"))?
        .par()
        .clone();
    Ok(RhoBackendInvocation::RunWithCallAndObserveBools { call, out_channel: "OUT".to_string() })
}

fn string_literal(term: &Str) -> Result<String, String> {
    match term {
        Str::StringLit(value) => Ok(value.clone()),
        other => Err(format!("Rho calculator bridge needs ground string literals, got {other:?}")),
    }
}

fn binary_string_call(op: &str, left: &Str, right: &Str) -> Result<RhoBackendInvocation, String> {
    let left = string_literal(left)?;
    let right = string_literal(right)?;
    let call = RhoAstSend::contract_call(
        op,
        vec![RhoAstLiteral::String(left), RhoAstLiteral::String(right)],
        "OUT",
    )
    .map_err(|err| format!("failed to build Rho AST call for {op}: {err:?}"))?
    .par()
    .clone();
    Ok(RhoBackendInvocation::RunWithCallAndObserveStrings { call, out_channel: "OUT".to_string() })
}

fn calculator_int(term: &dyn Term) -> Result<&Int, String> {
    let term = term
        .as_any()
        .downcast_ref::<CalculatorTerm>()
        .ok_or_else(|| format!("expected CalculatorTerm, got {term:?}"))?;
    calculator_int_inner(&term.0)
        .ok_or_else(|| format!("expected an Int calculator alternative, got {:?}", term.0))
}

fn calculator_int_inner(inner: &CalculatorTermInner) -> Option<&Int> {
    match inner {
        CalculatorTermInner::Int(int) => Some(int),
        CalculatorTermInner::Ambiguous(alternatives) => {
            alternatives.iter().find_map(calculator_int_inner)
        },
        _ => None,
    }
}

fn calculator_bool(term: &dyn Term) -> Result<&Bool, String> {
    let term = term
        .as_any()
        .downcast_ref::<CalculatorTerm>()
        .ok_or_else(|| format!("expected CalculatorTerm, got {term:?}"))?;
    calculator_bool_inner(&term.0)
        .ok_or_else(|| format!("expected a Bool calculator alternative, got {:?}", term.0))
}

fn calculator_bool_inner(inner: &CalculatorTermInner) -> Option<&Bool> {
    match inner {
        CalculatorTermInner::Bool(bool_term) => Some(bool_term),
        CalculatorTermInner::Ambiguous(alternatives) => {
            alternatives.iter().find_map(calculator_bool_inner)
        },
        _ => None,
    }
}

fn calculator_str(term: &dyn Term) -> Result<&Str, String> {
    let term = term
        .as_any()
        .downcast_ref::<CalculatorTerm>()
        .ok_or_else(|| format!("expected CalculatorTerm, got {term:?}"))?;
    calculator_str_inner(&term.0)
        .ok_or_else(|| format!("expected a Str calculator alternative, got {:?}", term.0))
}

fn calculator_str_inner(inner: &CalculatorTermInner) -> Option<&Str> {
    match inner {
        CalculatorTermInner::Str(str_term) => Some(str_term),
        CalculatorTermInner::Ambiguous(alternatives) => {
            alternatives.iter().find_map(calculator_str_inner)
        },
        _ => None,
    }
}

fn calculator_invocation(term: &dyn Term) -> Result<RhoBackendInvocation, String> {
    if let Ok(int) = calculator_int(term) {
        return match int {
            Int::AddInt(left, right) => binary_call("AddInt", left.as_ref(), right.as_ref()),
            Int::SubInt(left, right) => binary_call("SubInt", left.as_ref(), right.as_ref()),
            Int::MulInt(left, right) => binary_call("MulInt", left.as_ref(), right.as_ref()),
            Int::DivInt(left, right) => binary_call("DivInt", left.as_ref(), right.as_ref()),
            Int::ModInt(left, right) => binary_call("ModInt", left.as_ref(), right.as_ref()),
            other => Err(format!("calculator Rho backend has no invocation for {other:?}")),
        };
    }

    if let Ok(bool_term) = calculator_bool(term) {
        return match bool_term {
            Bool::EqInt(left, right) => binary_bool_call("EqInt", left.as_ref(), right.as_ref()),
            other => Err(format!("calculator Rho backend has no invocation for {other:?}")),
        };
    }

    match calculator_str(term)? {
        Str::Concat(left, right) => binary_string_call("Concat", left.as_ref(), right.as_ref()),
        other => Err(format!("calculator Rho backend has no invocation for {other:?}")),
    }
}

#[test]
fn rho_runtime_backed_language_dispatches_default_report() {
    let language = RhoRuntimeBackedLanguage::new(
        CalculatorLanguage,
        calculator_backend(),
        calculator_invocation,
    );
    let term = language.parse_term("2 + 3").expect("calculator parse");

    assert_eq!(language.default_runtime_backend(), RuntimeBackend::RhoMachine);
    assert!(language.supports_runtime_backend(RuntimeBackend::RhoMachine));
    assert!(language.supports_runtime_backend(RuntimeBackend::Ascent));
    assert!(!language.supports_runtime_backend(RuntimeBackend::Dovetail));
    let static_capabilities = language.metadata().runtime_backends();
    assert_eq!(static_capabilities.len(), 1);
    assert_eq!(static_capabilities[0].backend, RuntimeBackend::Ascent);
    assert!(static_capabilities[0].is_default);

    let capabilities = language.runtime_backend_capabilities();
    assert_eq!(capabilities.len(), 2);
    assert_eq!(capabilities[0].backend, RuntimeBackend::RhoMachine);
    assert!(capabilities[0].is_default);
    assert!(
        capabilities[0]
            .evidence_refs
            .iter()
            .any(|evidence| evidence == "formal/rocq/rho_bridge/theories/RhoBackendFlipGate.v"),
        "Rho runtime capability must carry flip-gate evidence refs"
    );
    assert_eq!(capabilities[1].backend, RuntimeBackend::Ascent);
    assert!(!capabilities[1].is_default);

    let report = language
        .run_default_backend_report(term.as_ref())
        .expect("Rho default backend must return a runtime report");
    assert_eq!(report.backend, RuntimeBackend::RhoMachine);
    assert_eq!(report.artifact, RuntimeBackendArtifact::RhoNormalizedAst);
    assert!(
        report
            .evidence_refs
            .iter()
            .any(|evidence| evidence == "formal/rocq/rho_bridge/theories/RhoBackendFlipGate.v"),
        "Rho backend report must carry flip-gate evidence refs"
    );

    let out = report
        .observations_for_channel("OUT")
        .expect("Rho report must expose OUT observations");
    assert_eq!(out.values, vec![RuntimeObservationValue::Int(5)]);

    let ascent_report = language
        .run_backend_report(RuntimeBackend::Ascent, term.as_ref())
        .expect("explicit Ascent backend must still delegate to the wrapped language");
    assert_eq!(ascent_report.backend, RuntimeBackend::Ascent);
    assert_eq!(ascent_report.artifact, RuntimeBackendArtifact::AscentFixpoint);
    assert!(ascent_report.as_ascent_results().is_some());

    let compat_err = language
        .run_default_backend(term.as_ref())
        .expect_err("Ascent-shaped compatibility API must reject Rho observations");
    assert!(
        compat_err
            .contains("RhoMachine backend for language Calculator returned runtime observations"),
        "{compat_err}"
    );

    let mut facts = SeedFacts::new();
    facts.insert("certified".to_string(), vec![vec!["2 + 3".to_string()]]);
    let seeded_err = language
        .run_default_backend_report_with_facts(term.as_ref(), &facts)
        .expect_err("Rho path must reject Ascent-shaped fact seeding");
    assert!(
        seeded_err.contains("does not accept Ascent-shaped seeded facts"),
        "{seeded_err}"
    );

    let bool_term = language
        .parse_term("2 == 2")
        .expect("calculator Bool parse");
    let bool_report = language
        .run_default_backend_report(bool_term.as_ref())
        .expect("Rho default backend must report Bool observations");
    assert_eq!(bool_report.backend, RuntimeBackend::RhoMachine);
    let bool_out = bool_report
        .observations_for_channel("OUT")
        .expect("Rho report must expose OUT Bool observations");
    assert_eq!(bool_out.values, vec![RuntimeObservationValue::Bool(true)]);

    let str_term = language
        .parse_term(r#""rho" ++ "net""#)
        .expect("calculator Str parse");
    let str_report = language
        .run_default_backend_report(str_term.as_ref())
        .expect("Rho default backend must report Str observations");
    assert_eq!(str_report.backend, RuntimeBackend::RhoMachine);
    let str_out = str_report
        .observations_for_channel("OUT")
        .expect("Rho report must expose OUT Str observations");
    assert_eq!(str_out.values, vec![RuntimeObservationValue::Text("rhonet".to_string())]);
}
