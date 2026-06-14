//! Verifies that a generated language can be wrapped as a Rho-default runtime
//! backend without making the generated language crate depend on
//! `mettail-rho-runtime`.

use mettail_ast::language::LanguageDef;
use mettail_languages::calculator::{
    Bool, CalculatorLanguage, CalculatorTerm, CalculatorTermInner, Int, Str,
};
use mettail_rho_codegen::{
    plan_call_by_need_thunk_with_spec, plan_rho_default_backend_with_evidence_audit,
    CallByNeedBudget, CallByNeedInitialState, CallByNeedPlanEvidence, CallByNeedThunkSpec,
    RhoAstLiteral, RhoAstSend, RhoCoverageEvidence, RhoDefaultBackendEvidence,
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
        NeInt . a:Int, b:Int |- a "!=" b : Bool ;
        LtInt . a:Int, b:Int |- a "<" b : Bool ;
        GtInt . a:Int, b:Int |- a ">" b : Bool ;
        LtEqInt . a:Int, b:Int |- a "<=" b : Bool ;
        GtEqInt . a:Int, b:Int |- a ">=" b : Bool ;
        EqBool . a:Bool, b:Bool |- a "==" b : Bool ;
        NeBool . a:Bool, b:Bool |- a "!=" b : Bool ;
        LtBool . a:Bool, b:Bool |- a "<" b : Bool ;
        GtBool . a:Bool, b:Bool |- a ">" b : Bool ;
        LtEqBool . a:Bool, b:Bool |- a "<=" b : Bool ;
        GtEqBool . a:Bool, b:Bool |- a ">=" b : Bool ;
        EqStr . a:Str, b:Str |- a "==" b : Bool ;
        NeStr . a:Str, b:Str |- a "!=" b : Bool ;
        LtStr . a:Str, b:Str |- a "<" b : Bool ;
        GtStr . a:Str, b:Str |- a ">" b : Bool ;
        LtEqStr . a:Str, b:Str |- a "<=" b : Bool ;
        GtEqStr . a:Str, b:Str |- a ">=" b : Bool ;
        And . a:Bool, b:Bool |- a "and" b : Bool ;
        Or . a:Bool, b:Bool |- a "or" b : Bool ;
        Not . a:Bool |- "not" a : Bool ;
        Concat . a:Str, b:Str |- a "++" b : Str ;
        AddStr . a:Str, b:Str |- a "+" b : Str ;
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

fn need_evidence() -> CallByNeedPlanEvidence {
    CallByNeedPlanEvidence {
        proof_evidence_refs: vec![
            "formal/rocq/rho_bridge/theories/RhoCallByNeedObservation.v".to_string()
        ],
        runtime_oracle_evidence_refs: vec![
            "mettail-rho-runtime/tests/rho_call_by_need.rs".to_string()
        ],
        budget_evidence_refs: vec![
            "formal/rocq/rho_bridge/theories/RhoCallByNeedBudget.v".to_string()
        ],
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
        vec![
            "AddInt", "SubInt", "MulInt", "DivInt", "ModInt", "EqInt", "NeInt", "LtInt", "GtInt",
            "LtEqInt", "GtEqInt", "EqBool", "NeBool", "LtBool", "GtBool", "LtEqBool", "GtEqBool",
            "EqStr", "NeStr", "LtStr", "GtStr", "LtEqStr", "GtEqStr", "And", "Or", "Not", "Concat",
            "AddStr",
        ],
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

fn bool_literal(term: &Bool) -> Result<bool, String> {
    match term {
        Bool::BoolLit(value) => Ok(*value),
        other => Err(format!("Rho calculator bridge needs ground boolean literals, got {other:?}")),
    }
}

fn binary_bool_payload_call(
    op: &str,
    left: &Bool,
    right: &Bool,
) -> Result<RhoBackendInvocation, String> {
    let left = bool_literal(left)?;
    let right = bool_literal(right)?;
    let call = RhoAstSend::contract_call(
        op,
        vec![RhoAstLiteral::Bool(left), RhoAstLiteral::Bool(right)],
        "OUT",
    )
    .map_err(|err| format!("failed to build Rho AST call for {op}: {err:?}"))?
    .par()
    .clone();
    Ok(RhoBackendInvocation::RunWithCallAndObserveBools { call, out_channel: "OUT".to_string() })
}

fn unary_bool_payload_call(op: &str, value: &Bool) -> Result<RhoBackendInvocation, String> {
    let value = bool_literal(value)?;
    let call = RhoAstSend::contract_call(op, vec![RhoAstLiteral::Bool(value)], "OUT")
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

fn binary_string_bool_call(
    op: &str,
    left: &Str,
    right: &Str,
) -> Result<RhoBackendInvocation, String> {
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
    Ok(RhoBackendInvocation::RunWithCallAndObserveBools { call, out_channel: "OUT".to_string() })
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
            Bool::NeInt(left, right) => binary_bool_call("NeInt", left.as_ref(), right.as_ref()),
            Bool::LtInt(left, right) => binary_bool_call("LtInt", left.as_ref(), right.as_ref()),
            Bool::GtInt(left, right) => binary_bool_call("GtInt", left.as_ref(), right.as_ref()),
            Bool::LtEqInt(left, right) => {
                binary_bool_call("LtEqInt", left.as_ref(), right.as_ref())
            },
            Bool::GtEqInt(left, right) => {
                binary_bool_call("GtEqInt", left.as_ref(), right.as_ref())
            },
            Bool::EqBool(left, right) => {
                binary_bool_payload_call("EqBool", left.as_ref(), right.as_ref())
            },
            Bool::NeBool(left, right) => {
                binary_bool_payload_call("NeBool", left.as_ref(), right.as_ref())
            },
            Bool::LtBool(left, right) => {
                binary_bool_payload_call("LtBool", left.as_ref(), right.as_ref())
            },
            Bool::GtBool(left, right) => {
                binary_bool_payload_call("GtBool", left.as_ref(), right.as_ref())
            },
            Bool::LtEqBool(left, right) => {
                binary_bool_payload_call("LtEqBool", left.as_ref(), right.as_ref())
            },
            Bool::GtEqBool(left, right) => {
                binary_bool_payload_call("GtEqBool", left.as_ref(), right.as_ref())
            },
            Bool::EqStr(left, right) => {
                binary_string_bool_call("EqStr", left.as_ref(), right.as_ref())
            },
            Bool::NeStr(left, right) => {
                binary_string_bool_call("NeStr", left.as_ref(), right.as_ref())
            },
            Bool::LtStr(left, right) => {
                binary_string_bool_call("LtStr", left.as_ref(), right.as_ref())
            },
            Bool::GtStr(left, right) => {
                binary_string_bool_call("GtStr", left.as_ref(), right.as_ref())
            },
            Bool::LtEqStr(left, right) => {
                binary_string_bool_call("LtEqStr", left.as_ref(), right.as_ref())
            },
            Bool::GtEqStr(left, right) => {
                binary_string_bool_call("GtEqStr", left.as_ref(), right.as_ref())
            },
            Bool::And(left, right) => {
                binary_bool_payload_call("And", left.as_ref(), right.as_ref())
            },
            Bool::Or(left, right) => binary_bool_payload_call("Or", left.as_ref(), right.as_ref()),
            Bool::Not(value) => unary_bool_payload_call("Not", value.as_ref()),
            other => Err(format!("calculator Rho backend has no invocation for {other:?}")),
        };
    }

    match calculator_str(term)? {
        Str::Concat(left, right) => binary_string_call("Concat", left.as_ref(), right.as_ref()),
        Str::AddStr(left, right) => binary_string_call("AddStr", left.as_ref(), right.as_ref()),
        other => Err(format!("calculator Rho backend has no invocation for {other:?}")),
    }
}

fn calculator_call_by_need_invocation(term: &dyn Term) -> Result<RhoBackendInvocation, String> {
    let int = calculator_int(term)?;
    let Int::AddInt(left, right) = int else {
        return Err(format!("calculator CBN bridge only covers AddInt in this test, got {int:?}"));
    };
    let value = int_literal(left.as_ref())? + int_literal(right.as_ref())?;
    let spec = CallByNeedThunkSpec::new(
        CallByNeedInitialState::Cold,
        value.to_string(),
        "AddInt",
        "NEED_OUT",
        "NEED_EVAL",
    )
    .map_err(|err| format!("failed to build calculator CBN thunk spec: {err:?}"))?;
    let plan =
        plan_call_by_need_thunk_with_spec(spec, CallByNeedBudget::new(2, 1), need_evidence())
            .map_err(|err| format!("failed to plan calculator CBN thunk: {err:?}"))?;
    Ok(RhoBackendInvocation::RunCallByNeedThunk { plan })
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
    assert_eq!(report.backend(), RuntimeBackend::RhoMachine);
    assert_eq!(report.artifact(), RuntimeBackendArtifact::RhoNormalizedAst);
    assert!(
        report
            .evidence_refs()
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
    assert_eq!(ascent_report.backend(), RuntimeBackend::Ascent);
    assert_eq!(ascent_report.artifact(), RuntimeBackendArtifact::AscentFixpoint);
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
    assert_eq!(bool_report.backend(), RuntimeBackend::RhoMachine);
    let bool_out = bool_report
        .observations_for_channel("OUT")
        .expect("Rho report must expose OUT Bool observations");
    assert_eq!(bool_out.values, vec![RuntimeObservationValue::Bool(true)]);

    let ne_int_term = language
        .parse_term("2 != 3")
        .expect("calculator Int comparison parse");
    let ne_int_report = language
        .run_default_backend_report(ne_int_term.as_ref())
        .expect("Rho default backend must report Int-comparison observations");
    let ne_int_out = ne_int_report
        .observations_for_channel("OUT")
        .expect("Rho report must expose OUT Int-comparison observations");
    assert_eq!(ne_int_out.values, vec![RuntimeObservationValue::Bool(true)]);

    let bool_order_term = language
        .parse_term("true > false")
        .expect("calculator Bool comparison parse");
    let bool_order_report = language
        .run_default_backend_report(bool_order_term.as_ref())
        .expect("Rho default backend must report Bool-comparison observations");
    let bool_order_out = bool_order_report
        .observations_for_channel("OUT")
        .expect("Rho report must expose OUT Bool-comparison observations");
    assert_eq!(bool_order_out.values, vec![RuntimeObservationValue::Bool(true)]);

    let str_predicate_term = language
        .parse_term(r#""alpha" < "beta""#)
        .expect("calculator Str comparison parse");
    let str_predicate_report = language
        .run_default_backend_report(str_predicate_term.as_ref())
        .expect("Rho default backend must report Str-comparison observations");
    let str_predicate_out = str_predicate_report
        .observations_for_channel("OUT")
        .expect("Rho report must expose OUT Str-comparison observations");
    assert_eq!(str_predicate_out.values, vec![RuntimeObservationValue::Bool(true)]);

    let str_term = language
        .parse_term(r#""rho" ++ "net""#)
        .expect("calculator Str parse");
    let str_report = language
        .run_default_backend_report(str_term.as_ref())
        .expect("Rho default backend must report Str observations");
    assert_eq!(str_report.backend(), RuntimeBackend::RhoMachine);
    let str_out = str_report
        .observations_for_channel("OUT")
        .expect("Rho report must expose OUT Str observations");
    assert_eq!(str_out.values, vec![RuntimeObservationValue::Text("rhonet".to_string())]);

    let add_str_term = language
        .parse_term(r#""rho" + "net""#)
        .expect("calculator Str plus parse");
    let add_str_report = language
        .run_default_backend_report(add_str_term.as_ref())
        .expect("Rho default backend must report Str plus observations");
    let add_str_out = add_str_report
        .observations_for_channel("OUT")
        .expect("Rho report must expose OUT Str plus observations");
    assert_eq!(add_str_out.values, vec![RuntimeObservationValue::Text("rhonet".to_string())]);
}

#[test]
fn rho_runtime_backed_language_dispatches_call_by_need_thunk_report() {
    let language = RhoRuntimeBackedLanguage::new(
        CalculatorLanguage,
        calculator_backend(),
        calculator_call_by_need_invocation,
    );
    let term = language.parse_term("2 + 3").expect("calculator parse");

    let report = language
        .run_default_backend_report(term.as_ref())
        .expect("Rho default backend must execute the planned CBN thunk invocation");
    assert_eq!(report.backend(), RuntimeBackend::RhoMachine);
    assert_eq!(report.artifact(), RuntimeBackendArtifact::RhoNormalizedAst);
    assert!(
        report.evidence_refs().iter().any(
            |evidence| evidence == "formal/rocq/rho_bridge/theories/RhoCallByNeedObservation.v"
        ),
        "CBN runtime report must carry need proof evidence refs"
    );

    let out = report
        .observations_for_channel("NEED_OUT")
        .expect("CBN report must expose generated value observations");
    assert_eq!(
        out.values,
        vec![
            RuntimeObservationValue::Text("5".to_string()),
            RuntimeObservationValue::Text("5".to_string()),
        ]
    );

    let eval = report
        .observations_for_channel("NEED_EVAL")
        .expect("CBN report must expose generated evaluation trace observations");
    assert_eq!(eval.values, vec![RuntimeObservationValue::Text("AddInt".to_string())]);
}
