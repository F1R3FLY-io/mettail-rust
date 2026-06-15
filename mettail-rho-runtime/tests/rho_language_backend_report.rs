//! Verifies that a generated language can be wrapped as a Rho-default runtime
//! backend without making the generated language crate depend on
//! `mettail-rho-runtime`.

use mettail_ast::identity::language_definition_fingerprint;
use mettail_ast::language::LanguageDef;
use mettail_languages::calculator::{
    Bool, CalculatorLanguage, CalculatorTerm, CalculatorTermInner, Int, Str,
};
use mettail_rho_codegen::{
    lower_language_def, plan_call_by_need_thunk_with_spec, plan_rho_default_backend,
    reconstruct_language_def, CallByNeedBudget, CallByNeedInitialState, CallByNeedThunkSpec,
    RhoAstLiteral, RhoCoverageEvidence, RhoDefaultBackendRequirements, RhoGuardCoverageEvidence,
    RhoRejectedRuleDisposition, RhoRejectedRuleDispositionKind,
};
use mettail_rho_runtime::{
    build_scalar_contract_invocation_from_contract, install_dovetail_rho_runtime_backend,
    install_rho_runtime_backend, DovetailCompilerStage, DovetailRhoRuntimeBackedLanguage,
    PlannedRhoBackend, RhoBackendInvocation, RhoInvocationCompilerStage, RhoRuntimeBackedLanguage,
    RhoRuntimeBackedLanguageError,
};
use mettail_runtime::{
    Language, RuntimeBackend, RuntimeBackendArtifact, RuntimeBackendOutput,
    RuntimeDovetailCompleteness, RuntimeDovetailRunReport, RuntimeDovetailTermRecord,
    RuntimeObservationValue, SeedFacts, Term,
};

// `complete_dovetail_report_for` / `bounded_dovetail_report_for` /
// `malformed_dovetail_report_for` remain as hand-rolled Dovetail report stubs
// used by the bad-stage tests; `generated_calculator_dovetail_report_for` is
// the real generated report used by the acceptance/execution tests.

/// Reconstruct the REAL `CalculatorLanguage` augmented `LanguageDef` from the
/// generated metadata's `definition_source()`. This is the exact macro-time
/// def (composition + auto-injection) the generated `definition_fingerprint()`
/// was computed over — no fingerprint-spoofing fragment shim.
fn calculator_def() -> LanguageDef {
    let source = CalculatorLanguage
        .metadata()
        .definition_source()
        .expect("generated CalculatorLanguage must expose its definition_source");
    reconstruct_language_def(source)
        .expect("CalculatorLanguage definition_source must reconstruct as a LanguageDef")
}

/// Map a lowering's rejected-rule labels to exactly-once native-handler
/// dispositions. The lowering may list the same label more than once (e.g.
/// `Err` appears in several categories); `RhoCoverageEvidence` compares covered
/// rules as a set but forbids duplicate dispositions, so the labels are
/// de-duplicated (deterministically, via `BTreeSet`) before mapping.
fn native_handler_dispositions_for(def: &LanguageDef) -> Vec<RhoRejectedRuleDisposition> {
    let lowering = lower_language_def(def);
    lowering
        .rejected
        .iter()
        .cloned()
        .collect::<std::collections::BTreeSet<String>>()
        .into_iter()
        .map(|label| {
            RhoRejectedRuleDisposition::new(label, RhoRejectedRuleDispositionKind::NativeHandler)
        })
        .collect()
}

/// Coverage requirements for the REAL Calculator: every rule that the scalar
/// lowering family records as `rejected` is dispatched through a verified
/// native-handler boundary (the generated `rho_scalar_contract_invocation_*`
/// path), so the default-backend gate sees exact coverage.
fn calculator_requirements() -> RhoDefaultBackendRequirements {
    RhoDefaultBackendRequirements {
        coverage: RhoCoverageEvidence::CoveredRejectedRules(native_handler_dispositions_for(
            &calculator_def(),
        )),
        guard_coverage: RhoGuardCoverageEvidence::NoGuardObligations,
    }
}

/// Build the Rho-default backend plan from the REAL `CalculatorLanguage`
/// augmented definition. The plan's `definition_fingerprint()` therefore equals
/// `CalculatorLanguage.metadata().definition_fingerprint()`, so it installs on
/// the real `CalculatorLanguage` (no shim).
fn calculator_backend() -> PlannedRhoBackend {
    let def = calculator_def();
    let plan = plan_rho_default_backend(&def, calculator_requirements())
        .expect("real Calculator def must pass the Rho-default gate with native-handler coverage");
    assert_eq!(
        plan.language_name(),
        "Calculator",
        "real Calculator plan must preserve its source LanguageDef name"
    );
    assert_eq!(
        plan.definition_fingerprint(),
        CalculatorLanguage
            .metadata()
            .definition_fingerprint()
            .expect("generated Calculator must expose its definition fingerprint"),
        "plan fingerprint built from definition_source() must equal the generated fingerprint"
    );
    PlannedRhoBackend::from_plan(plan)
}

fn stage_fingerprint(backend: &PlannedRhoBackend) -> String {
    backend.plan().definition_fingerprint().to_string()
}

fn invocation_stage<F>(backend: &PlannedRhoBackend, compiler: F) -> RhoInvocationCompilerStage<F> {
    RhoInvocationCompilerStage::new(stage_fingerprint(backend), compiler)
}

fn complete_dovetail_report_for(term: &dyn Term) -> Result<RuntimeDovetailRunReport, String> {
    let key = format!("calculator:{}", term).into_bytes();
    Ok(RuntimeDovetailRunReport {
        roots: vec![key.clone()],
        root_ordinals: vec![0],
        terms: vec![RuntimeDovetailTermRecord {
            ordinal: 0,
            class_id: 0,
            key,
            op_display: format!("{}", term),
            weight_display: "0".to_string(),
            is_root: true,
        }],
        derivation_edges: Vec::new(),
        completeness: RuntimeDovetailCompleteness::Complete,
    })
}

fn bounded_dovetail_report_for(term: &dyn Term) -> Result<RuntimeDovetailRunReport, String> {
    let mut report = complete_dovetail_report_for(term)?;
    report.completeness = RuntimeDovetailCompleteness::BoundedByCycleCut;
    Ok(report)
}

fn malformed_dovetail_report_for(term: &dyn Term) -> Result<RuntimeDovetailRunReport, String> {
    let mut report = complete_dovetail_report_for(term)?;
    report.root_ordinals[0] = 1;
    Ok(report)
}

fn generated_calculator_dovetail_report_for(
    term: &dyn Term,
) -> Result<RuntimeDovetailRunReport, String> {
    CalculatorLanguage::dovetail_report_for(term, 64, 1_000_000)
}

fn int_literal(term: &Int) -> Result<i64, String> {
    match term {
        Int::NumLit(value) => Ok(i64::from(*value)),
        other => Err(format!("Rho calculator bridge needs ground integer literals, got {other:?}")),
    }
}

fn bool_literal(term: &Bool) -> Result<bool, String> {
    match term {
        Bool::BoolLit(value) => Ok(*value),
        other => Err(format!("Rho calculator bridge needs ground boolean literals, got {other:?}")),
    }
}

fn string_literal(term: &Str) -> Result<String, String> {
    match term {
        Str::StringLit(value) => Ok(value.clone()),
        other => Err(format!("Rho calculator bridge needs ground string literals, got {other:?}")),
    }
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
    let invocation = CalculatorLanguage::rho_scalar_contract_invocation_to(term, "OUT")?;
    build_scalar_contract_invocation_from_contract(invocation)
        .map_err(|err| format!("failed to normalize generated Rho scalar invocation: {err}"))
}

fn calculator_invocation_from_dovetail(
    term: &dyn Term,
    report: &RuntimeDovetailRunReport,
) -> Result<RhoBackendInvocation, String> {
    let invocation =
        CalculatorLanguage::rho_scalar_contract_invocation_from_dovetail_to(term, report, "OUT")?;
    build_scalar_contract_invocation_from_contract(invocation)
        .map_err(|err| format!("failed to normalize generated Dovetail-to-Rho invocation: {err}"))
}

fn calculator_call_by_need_invocation(term: &dyn Term) -> Result<RhoBackendInvocation, String> {
    if let Ok(int) = calculator_int(term) {
        return match int {
            Int::AddInt(left, right) => need_int_binary("AddInt", left, right, |a, b| Ok(a + b)),
            Int::SubInt(left, right) => need_int_binary("SubInt", left, right, |a, b| Ok(a - b)),
            Int::MulInt(left, right) => need_int_binary("MulInt", left, right, |a, b| Ok(a * b)),
            Int::DivInt(left, right) => need_int_binary("DivInt", left, right, checked_div),
            Int::ModInt(left, right) => need_int_binary("ModInt", left, right, checked_rem),
            other => Err(format!("calculator CBN bridge has no Int invocation for {other:?}")),
        };
    }

    if let Ok(bool_term) = calculator_bool(term) {
        return match bool_term {
            Bool::EqInt(left, right) => need_int_predicate("EqInt", left, right, |a, b| a == b),
            Bool::NeInt(left, right) => need_int_predicate("NeInt", left, right, |a, b| a != b),
            Bool::LtInt(left, right) => need_int_predicate("LtInt", left, right, |a, b| a < b),
            Bool::GtInt(left, right) => need_int_predicate("GtInt", left, right, |a, b| a > b),
            Bool::LtEqInt(left, right) => need_int_predicate("LtEqInt", left, right, |a, b| a <= b),
            Bool::GtEqInt(left, right) => need_int_predicate("GtEqInt", left, right, |a, b| a >= b),
            Bool::EqBool(left, right) => need_bool_predicate("EqBool", left, right, |a, b| a == b),
            Bool::NeBool(left, right) => need_bool_predicate("NeBool", left, right, |a, b| a != b),
            Bool::LtBool(left, right) => need_bool_predicate("LtBool", left, right, |a, b| !a && b),
            Bool::GtBool(left, right) => need_bool_predicate("GtBool", left, right, |a, b| a && !b),
            Bool::LtEqBool(left, right) => {
                need_bool_predicate("LtEqBool", left, right, |a, b| !a || b)
            },
            Bool::GtEqBool(left, right) => {
                need_bool_predicate("GtEqBool", left, right, |a, b| a || !b)
            },
            Bool::EqStr(left, right) => need_string_predicate("EqStr", left, right, |a, b| a == b),
            Bool::NeStr(left, right) => need_string_predicate("NeStr", left, right, |a, b| a != b),
            Bool::LtStr(left, right) => need_string_predicate("LtStr", left, right, |a, b| a < b),
            Bool::GtStr(left, right) => need_string_predicate("GtStr", left, right, |a, b| a > b),
            Bool::LtEqStr(left, right) => {
                need_string_predicate("LtEqStr", left, right, |a, b| a <= b)
            },
            Bool::GtEqStr(left, right) => {
                need_string_predicate("GtEqStr", left, right, |a, b| a >= b)
            },
            Bool::And(left, right) => need_bool_predicate("And", left, right, |a, b| a && b),
            Bool::Or(left, right) => need_bool_predicate("Or", left, right, |a, b| a || b),
            Bool::Not(value) => {
                let value = bool_literal(value.as_ref())?;
                plan_need(RhoAstLiteral::Bool(!value), "Not")
            },
            other => Err(format!("calculator CBN bridge has no Bool invocation for {other:?}")),
        };
    }

    match calculator_str(term)? {
        Str::Concat(left, right) => {
            need_string_binary("Concat", left, right, |a, b| format!("{a}{b}"))
        },
        Str::AddStr(left, right) => {
            need_string_binary("AddStr", left, right, |a, b| format!("{a}{b}"))
        },
        other => Err(format!("calculator CBN bridge has no Str invocation for {other:?}")),
    }
}

fn checked_div(left: i64, right: i64) -> Result<i64, String> {
    if right == 0 {
        Err("calculator CBN bridge cannot divide by zero".to_string())
    } else {
        Ok(left / right)
    }
}

fn checked_rem(left: i64, right: i64) -> Result<i64, String> {
    if right == 0 {
        Err("calculator CBN bridge cannot take remainder by zero".to_string())
    } else {
        Ok(left % right)
    }
}

fn need_int_binary(
    marker: &str,
    left: &Int,
    right: &Int,
    op: impl FnOnce(i64, i64) -> Result<i64, String>,
) -> Result<RhoBackendInvocation, String> {
    let left = int_literal(left)?;
    let right = int_literal(right)?;
    plan_need(RhoAstLiteral::Int(op(left, right)?), marker)
}

fn need_int_predicate(
    marker: &str,
    left: &Int,
    right: &Int,
    op: impl FnOnce(i64, i64) -> bool,
) -> Result<RhoBackendInvocation, String> {
    let left = int_literal(left)?;
    let right = int_literal(right)?;
    plan_need(RhoAstLiteral::Bool(op(left, right)), marker)
}

fn need_bool_predicate(
    marker: &str,
    left: &Bool,
    right: &Bool,
    op: impl FnOnce(bool, bool) -> bool,
) -> Result<RhoBackendInvocation, String> {
    let left = bool_literal(left)?;
    let right = bool_literal(right)?;
    plan_need(RhoAstLiteral::Bool(op(left, right)), marker)
}

fn need_string_binary(
    marker: &str,
    left: &Str,
    right: &Str,
    op: impl FnOnce(&str, &str) -> String,
) -> Result<RhoBackendInvocation, String> {
    let left = string_literal(left)?;
    let right = string_literal(right)?;
    plan_need(RhoAstLiteral::String(op(&left, &right)), marker)
}

fn need_string_predicate(
    marker: &str,
    left: &Str,
    right: &Str,
    op: impl FnOnce(&str, &str) -> bool,
) -> Result<RhoBackendInvocation, String> {
    let left = string_literal(left)?;
    let right = string_literal(right)?;
    plan_need(RhoAstLiteral::Bool(op(&left, &right)), marker)
}

fn plan_need(value: RhoAstLiteral, eval_marker: &str) -> Result<RhoBackendInvocation, String> {
    let spec = CallByNeedThunkSpec::new(
        CallByNeedInitialState::Cold,
        value,
        eval_marker,
        "NEED_OUT",
        "NEED_EVAL",
    )
    .map_err(|err| format!("failed to build calculator CBN thunk spec: {err:?}"))?;
    let plan = plan_call_by_need_thunk_with_spec(spec, CallByNeedBudget::new(2, 1))
        .map_err(|err| format!("failed to plan calculator CBN thunk: {err:?}"))?;
    Ok(RhoBackendInvocation::RunCallByNeedThunk { plan: Box::new(plan) })
}

fn planned_need_spec_for(snippet: &str) -> (RhoAstLiteral, String) {
    let term = CalculatorLanguage
        .parse_term(snippet)
        .unwrap_or_else(|err| panic!("calculator parse failed for {snippet:?}: {err}"));
    match calculator_call_by_need_invocation(term.as_ref())
        .unwrap_or_else(|err| panic!("CBN invocation failed for {snippet:?}: {err}"))
    {
        RhoBackendInvocation::RunCallByNeedThunk { plan } => {
            (plan.spec().value().clone(), plan.spec().eval_marker().to_string())
        },
        other => panic!("expected CBN thunk invocation for {snippet:?}, got {other:?}"),
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct NeedScalarCase {
    snippet: String,
    expected_value: RhoAstLiteral,
    expected_marker: &'static str,
}

fn need_case(
    snippet: impl Into<String>,
    expected_value: RhoAstLiteral,
    expected_marker: &'static str,
) -> NeedScalarCase {
    NeedScalarCase {
        snippet: snippet.into(),
        expected_value,
        expected_marker,
    }
}

fn scalar_need_cases() -> Vec<NeedScalarCase> {
    let mut cases = Vec::new();
    let ints = [0_i64, 1, 3];
    for left in ints {
        for right in ints {
            cases.push(need_case(
                format!("{left} + {right}"),
                RhoAstLiteral::Int(left + right),
                "AddInt",
            ));
            cases.push(need_case(
                format!("{left} - {right}"),
                RhoAstLiteral::Int(left - right),
                "SubInt",
            ));
            cases.push(need_case(
                format!("{left} * {right}"),
                RhoAstLiteral::Int(left * right),
                "MulInt",
            ));
            if right != 0 {
                cases.push(need_case(
                    format!("{left} / {right}"),
                    RhoAstLiteral::Int(left / right),
                    "DivInt",
                ));
                cases.push(need_case(
                    format!("{left} % {right}"),
                    RhoAstLiteral::Int(left % right),
                    "ModInt",
                ));
            }
            cases.push(need_case(
                format!("{left} == {right}"),
                RhoAstLiteral::Bool(left == right),
                "EqInt",
            ));
            cases.push(need_case(
                format!("{left} != {right}"),
                RhoAstLiteral::Bool(left != right),
                "NeInt",
            ));
            cases.push(need_case(
                format!("{left} < {right}"),
                RhoAstLiteral::Bool(left < right),
                "LtInt",
            ));
            cases.push(need_case(
                format!("{left} > {right}"),
                RhoAstLiteral::Bool(left > right),
                "GtInt",
            ));
            cases.push(need_case(
                format!("{left} <= {right}"),
                RhoAstLiteral::Bool(left <= right),
                "LtEqInt",
            ));
            cases.push(need_case(
                format!("{left} >= {right}"),
                RhoAstLiteral::Bool(left >= right),
                "GtEqInt",
            ));
        }
    }

    let bools = [false, true];
    for left in bools {
        for right in bools {
            cases.push(need_case(
                format!("{left} == {right}"),
                RhoAstLiteral::Bool(left == right),
                "EqBool",
            ));
            cases.push(need_case(
                format!("{left} != {right}"),
                RhoAstLiteral::Bool(left != right),
                "NeBool",
            ));
            cases.push(need_case(
                format!("{left} < {right}"),
                RhoAstLiteral::Bool(!left && right),
                "LtBool",
            ));
            cases.push(need_case(
                format!("{left} > {right}"),
                RhoAstLiteral::Bool(left && !right),
                "GtBool",
            ));
            cases.push(need_case(
                format!("{left} <= {right}"),
                RhoAstLiteral::Bool(!left || right),
                "LtEqBool",
            ));
            cases.push(need_case(
                format!("{left} >= {right}"),
                RhoAstLiteral::Bool(left || !right),
                "GtEqBool",
            ));
            cases.push(need_case(
                format!("{left} and {right}"),
                RhoAstLiteral::Bool(left && right),
                "And",
            ));
            cases.push(need_case(
                format!("{left} or {right}"),
                RhoAstLiteral::Bool(left || right),
                "Or",
            ));
        }
        cases.push(need_case(format!("not {left}"), RhoAstLiteral::Bool(!left), "Not"));
    }

    let strings = ["", "a", "hello"];
    for left in strings {
        for right in strings {
            let left_lit = calculator_string_literal(left);
            let right_lit = calculator_string_literal(right);
            cases.push(need_case(
                format!("{left_lit} ++ {right_lit}"),
                RhoAstLiteral::String(format!("{left}{right}")),
                "Concat",
            ));
            cases.push(need_case(
                format!("{left_lit} + {right_lit}"),
                RhoAstLiteral::String(format!("{left}{right}")),
                "AddStr",
            ));
            cases.push(need_case(
                format!("{left_lit} == {right_lit}"),
                RhoAstLiteral::Bool(left == right),
                "EqStr",
            ));
            cases.push(need_case(
                format!("{left_lit} != {right_lit}"),
                RhoAstLiteral::Bool(left != right),
                "NeStr",
            ));
            cases.push(need_case(
                format!("{left_lit} < {right_lit}"),
                RhoAstLiteral::Bool(left < right),
                "LtStr",
            ));
            cases.push(need_case(
                format!("{left_lit} > {right_lit}"),
                RhoAstLiteral::Bool(left > right),
                "GtStr",
            ));
            cases.push(need_case(
                format!("{left_lit} <= {right_lit}"),
                RhoAstLiteral::Bool(left <= right),
                "LtEqStr",
            ));
            cases.push(need_case(
                format!("{left_lit} >= {right_lit}"),
                RhoAstLiteral::Bool(left >= right),
                "GtEqStr",
            ));
        }
    }

    cases
}

fn calculator_string_literal(value: &str) -> String {
    format!("{:?}", value)
}

fn ascent_normal_form_displays_for(snippet: &str) -> Vec<String> {
    mettail_runtime::clear_var_cache();
    let term = CalculatorLanguage
        .parse_term(snippet)
        .unwrap_or_else(|err| {
            panic!("calculator parse failed for Ascent golden {snippet:?}: {err}")
        });
    let results = CalculatorLanguage
        .run_ascent(term.as_ref())
        .unwrap_or_else(|err| panic!("calculator Ascent run failed for {snippet:?}: {err}"));
    let mut displays = results
        .normal_forms()
        .iter()
        .map(|normal_form| normal_form.display.clone())
        .collect::<Vec<_>>();
    displays.sort();
    displays.dedup();
    displays
}

fn rho_literal_calculator_display(value: &RhoAstLiteral) -> String {
    match value {
        RhoAstLiteral::Int(value) => value.to_string(),
        RhoAstLiteral::Bool(value) => value.to_string(),
        RhoAstLiteral::String(value) => calculator_string_literal(value),
        other => {
            panic!("calculator scalar CBN parity only covers Int, Bool, and Str, got {other:?}")
        },
    }
}

#[test]
fn call_by_need_planning_preserves_typed_payloads_for_scalar_families() {
    for case in scalar_need_cases() {
        let (value, marker) = planned_need_spec_for(&case.snippet);
        assert_eq!(value, case.expected_value, "typed CBN value mismatch for {:?}", case.snippet);
        assert_eq!(marker, case.expected_marker, "CBN eval marker mismatch for {:?}", case.snippet);
    }
}

#[test]
fn call_by_need_plans_match_ascent_golden_for_supported_scalar_families() {
    for case in scalar_need_cases() {
        let (value, marker) = planned_need_spec_for(&case.snippet);
        assert_eq!(
            marker, case.expected_marker,
            "CBN eval marker mismatch before golden comparison for {:?}",
            case.snippet
        );
        assert_eq!(
            value, case.expected_value,
            "typed CBN value mismatch before golden comparison for {:?}",
            case.snippet
        );

        let expected_display = rho_literal_calculator_display(&value);
        let ascent_displays = ascent_normal_form_displays_for(&case.snippet);
        assert!(
            ascent_displays.contains(&expected_display),
            "CBN planned value for {:?} must match a generated Calculator Ascent normal form; expected display {:?}, Ascent normal forms {:?}",
            case.snippet,
            expected_display,
            ascent_displays
        );
    }
}

#[test]
fn rho_runtime_installer_derives_invocation_fingerprint_from_plan() {
    let backend = calculator_backend();
    let language = install_rho_runtime_backend(
        CalculatorLanguage,
        backend,
        calculator_invocation,
    )
    .expect("plan-derived Rho invocation stage should install on matching language");
    let term = language.parse_term("2 + 3").expect("calculator parse");

    assert_eq!(language.default_runtime_backend(), Some(RuntimeBackend::RhoMachine));
    assert!(language.supports_runtime_backend(RuntimeBackend::RhoMachine));
    assert!(!language.supports_runtime_backend(RuntimeBackend::Ascent));

    let report = language
        .run_default_backend_report(term.as_ref())
        .expect("installer-built Rho wrapper must execute the planned backend");
    assert_eq!(report.backend(), RuntimeBackend::RhoMachine);
    assert_eq!(report.artifact(), RuntimeBackendArtifact::RhoNormalizedAst);
    let out = report
        .observations_for_channel("OUT")
        .expect("Rho report must expose OUT observations");
    assert_eq!(out.values, vec![RuntimeObservationValue::Int(5)]);
}

#[test]
fn rho_runtime_backed_language_dispatches_default_report() {
    let backend = calculator_backend();
    let invocation = invocation_stage(&backend, calculator_invocation);
    let language =
        RhoRuntimeBackedLanguage::new(CalculatorLanguage, backend, invocation)
            .expect("Calculator plan should install on CalculatorLanguage");
    let term = language.parse_term("2 + 3").expect("calculator parse");

    assert_eq!(language.default_runtime_backend(), Some(RuntimeBackend::RhoMachine));
    assert!(language.supports_runtime_backend(RuntimeBackend::RhoMachine));
    assert!(!language.supports_runtime_backend(RuntimeBackend::Ascent));
    assert!(!language.supports_runtime_backend(RuntimeBackend::Dovetail));
    let static_capabilities = language.metadata().runtime_backends();
    assert!(
        static_capabilities.is_empty(),
        "Rho wrapper must not mutate substrate-neutral generated metadata"
    );

    let capabilities = language.runtime_backend_capabilities();
    assert_eq!(capabilities.len(), 1);
    assert_eq!(capabilities[0].backend, RuntimeBackend::RhoMachine);
    assert!(capabilities[0].is_default);

    let report = language
        .run_default_backend_report(term.as_ref())
        .expect("Rho default backend must return a runtime report");
    assert_eq!(report.backend(), RuntimeBackend::RhoMachine);
    assert_eq!(report.artifact(), RuntimeBackendArtifact::RhoNormalizedAst);

    let out = report
        .observations_for_channel("OUT")
        .expect("Rho report must expose OUT observations");
    assert_eq!(out.values, vec![RuntimeObservationValue::Int(5)]);

    let ascent_err = language
        .run_backend_report(RuntimeBackend::Ascent, term.as_ref())
        .expect_err("production Rho wrapper must not expose Ascent");
    assert!(ascent_err.contains("legacy Ascent runtime is not exposed"), "{ascent_err}");

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
fn dovetail_rho_runtime_installer_derives_stage_fingerprints_from_plan() {
    let language = install_dovetail_rho_runtime_backend(
        CalculatorLanguage,
        calculator_backend(),
        generated_calculator_dovetail_report_for,
        calculator_invocation_from_dovetail,
    )
    .expect("plan-derived Dovetail and Rho stages should install on matching language");
    let term = language.parse_term("2 + 3").expect("calculator parse");

    assert_eq!(language.default_runtime_backend(), Some(RuntimeBackend::RhoMachine));
    assert!(language.supports_runtime_backend(RuntimeBackend::RhoMachine));
    assert!(language.supports_runtime_backend(RuntimeBackend::Dovetail));
    assert!(!language.supports_runtime_backend(RuntimeBackend::Ascent));

    let dovetail_report = language
        .run_backend_report(RuntimeBackend::Dovetail, term.as_ref())
        .expect("installer-built wrapper must expose the checked Dovetail intermediate");
    assert_eq!(dovetail_report.backend(), RuntimeBackend::Dovetail);
    assert_eq!(dovetail_report.artifact(), RuntimeBackendArtifact::DovetailRunReport);
    let RuntimeBackendOutput::Dovetail(dovetail_output) = dovetail_report.into_output() else {
        panic!("Dovetail backend must return Dovetail report output");
    };
    assert!(dovetail_output.is_complete());
    assert!(dovetail_output.root_count() >= 1);
    assert!(
        dovetail_output
            .terms
            .iter()
            .any(|term| term.op_display == "5"),
        "complete Dovetail report must include the normalized integer literal root: {dovetail_output:?}"
    );

    let rho_report = language
        .run_default_backend_report(term.as_ref())
        .expect("installer-built wrapper must execute Rho after checked Dovetail");
    assert_eq!(rho_report.backend(), RuntimeBackend::RhoMachine);
    assert_eq!(rho_report.artifact(), RuntimeBackendArtifact::RhoNormalizedAst);
    let out = rho_report
        .observations_for_channel("OUT")
        .expect("Rho report must expose OUT observations");
    assert_eq!(out.values, vec![RuntimeObservationValue::Int(5)]);
}

#[test]
fn dovetail_rho_runtime_backed_language_checks_dovetail_before_rho_execution() {
    let backend = calculator_backend();
    let fingerprint = stage_fingerprint(&backend);
    let language = DovetailRhoRuntimeBackedLanguage::new(
        CalculatorLanguage,
        backend,
        DovetailCompilerStage::new(fingerprint.clone(), generated_calculator_dovetail_report_for),
        RhoInvocationCompilerStage::new(fingerprint, calculator_invocation_from_dovetail),
    )
    .expect("Calculator Dovetail+Rho plan should install on CalculatorLanguage");
    let term = language.parse_term("2 + 3").expect("calculator parse");

    assert_eq!(language.default_runtime_backend(), Some(RuntimeBackend::RhoMachine));
    assert!(language.supports_runtime_backend(RuntimeBackend::RhoMachine));
    assert!(language.supports_runtime_backend(RuntimeBackend::Dovetail));
    assert!(!language.supports_runtime_backend(RuntimeBackend::Ascent));
    assert_eq!(language.runtime_backend_capabilities().len(), 2);
    assert_eq!(language.runtime_backend_capabilities()[0].backend, RuntimeBackend::RhoMachine);
    assert!(language.runtime_backend_capabilities()[0].is_default);
    assert_eq!(language.runtime_backend_capabilities()[1].backend, RuntimeBackend::Dovetail);
    assert!(!language.runtime_backend_capabilities()[1].is_default);

    let dovetail_report = language
        .run_backend_report(RuntimeBackend::Dovetail, term.as_ref())
        .expect("explicit Dovetail report should expose the checked intermediate");
    assert_eq!(dovetail_report.backend(), RuntimeBackend::Dovetail);
    assert_eq!(dovetail_report.artifact(), RuntimeBackendArtifact::DovetailRunReport);
    let RuntimeBackendOutput::Dovetail(dovetail_output) = dovetail_report.into_output() else {
        panic!("Dovetail backend must return Dovetail report output");
    };
    assert!(dovetail_output.is_complete());
    assert!(dovetail_output.root_count() >= 1);
    assert!(
        dovetail_output
            .terms
            .iter()
            .any(|term| term.op_display == "5"),
        "complete Dovetail report must include the normalized integer literal root: {dovetail_output:?}"
    );

    let rho_report = language
        .run_default_backend_report(term.as_ref())
        .expect("Rho default backend must execute after checked Dovetail compilation");
    assert_eq!(rho_report.backend(), RuntimeBackend::RhoMachine);
    assert_eq!(rho_report.artifact(), RuntimeBackendArtifact::RhoNormalizedAst);
    let out = rho_report
        .observations_for_channel("OUT")
        .expect("Rho report must expose OUT observations");
    assert_eq!(out.values, vec![RuntimeObservationValue::Int(5)]);

    let ascent_err = language
        .run_backend_report(RuntimeBackend::Ascent, term.as_ref())
        .expect_err("Dovetail+Rho production wrapper must not expose Ascent");
    assert!(ascent_err.contains("legacy Ascent runtime is not exposed"), "{ascent_err}");

    let mut facts = SeedFacts::new();
    facts.insert("certified".to_string(), vec![vec!["2 + 3".to_string()]]);
    let seeded_err = language
        .run_default_backend_report_with_facts(term.as_ref(), &facts)
        .expect_err("Dovetail+Rho path must reject Ascent-shaped fact seeding");
    assert!(
        seeded_err.contains("does not accept Ascent-shaped seeded facts"),
        "{seeded_err}"
    );
}

#[test]
fn dovetail_rho_runtime_installer_accepts_real_plan_on_full_calculator() {
    // The plan is now built from the REAL `CalculatorLanguage` augmented
    // `LanguageDef` (reconstructed from `definition_source()`), so its
    // fingerprint equals the generated Calculator's. The installer therefore
    // accepts it on the real `CalculatorLanguage` — no fingerprint-spoofing
    // shim is required.
    let language = install_dovetail_rho_runtime_backend(
        CalculatorLanguage,
        calculator_backend(),
        generated_calculator_dovetail_report_for,
        calculator_invocation_from_dovetail,
    )
    .expect("real Calculator plan must install on the full generated CalculatorLanguage");
    let term = language.parse_term("2 + 3").expect("calculator parse");
    let report = language
        .run_default_backend_report(term.as_ref())
        .expect("installer-built real-Calculator wrapper must execute Rho after checked Dovetail");
    assert_eq!(report.backend(), RuntimeBackend::RhoMachine);
    let out = report
        .observations_for_channel("OUT")
        .expect("Rho report must expose OUT observations");
    assert_eq!(out.values, vec![RuntimeObservationValue::Int(5)]);
}

#[test]
fn dovetail_rho_runtime_backed_language_accepts_real_plan_on_full_calculator() {
    let backend = calculator_backend();
    let fingerprint = stage_fingerprint(&backend);
    let language = DovetailRhoRuntimeBackedLanguage::new(
        CalculatorLanguage,
        backend,
        DovetailCompilerStage::new(fingerprint.clone(), generated_calculator_dovetail_report_for),
        RhoInvocationCompilerStage::new(fingerprint, calculator_invocation_from_dovetail),
    )
    .expect("real Calculator plan must install on the full generated CalculatorLanguage");
    let term = language.parse_term("2 + 3").expect("calculator parse");
    let report = language
        .run_default_backend_report(term.as_ref())
        .expect("real-Calculator Dovetail+Rho wrapper must execute Rho after checked Dovetail");
    assert_eq!(report.backend(), RuntimeBackend::RhoMachine);
    let out = report
        .observations_for_channel("OUT")
        .expect("Rho report must expose OUT observations");
    assert_eq!(out.values, vec![RuntimeObservationValue::Int(5)]);
}

#[test]
fn dovetail_rho_runtime_backed_language_rejects_bad_dovetail_stage() {
    let bounded_backend = calculator_backend();
    let bounded_fingerprint = stage_fingerprint(&bounded_backend);
    let bounded_language = DovetailRhoRuntimeBackedLanguage::new(
        CalculatorLanguage,
        bounded_backend,
        DovetailCompilerStage::new(bounded_fingerprint.clone(), bounded_dovetail_report_for),
        RhoInvocationCompilerStage::new(bounded_fingerprint, calculator_invocation_from_dovetail),
    )
    .expect("Calculator Dovetail+Rho plan should install on CalculatorLanguage");
    assert_eq!(
        bounded_language.default_runtime_backend(),
        Some(RuntimeBackend::RhoMachine),
        "capability exposure is an installation property"
    );
    assert!(bounded_language.supports_runtime_backend(RuntimeBackend::RhoMachine));
    assert!(bounded_language.supports_runtime_backend(RuntimeBackend::Dovetail));
    assert!(!bounded_language.supports_runtime_backend(RuntimeBackend::Ascent));
    let term = bounded_language
        .parse_term("2 + 3")
        .expect("calculator parse");
    let bounded_err = bounded_language
        .run_default_backend_report(term.as_ref())
        .expect_err("bounded Dovetail reports must not reach Rho execution");
    assert!(
        bounded_err.contains("produced incomplete report: BoundedByCycleCut"),
        "{bounded_err}"
    );

    let malformed_backend = calculator_backend();
    let malformed_fingerprint = stage_fingerprint(&malformed_backend);
    let malformed_language = DovetailRhoRuntimeBackedLanguage::new(
        CalculatorLanguage,
        malformed_backend,
        DovetailCompilerStage::new(malformed_fingerprint.clone(), malformed_dovetail_report_for),
        RhoInvocationCompilerStage::new(malformed_fingerprint, calculator_invocation_from_dovetail),
    )
    .expect("Calculator Dovetail+Rho plan should install on CalculatorLanguage");
    let malformed_err = malformed_language
        .run_default_backend_report(term.as_ref())
        .expect_err("malformed Dovetail reports must not reach Rho execution");
    assert!(malformed_err.contains("produced malformed report"), "{malformed_err}");
    assert!(malformed_err.contains("term ordinal 1"), "{malformed_err}");
}

#[test]
fn rho_runtime_backed_language_dispatches_call_by_need_thunk_report() {
    let backend = calculator_backend();
    let invocation = invocation_stage(&backend, calculator_call_by_need_invocation);
    let language =
        RhoRuntimeBackedLanguage::new(CalculatorLanguage, backend, invocation)
            .expect("Calculator plan should install on CalculatorLanguage");

    let cases = [
        ("2 + 3", RuntimeObservationValue::Int(5), "AddInt"),
        ("2 == 2", RuntimeObservationValue::Bool(true), "EqInt"),
        (
            r#""rho" ++ "net""#,
            RuntimeObservationValue::Text("rhonet".to_string()),
            "Concat",
        ),
    ];

    for (snippet, expected_value, expected_marker) in cases {
        let term = language.parse_term(snippet).expect("calculator parse");

        let report = language
            .run_default_backend_report(term.as_ref())
            .expect("Rho default backend must execute the planned CBN thunk invocation");
        assert_eq!(report.backend(), RuntimeBackend::RhoMachine);
        assert_eq!(report.artifact(), RuntimeBackendArtifact::RhoNormalizedAst);

        let out = report
            .observations_for_channel("NEED_OUT")
            .expect("CBN report must expose generated value observations");
        assert_eq!(
            out.values,
            vec![expected_value.clone(), expected_value],
            "CBN report must preserve typed generated value observations for {snippet:?}"
        );

        let eval = report
            .observations_for_channel("NEED_EVAL")
            .expect("CBN report must expose generated evaluation trace observations");
        assert_eq!(
            eval.values,
            vec![RuntimeObservationValue::Text(expected_marker.to_string())],
            "CBN report must preserve textual eval marker for {snippet:?}"
        );
    }
}

#[test]
fn rho_runtime_backed_language_accepts_real_plan_on_full_calculator() {
    // Built from the REAL Calculator augmented def: the plan fingerprint equals
    // the generated Calculator's, so it installs and executes on the real
    // `CalculatorLanguage`.
    let backend = calculator_backend();
    let invocation = invocation_stage(&backend, calculator_invocation);
    let language = RhoRuntimeBackedLanguage::new(CalculatorLanguage, backend, invocation)
        .expect("real Calculator plan must install on the full generated CalculatorLanguage");
    let term = language.parse_term("2 + 3").expect("calculator parse");
    let report = language
        .run_default_backend_report(term.as_ref())
        .expect("real-Calculator Rho wrapper must execute the planned backend");
    assert_eq!(report.backend(), RuntimeBackend::RhoMachine);
    let out = report
        .observations_for_channel("OUT")
        .expect("Rho report must expose OUT observations");
    assert_eq!(out.values, vec![RuntimeObservationValue::Int(5)]);
}

#[test]
fn rho_runtime_backed_language_rejects_mismatched_invocation_stage() {
    let backend = calculator_backend();
    let result = RhoRuntimeBackedLanguage::new(
        CalculatorLanguage,
        backend,
        RhoInvocationCompilerStage::new("different-definition", calculator_invocation),
    );
    let err = match result {
        Ok(_) => panic!("mismatched Rho invocation compiler must not install"),
        Err(err) => err,
    };
    assert!(
        matches!(err, RhoRuntimeBackedLanguageError::InvocationCompilerDefinitionMismatch { .. }),
        "{err}"
    );
    assert!(err.to_string().contains("different-definition"), "{err}");
}

#[test]
fn rho_runtime_backed_language_rejects_cross_language_plan_installation() {
    // Reconstruct the REAL Calculator def but rename it to `NotCalculator`, so
    // the plan's `language_name()` no longer matches `CalculatorLanguage`. The
    // install must fail with `LanguagePlanMismatch` (name-level guard), proving
    // the real-plan path still rejects a foreign-language plan.
    let source = CalculatorLanguage
        .metadata()
        .definition_source()
        .expect("generated CalculatorLanguage must expose its definition_source");
    let renamed_source = source.replacen("name: Calculator", "name: NotCalculator", 1);
    assert_ne!(
        renamed_source, source,
        "rename must take effect; the macro body must contain `name: Calculator`"
    );
    let def = reconstruct_language_def(&renamed_source)
        .expect("renamed Calculator source must reconstruct as a LanguageDef");
    let requirements = RhoDefaultBackendRequirements {
        coverage: RhoCoverageEvidence::CoveredRejectedRules(native_handler_dispositions_for(&def)),
        guard_coverage: RhoGuardCoverageEvidence::NoGuardObligations,
    };
    let plan = plan_rho_default_backend(&def, requirements)
        .expect("renamed Calculator def must still pass the Rho-default gate");
    let backend = PlannedRhoBackend::from_plan(plan);
    let invocation = invocation_stage(&backend, calculator_invocation);
    let result = RhoRuntimeBackedLanguage::new(CalculatorLanguage, backend, invocation);
    assert!(result.is_err(), "a NotCalculator plan must not install on CalculatorLanguage");
    let err = result
        .err()
        .expect("mismatch must produce an installation error");

    assert_eq!(
        err,
        mettail_rho_runtime::RhoRuntimeBackedLanguageError::LanguagePlanMismatch {
            language_name: "Calculator".to_string(),
            plan_language_name: "NotCalculator".to_string(),
        }
    );
    assert!(
        err.to_string()
            .contains("cannot be installed on generated language Calculator"),
        "{err}"
    );
}

/// THE FINGERPRINT GUARANTEE (Step 5): reconstructing the real
/// `CalculatorLanguage` augmented `LanguageDef` from its
/// `definition_source()` and fingerprinting it reproduces — exactly — the
/// generated `definition_fingerprint()`. This is what lets a Rho/Dovetail plan
/// be installed on the REAL `CalculatorLanguage` without a fingerprint-spoofing
/// shim.
#[test]
fn reconstructed_definition_source_fingerprint_matches_generated_fingerprint() {
    let source = CalculatorLanguage
        .metadata()
        .definition_source()
        .expect("generated CalculatorLanguage must expose its definition_source");
    let reconstructed = reconstruct_language_def(source)
        .expect("CalculatorLanguage definition_source must reconstruct as a LanguageDef");
    assert_eq!(
        language_definition_fingerprint(&reconstructed),
        CalculatorLanguage
            .metadata()
            .definition_fingerprint()
            .expect("generated CalculatorLanguage must expose its definition fingerprint"),
    );
}
