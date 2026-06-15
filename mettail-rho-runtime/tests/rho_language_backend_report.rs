//! Verifies that a generated language can be wrapped as a Rho-default runtime
//! backend without making the generated language crate depend on
//! `mettail-rho-runtime`.

use std::any::Any;
use std::sync::OnceLock;

use mettail_ast::identity::language_definition_fingerprint;
use mettail_ast::language::LanguageDef;
use mettail_languages::calculator::{
    Bool, CalculatorLanguage, CalculatorTerm, CalculatorTermInner, Int, Str,
};
use mettail_rho_codegen::{
    plan_call_by_need_thunk_with_spec, plan_rho_default_backend, CallByNeedBudget,
    CallByNeedInitialState, CallByNeedThunkSpec, RhoAstLiteral, RhoCoverageEvidence,
    RhoDefaultBackendRequirements, RhoGuardCoverageEvidence,
};
use mettail_rho_runtime::{
    build_scalar_contract_invocation_from_contract, install_dovetail_rho_runtime_backend,
    install_rho_runtime_backend, DovetailCompilerStage, DovetailRhoRuntimeBackedLanguage,
    PlannedRhoBackend, RhoBackendInvocation, RhoInvocationCompilerStage, RhoRuntimeBackedLanguage,
    RhoRuntimeBackedLanguageError,
};
use mettail_runtime::{
    AscentResults, Language, LanguageMetadata, RuntimeBackend, RuntimeBackendArtifact,
    RuntimeBackendOutput, RuntimeDovetailCompleteness, RuntimeDovetailRunReport,
    RuntimeDovetailTermRecord, RuntimeObservationValue, SeedFacts, Term, TermType, VarTypeInfo,
};

const CALC_RUN_FRAGMENT: &str = r#"
    name: Calculator,
    types {
        Proc
        ![i64] as Int
        ![bool] as Bool
        ![str] as Str
    }
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

fn passing_requirements() -> RhoDefaultBackendRequirements {
    RhoDefaultBackendRequirements {
        coverage: RhoCoverageEvidence::AllRulesLowered,
        guard_coverage: RhoGuardCoverageEvidence::NoGuardObligations,
    }
}

fn backend_from_fragment(fragment: &str) -> PlannedRhoBackend {
    let def = syn::parse_str::<LanguageDef>(fragment).expect("calculator fragment must parse");
    let plan = plan_rho_default_backend(&def, passing_requirements())
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

fn calculator_backend() -> PlannedRhoBackend {
    let backend = backend_from_fragment(CALC_RUN_FRAGMENT);
    assert_eq!(
        backend.plan().language_name(),
        "Calculator",
        "wrapper-installed Calculator plan must preserve its source LanguageDef name"
    );
    backend
}

fn calc_run_definition_fingerprint() -> &'static str {
    static FINGERPRINT: OnceLock<String> = OnceLock::new();
    FINGERPRINT
        .get_or_init(|| {
            let def = syn::parse_str::<LanguageDef>(CALC_RUN_FRAGMENT)
                .expect("calculator fragment must parse");
            language_definition_fingerprint(&def)
        })
        .as_str()
}

fn stage_fingerprint(backend: &PlannedRhoBackend) -> String {
    backend.plan().definition_fingerprint().to_string()
}

fn invocation_stage<F>(backend: &PlannedRhoBackend, compiler: F) -> RhoInvocationCompilerStage<F> {
    RhoInvocationCompilerStage::new(stage_fingerprint(backend), compiler)
}

struct FragmentMatchedCalculatorLanguage;

struct FragmentMatchedCalculatorMetadata;

static FRAGMENT_MATCHED_CALCULATOR_METADATA: FragmentMatchedCalculatorMetadata =
    FragmentMatchedCalculatorMetadata;

impl LanguageMetadata for FragmentMatchedCalculatorMetadata {
    fn name(&self) -> &'static str {
        CalculatorLanguage.metadata().name()
    }

    fn definition_fingerprint(&self) -> Option<&'static str> {
        Some(calc_run_definition_fingerprint())
    }

    fn types(&self) -> &'static [mettail_runtime::TypeDef] {
        CalculatorLanguage.metadata().types()
    }

    fn terms(&self) -> &'static [mettail_runtime::TermDef] {
        CalculatorLanguage.metadata().terms()
    }

    fn equations(&self) -> &'static [mettail_runtime::EquationDef] {
        CalculatorLanguage.metadata().equations()
    }

    fn rewrites(&self) -> &'static [mettail_runtime::RewriteDef] {
        CalculatorLanguage.metadata().rewrites()
    }

    fn runtime_backends(&self) -> &'static [mettail_runtime::BackendCapabilityDef] {
        CalculatorLanguage.metadata().runtime_backends()
    }

    fn logic_relations(&self) -> &'static [mettail_runtime::LogicRelationDef] {
        CalculatorLanguage.metadata().logic_relations()
    }

    fn logic_rules(&self) -> &'static [mettail_runtime::LogicRuleDef] {
        CalculatorLanguage.metadata().logic_rules()
    }

    fn builtin_predicates(&self) -> &'static [mettail_runtime::BuiltinPredicateDef] {
        CalculatorLanguage.metadata().builtin_predicates()
    }

    fn theories(&self) -> &'static [mettail_runtime::TheoryDef] {
        CalculatorLanguage.metadata().theories()
    }

    fn channels(&self) -> &'static [mettail_runtime::ChannelDef] {
        CalculatorLanguage.metadata().channels()
    }

    fn join_patterns(&self) -> &'static [mettail_runtime::JoinPatternDef] {
        CalculatorLanguage.metadata().join_patterns()
    }

    fn connectives(&self) -> &'static [mettail_runtime::ConnectiveDef] {
        CalculatorLanguage.metadata().connectives()
    }
}

impl Language for FragmentMatchedCalculatorLanguage {
    fn name(&self) -> &'static str {
        CalculatorLanguage.name()
    }

    fn metadata(&self) -> &'static dyn LanguageMetadata {
        &FRAGMENT_MATCHED_CALCULATOR_METADATA
    }

    fn parse_term(&self, input: &str) -> Result<Box<dyn Term>, String> {
        CalculatorLanguage.parse_term(input)
    }

    fn parse_term_for_env(&self, input: &str) -> Result<Box<dyn Term>, String> {
        CalculatorLanguage.parse_term_for_env(input)
    }

    fn run_ascent(&self, term: &dyn Term) -> Result<AscentResults, String> {
        CalculatorLanguage.run_ascent(term)
    }

    fn run_ascent_with_facts(
        &self,
        term: &dyn Term,
        facts: &SeedFacts,
    ) -> Result<AscentResults, String> {
        CalculatorLanguage.run_ascent_with_facts(term, facts)
    }

    fn try_direct_eval(&self, term: &dyn Term) -> Option<Box<dyn Term>> {
        CalculatorLanguage.try_direct_eval(term)
    }

    fn normalize_term(&self, term: &dyn Term) -> Box<dyn Term> {
        CalculatorLanguage.normalize_term(term)
    }

    fn format_term(&self, term: &dyn Term) -> String {
        CalculatorLanguage.format_term(term)
    }

    fn create_env(&self) -> Box<dyn Any + Send + Sync> {
        CalculatorLanguage.create_env()
    }

    fn add_to_env(&self, env: &mut dyn Any, name: &str, term: &dyn Term) -> Result<(), String> {
        CalculatorLanguage.add_to_env(env, name, term)
    }

    fn remove_from_env(&self, env: &mut dyn Any, name: &str) -> Result<bool, String> {
        CalculatorLanguage.remove_from_env(env, name)
    }

    fn clear_env(&self, env: &mut dyn Any) {
        CalculatorLanguage.clear_env(env)
    }

    fn substitute_env(&self, term: &dyn Term, env: &dyn Any) -> Result<Box<dyn Term>, String> {
        CalculatorLanguage.substitute_env(term, env)
    }

    fn substitute_env_preserve_structure(
        &self,
        term: &dyn Term,
        env: &dyn Any,
    ) -> Result<Box<dyn Term>, String> {
        CalculatorLanguage.substitute_env_preserve_structure(term, env)
    }

    fn list_env(&self, env: &dyn Any) -> Vec<(String, String, Option<String>)> {
        CalculatorLanguage.list_env(env)
    }

    fn set_env_comment(
        &self,
        env: &mut dyn Any,
        name: &str,
        comment: String,
    ) -> Result<(), String> {
        CalculatorLanguage.set_env_comment(env, name, comment)
    }

    fn is_env_empty(&self, env: &dyn Any) -> bool {
        CalculatorLanguage.is_env_empty(env)
    }

    fn get_env_term(&self, env: &dyn Any, name: &str) -> Option<Box<dyn Term>> {
        CalculatorLanguage.get_env_term(env, name)
    }

    fn infer_term_type(&self, term: &dyn Term) -> TermType {
        CalculatorLanguage.infer_term_type(term)
    }

    fn infer_var_types(&self, term: &dyn Term) -> Vec<VarTypeInfo> {
        CalculatorLanguage.infer_var_types(term)
    }

    fn infer_var_type(&self, term: &dyn Term, var_name: &str) -> Option<TermType> {
        CalculatorLanguage.infer_var_type(term, var_name)
    }
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
        FragmentMatchedCalculatorLanguage,
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
        RhoRuntimeBackedLanguage::new(FragmentMatchedCalculatorLanguage, backend, invocation)
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
        FragmentMatchedCalculatorLanguage,
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
        FragmentMatchedCalculatorLanguage,
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
fn dovetail_rho_runtime_installer_rejects_plan_for_different_generated_definition() {
    let result = install_dovetail_rho_runtime_backend(
        CalculatorLanguage,
        calculator_backend(),
        complete_dovetail_report_for,
        calculator_invocation_from_dovetail,
    );
    let err = match result {
        Ok(_) => panic!("fragment Rho plan must not install on the full generated Calculator"),
        Err(err) => err,
    };
    assert!(
        matches!(err, RhoRuntimeBackedLanguageError::LanguagePlanDefinitionMismatch { .. }),
        "{err}"
    );
}

#[test]
fn dovetail_rho_runtime_backed_language_rejects_fragment_plan_for_full_calculator() {
    let backend = calculator_backend();
    let fingerprint = stage_fingerprint(&backend);
    let result = DovetailRhoRuntimeBackedLanguage::new(
        CalculatorLanguage,
        backend,
        DovetailCompilerStage::new(fingerprint.clone(), complete_dovetail_report_for),
        RhoInvocationCompilerStage::new(fingerprint, calculator_invocation_from_dovetail),
    );
    let err = match result {
        Ok(_) => panic!("fragment Rho plan must not install on the full generated Calculator"),
        Err(err) => err,
    };
    assert!(
        matches!(err, RhoRuntimeBackedLanguageError::LanguagePlanDefinitionMismatch { .. }),
        "{err}"
    );
}

#[test]
fn dovetail_rho_runtime_backed_language_rejects_bad_dovetail_stage() {
    let bounded_backend = calculator_backend();
    let bounded_fingerprint = stage_fingerprint(&bounded_backend);
    let bounded_language = DovetailRhoRuntimeBackedLanguage::new(
        FragmentMatchedCalculatorLanguage,
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
        FragmentMatchedCalculatorLanguage,
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
        RhoRuntimeBackedLanguage::new(FragmentMatchedCalculatorLanguage, backend, invocation)
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
fn rho_runtime_backed_language_rejects_fragment_plan_for_full_calculator() {
    let backend = calculator_backend();
    let invocation = invocation_stage(&backend, calculator_invocation);
    let result = RhoRuntimeBackedLanguage::new(CalculatorLanguage, backend, invocation);
    let err = match result {
        Ok(_) => panic!("fragment Rho plan must not install on the full generated Calculator"),
        Err(err) => err,
    };
    assert!(
        matches!(err, RhoRuntimeBackedLanguageError::LanguagePlanDefinitionMismatch { .. }),
        "{err}"
    );
}

#[test]
fn rho_runtime_backed_language_rejects_mismatched_invocation_stage() {
    let backend = calculator_backend();
    let result = RhoRuntimeBackedLanguage::new(
        FragmentMatchedCalculatorLanguage,
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
    let mismatched_fragment =
        CALC_RUN_FRAGMENT.replacen("name: Calculator", "name: NotCalculator", 1);
    let backend = backend_from_fragment(&mismatched_fragment);
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
