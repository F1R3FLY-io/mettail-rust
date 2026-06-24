//! Integration test for the OSLF Phase 5 *temporal* wire.
//!
//! Verifies that [`SimulationRunner`](mettail_simulation::runner::SimulationRunner)
//! actually checks its configured `ltl_properties` against each run's execution
//! trace via the shipped [`check_trace_ltl`](mettail_simulation::temporal::check_trace_ltl)
//! pipeline, surfacing any `Violated` result as a
//! [`TraceOutcome::LtlViolation`] failure (and into
//! `CampaignResults::ltl_violations`).
//!
//! ## Why a self-contained mock language
//!
//! The `simulation` crate is depended on **by** `languages` (the per-language
//! `simulate_*` CLI binaries live there), so `simulation` cannot depend on
//! `languages` — a real `CalculatorLanguage` runner is therefore unavailable to
//! `simulation/tests/`. Instead, this test builds a minimal mock `Language`
//! whose Dovetail backend returns a fully-formed (shape-valid)
//! `RuntimeDovetailRunReport`, parameterized by the parsed input so a test can
//! deterministically produce either:
//!
//! - a **converging** trace — the report's root term is a literal constructor
//!   (`…Lit(<payload>)`), which the runner reduces to a
//!   [`TraceOutcome::NormalForm`]; its final step is in normal form, so
//!   `F(normal_form)` is *satisfied*; or
//! - a **non-converging** trace — the report's root term is a non-literal
//!   operator, which yields a [`TraceOutcome::RuntimeReport`] with no
//!   normal-form step, so `F(normal_form)` is *violated*.
//!
//! This exercises the real `run_to_normal_form` / `run_campaign` consume path
//! end-to-end without fabricating any backend evidence.

use std::any::Any;

use mettail_runtime::{
    AscentResults, BackendCapabilityDef, Language, LanguageMetadata, RuntimeBackend,
    RuntimeBackendReport, RuntimeDovetailCompleteness, RuntimeDovetailRunReport,
    RuntimeDovetailTermRecord, Term, TermType, VarTypeInfo,
};
use mettail_simulation::results::CampaignResults;
use mettail_simulation::runner::{SimulationConfig, SimulationRunner};
use mettail_simulation::trace::TraceOutcome;

// ════════════════════════════════════════════════════════════════════════════
// Mock term
// ════════════════════════════════════════════════════════════════════════════

/// A trivial term that simply carries its input string. The runner only needs
/// `Display` (for trace steps) and the `Term` object-safety methods.
#[derive(Debug, Clone)]
struct MockTerm(String);

impl std::fmt::Display for MockTerm {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}

impl Term for MockTerm {
    fn clone_box(&self) -> Box<dyn Term> {
        Box::new(self.clone())
    }

    fn term_id(&self) -> u64 {
        // Stable id; the BFS/normal-form picker is unused on the Dovetail path.
        1
    }

    fn term_eq(&self, other: &dyn Term) -> bool {
        other
            .as_any()
            .downcast_ref::<MockTerm>()
            .is_some_and(|other| self.0 == other.0)
    }

    fn as_any(&self) -> &dyn Any {
        self
    }
}

// ════════════════════════════════════════════════════════════════════════════
// Mock metadata + language (Dovetail default backend)
// ════════════════════════════════════════════════════════════════════════════

struct MockMetadata;

static DOVETAIL_BACKENDS: &[BackendCapabilityDef] = &[BackendCapabilityDef {
    backend: RuntimeBackend::Dovetail,
    is_default: true,
}];

impl LanguageMetadata for MockMetadata {
    fn name(&self) -> &'static str {
        "TemporalWireMock"
    }

    fn types(&self) -> &'static [mettail_runtime::TypeDef] {
        &[]
    }

    fn terms(&self) -> &'static [mettail_runtime::TermDef] {
        &[]
    }

    fn equations(&self) -> &'static [mettail_runtime::EquationDef] {
        &[]
    }

    fn rewrites(&self) -> &'static [mettail_runtime::RewriteDef] {
        &[]
    }

    fn runtime_backends(&self) -> &'static [BackendCapabilityDef] {
        DOVETAIL_BACKENDS
    }
}

static MOCK_METADATA: MockMetadata = MockMetadata;

/// A mock language whose Dovetail backend's report is selected by the input:
///
/// - input `"converge"` → root term `TemporalWireMock::Int::NumLit(8)`
///   (a literal) → runner extracts normal form `"8"`.
/// - any other input → root term `TemporalWireMock::Proc::Loop` (no literal)
///   → runner keeps a `RuntimeReport` (no normal form reached).
struct TemporalWireMockLanguage;

/// Build a structurally-valid single-root Dovetail report carrying the given
/// root `op_display`. One term, marked as root, ordinal 0, key `b"root"`, no
/// derivation edges, no rule firings, `Complete`.
fn single_root_report(op_display: &str) -> RuntimeDovetailRunReport {
    RuntimeDovetailRunReport {
        roots: vec![b"root".to_vec()],
        root_ordinals: vec![0],
        terms: vec![RuntimeDovetailTermRecord {
            ordinal: 0,
            class_id: 0,
            key: b"root".to_vec(),
            op_display: op_display.to_string(),
            weight_display: "1".to_string(),
            is_root: true,
            source_display: None,
        }],
        derivation_edges: Vec::new(),
        rule_firings: Vec::new(),
        completeness: RuntimeDovetailCompleteness::Complete,
    }
}

impl Language for TemporalWireMockLanguage {
    fn name(&self) -> &'static str {
        "TemporalWireMock"
    }

    fn metadata(&self) -> &'static dyn LanguageMetadata {
        &MOCK_METADATA
    }

    fn parse_term(&self, input: &str) -> Result<Box<dyn Term>, String> {
        Ok(Box::new(MockTerm(input.to_string())))
    }

    fn parse_term_for_env(&self, input: &str) -> Result<Box<dyn Term>, String> {
        self.parse_term(input)
    }

    fn run_ascent(&self, _term: &dyn Term) -> Result<AscentResults, String> {
        Ok(AscentResults::empty())
    }

    fn run_backend_report(
        &self,
        backend: RuntimeBackend,
        term: &dyn Term,
    ) -> Result<RuntimeBackendReport, String> {
        match backend {
            RuntimeBackend::Dovetail => {
                let report = if format!("{}", term) == "converge" {
                    // Literal root → reduces to a normal form.
                    single_root_report("TemporalWireMock::Int::NumLit(8)")
                } else {
                    // Non-literal root → stays a runtime report (no normal form).
                    single_root_report("TemporalWireMock::Proc::Loop")
                };
                RuntimeBackendReport::try_dovetail(report).map_err(|err| err.to_string())
            },
            other => Err(format!("{other} backend is not installed")),
        }
    }

    fn create_env(&self) -> Box<dyn Any + Send + Sync> {
        Box::new(())
    }

    fn add_to_env(&self, _env: &mut dyn Any, _name: &str, _term: &dyn Term) -> Result<(), String> {
        Ok(())
    }

    fn remove_from_env(&self, _env: &mut dyn Any, _name: &str) -> Result<bool, String> {
        Ok(false)
    }

    fn clear_env(&self, _env: &mut dyn Any) {}

    fn substitute_env(&self, term: &dyn Term, _env: &dyn Any) -> Result<Box<dyn Term>, String> {
        Ok(term.clone_box())
    }

    fn list_env(&self, _env: &dyn Any) -> Vec<(String, String, Option<String>)> {
        Vec::new()
    }

    fn set_env_comment(
        &self,
        _env: &mut dyn Any,
        _name: &str,
        _comment: String,
    ) -> Result<(), String> {
        Ok(())
    }

    fn is_env_empty(&self, _env: &dyn Any) -> bool {
        true
    }

    fn infer_term_type(&self, _term: &dyn Term) -> TermType {
        TermType::Unknown
    }

    fn infer_var_types(&self, _term: &dyn Term) -> Vec<VarTypeInfo> {
        Vec::new()
    }

    fn infer_var_type(&self, _term: &dyn Term, _var_name: &str) -> Option<TermType> {
        None
    }
}

// ════════════════════════════════════════════════════════════════════════════
// Helpers
// ════════════════════════════════════════════════════════════════════════════

/// Build a runner over the mock language with the given LTL properties.
fn mock_runner(ltl_properties: Vec<String>) -> SimulationRunner<'static> {
    let language: &'static dyn Language = Box::leak(Box::new(TemporalWireMockLanguage));
    let config = SimulationConfig {
        max_steps: 100,
        proptest_cases: 1,
        // Fixed seed so the (single-case) campaign is deterministic across runs.
        seed: Some([5u8; 32]),
        ltl_properties,
        ..SimulationConfig::default()
    };
    SimulationRunner::new(language, config)
}

// ════════════════════════════════════════════════════════════════════════════
// Assertion (i): a converging input → no LTL violation
// ════════════════════════════════════════════════════════════════════════════

#[test]
fn converging_input_satisfies_eventually_normal_form() {
    let runner = mock_runner(vec!["F(normal_form)".to_string()]);

    let trace = runner
        .run_to_normal_form("converge")
        .expect("converging run must satisfy F(normal_form), not surface an LTL violation");

    // The run reaches a normal form, so F(normal_form) holds and the outcome is
    // the ordinary NormalForm — never an LtlViolation.
    match &trace.outcome {
        TraceOutcome::NormalForm { term, .. } => {
            assert_eq!(term, "8", "expected the literal normal form '8', got '{}'", term);
        },
        other => panic!("expected NormalForm outcome for a converging run, got: {:?}", other),
    }
    assert!(
        !matches!(trace.outcome, TraceOutcome::LtlViolation { .. }),
        "a satisfied LTL property must not produce an LtlViolation outcome",
    );
}

// ════════════════════════════════════════════════════════════════════════════
// Assertion (ii): a non-converging input → a Violated surfaced in the campaign
// ════════════════════════════════════════════════════════════════════════════

#[test]
fn non_converging_input_surfaces_ltl_violation_in_run() {
    let runner = mock_runner(vec!["F(normal_form)".to_string()]);

    // A non-literal Dovetail report never reaches a normal form, so
    // F(normal_form) is violated and the run fails with an LtlViolation.
    let failure = runner
        .run_to_normal_form("loop-forever")
        .expect_err("non-converging run must surface an F(normal_form) LTL violation");

    assert!(
        failure.error.contains("F(normal_form)"),
        "failure error should reference the violated formula, got: {}",
        failure.error,
    );
    match &failure.trace.outcome {
        TraceOutcome::LtlViolation { formula, message, .. } => {
            assert_eq!(formula, "F(normal_form)");
            assert!(
                message.contains("F(normal_form)"),
                "LtlViolation message should reference the formula, got: {}",
                message,
            );
        },
        other => panic!("expected LtlViolation outcome, got: {:?}", other),
    }
}

#[test]
fn non_converging_campaign_surfaces_violation_in_campaign_results() {
    let mut runner = mock_runner(vec!["F(normal_form)".to_string()]);

    // Single-case campaign over the non-converging input.
    use proptest::prelude::*;
    let strategy = Just("loop-forever".to_string());

    let results: CampaignResults = runner.run_campaign(strategy.boxed());

    assert_eq!(results.total_cases, 1, "expected exactly one case");
    assert_eq!(results.failed, 1, "the non-converging case must fail on F(normal_form)");
    assert_eq!(results.passed, 0);

    // The dedicated ltl_violations surface must carry the counterexample.
    assert_eq!(
        results.ltl_violations.len(),
        1,
        "exactly one LTL violation should be surfaced, got {:?}",
        results.ltl_violations,
    );
    let (formula, message) = &results.ltl_violations[0];
    assert_eq!(formula, "F(normal_form)");
    assert!(
        message.contains("F(normal_form)"),
        "surfaced LTL message should reference the formula, got: {}",
        message,
    );

    // The full failure record must also carry the LtlViolation outcome.
    assert_eq!(results.failures.len(), 1);
    assert!(matches!(
        results.failures[0].trace.outcome,
        TraceOutcome::LtlViolation { .. }
    ));
}

// ════════════════════════════════════════════════════════════════════════════
// Assertion (iii): empty ltl_properties → byte-identical campaign outcome
// ════════════════════════════════════════════════════════════════════════════

/// The no-regress canary. Running the SAME campaign twice — once with empty
/// `ltl_properties`, once with a property that *would* fire — must leave the
/// campaign pass/fail tallies governed solely by the empty-vs-nonempty toggle:
/// with empty properties the non-converging run is recorded exactly as it was
/// before the temporal wire existed (no LtlViolation, no `ltl_violations`
/// entry), proving the new check is a true no-op when unconfigured.
#[test]
fn empty_ltl_properties_is_a_noop_canary() {
    // Baseline: NO LTL properties. The non-converging run produces a
    // RuntimeReport and — with no NormalFormReachable invariant — that is NOT a
    // failure, so the campaign passes.
    let mut baseline_runner = mock_runner(Vec::new());
    use proptest::prelude::*;
    let baseline_results = baseline_runner.run_campaign(Just("loop-forever".to_string()).boxed());

    assert_eq!(baseline_results.total_cases, 1);
    assert_eq!(
        baseline_results.failed, 0,
        "with empty ltl_properties, a RuntimeReport run is not a failure",
    );
    assert_eq!(baseline_results.passed, 1);
    assert!(
        baseline_results.ltl_violations.is_empty(),
        "empty ltl_properties must never populate ltl_violations",
    );

    // Direct single-run confirmation: the trace outcome is the ordinary
    // RuntimeReport, byte-identical to pre-wire behavior (no LtlViolation).
    let runner = mock_runner(Vec::new());
    let trace = runner
        .run_to_normal_form("loop-forever")
        .expect("empty ltl_properties: the non-converging run still succeeds as a RuntimeReport");
    match &trace.outcome {
        TraceOutcome::RuntimeReport { backend, .. } => {
            assert_eq!(backend, "Dovetail");
        },
        other => panic!(
            "empty ltl_properties must leave the outcome unchanged (RuntimeReport), got: {:?}",
            other
        ),
    }

    // Contrast: the SAME input WITH the property flips the campaign to a
    // failure surfaced via ltl_violations. This proves the toggle — and only
    // the toggle — governs the difference.
    let mut wired_runner = mock_runner(vec!["F(normal_form)".to_string()]);
    let wired_results = wired_runner.run_campaign(Just("loop-forever".to_string()).boxed());
    assert_eq!(wired_results.failed, 1);
    assert_eq!(wired_results.ltl_violations.len(), 1);
}
