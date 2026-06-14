//! Semantic property assertions: eval determinism, normalization idempotence,
//! substitution well-formedness, ground eval completeness.

use crate::runtime_report;
use mettail_runtime::{Language, Term};

/// Assert `eval(t) == eval(t)` — evaluation is deterministic.
///
/// Evaluates the term twice and verifies the results are alpha-equivalent.
pub fn assert_eval_determinism(lang: &dyn Language, term: &dyn Term) -> Result<(), String> {
    let result_1 =
        runtime_report::run_default_backend_report(lang, term, "first deterministic evaluation")?;

    let result_2 =
        runtime_report::run_default_backend_report(lang, term, "second deterministic evaluation")?;

    let signature_1 = runtime_report::report_signature(&result_1);
    let signature_2 = runtime_report::report_signature(&result_2);

    if signature_1 != signature_2 {
        return Err(format!(
            "Non-deterministic eval:\n  first:  {:?}\n  second: {:?}\n  term: {:?}",
            signature_1, signature_2, term
        ));
    }

    Ok(())
}

/// Assert `is_ground(t) => try_direct_eval(t).is_some()` — ground terms evaluate.
pub fn assert_ground_eval_completeness(
    lang: &dyn Language,
    term: &dyn Term,
    is_ground: bool,
) -> Result<(), String> {
    if !is_ground {
        return Ok(()); // Only applies to ground terms
    }

    mettail_runtime::clear_var_cache();
    match lang.try_direct_eval(term) {
        Some(_) => Ok(()),
        None => Err(format!("Ground term did not evaluate: {:?}", term)),
    }
}

/// Assert eval(parse(input)) displays as expected.
pub fn assert_evals_to(lang: &dyn Language, input: &str, expected: &str) -> Result<(), String> {
    mettail_runtime::clear_var_cache();
    let term = lang
        .parse_term(input)
        .map_err(|e| format!("Failed to parse input '{}': {}", input, e))?;

    // Try direct eval first (for native types)
    if let Some(result) = lang.try_direct_eval(term.as_ref()) {
        let result_str = format!("{}", result);
        if result_str != expected {
            return Err(format!(
                "Eval mismatch:\n  input:    '{}'\n  expected: '{}'\n  got:      '{}'",
                input, expected, result_str
            ));
        }
        return Ok(());
    }

    let report = runtime_report::run_default_backend_report(
        lang,
        term.as_ref(),
        &format!("evaluation for '{}'", input),
    )?;
    if runtime_report::report_contains_expected(&report, expected) {
        return Ok(());
    }

    let observed = runtime_report::report_observed_outputs(&report);
    Err(format!(
        "No backend output matches expected:\n  input:    '{}'\n  expected: '{}'\n  backend:  {}\n  got:      {:?}",
        input,
        expected,
        report.backend(),
        observed
    ))
}

#[cfg(test)]
mod tests {
    use std::any::Any;

    use mettail_runtime::{
        AscentResults, BackendCapabilityDef, LanguageMetadata, RuntimeBackend,
        RuntimeBackendArtifact, RuntimeBackendReport, RuntimeChannelObservation,
        RuntimeObservationValue, TermType, VarTypeInfo,
    };

    use super::*;

    #[derive(Clone, Debug)]
    struct ObservationTerm(String);

    impl std::fmt::Display for ObservationTerm {
        fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            write!(formatter, "{}", self.0)
        }
    }

    impl Term for ObservationTerm {
        fn clone_box(&self) -> Box<dyn Term> {
            Box::new(self.clone())
        }

        fn term_id(&self) -> u64 {
            7
        }

        fn term_eq(&self, other: &dyn Term) -> bool {
            other
                .as_any()
                .downcast_ref::<ObservationTerm>()
                .is_some_and(|other| self.0 == other.0)
        }

        fn as_any(&self) -> &dyn Any {
            self
        }
    }

    struct ObservationMetadata;

    static OBSERVATION_BACKENDS: &[BackendCapabilityDef] = &[BackendCapabilityDef {
        backend: RuntimeBackend::RhoMachine,
        is_default: true,
    }];

    impl LanguageMetadata for ObservationMetadata {
        fn name(&self) -> &'static str {
            "ObservationTestLanguage"
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
            OBSERVATION_BACKENDS
        }
    }

    static OBSERVATION_METADATA: ObservationMetadata = ObservationMetadata;

    struct ObservationLanguage;

    impl Language for ObservationLanguage {
        fn name(&self) -> &'static str {
            "ObservationTestLanguage"
        }

        fn metadata(&self) -> &'static dyn LanguageMetadata {
            &OBSERVATION_METADATA
        }

        fn parse_term(&self, input: &str) -> Result<Box<dyn Term>, String> {
            Ok(Box::new(ObservationTerm(input.to_string())))
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
                RuntimeBackend::Ascent => self.run_ascent(term).map(RuntimeBackendReport::ascent),
                RuntimeBackend::RhoMachine => RuntimeBackendReport::try_observations(
                    RuntimeBackend::RhoMachine,
                    RuntimeBackendArtifact::RhoNormalizedAst,
                    vec![RuntimeChannelObservation::new(
                        "OUT",
                        vec![RuntimeObservationValue::Int(5)],
                    )],
                )
                .map_err(|err| err.to_string()),
                other => Err(format!("{other} is not installed")),
            }
        }

        fn create_env(&self) -> Box<dyn Any + Send + Sync> {
            Box::new(())
        }

        fn add_to_env(
            &self,
            _env: &mut dyn Any,
            _name: &str,
            _term: &dyn Term,
        ) -> Result<(), String> {
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

    #[test]
    fn semantic_eval_assertion_accepts_runtime_observations() {
        let language = ObservationLanguage;
        assert_evals_to(&language, "rho-call", "5").expect("observation value should match");
    }

    #[test]
    fn eval_determinism_compares_runtime_report_signatures() {
        let language = ObservationLanguage;
        let term = language
            .parse_term("rho-call")
            .expect("parse should succeed");

        assert_eval_determinism(&language, term.as_ref())
            .expect("stable observation reports should be deterministic");
    }

    #[test]
    fn rewrite_to_accepts_runtime_observations() {
        let language = ObservationLanguage;

        crate::properties::algebraic::assert_rewrites_to(&language, "rho-call", "5")
            .expect("runtime observation should satisfy rewrite-to style expected output");
    }

    #[test]
    fn graph_only_assertions_reject_runtime_observations() {
        let language = ObservationLanguage;
        let error = crate::properties::algebraic::assert_rewrite_fires(&language, "rho-call")
            .expect_err("rewrite graph checks must reject observation-shaped reports");

        assert!(error.contains("requires an Ascent-shaped rewrite graph"));
    }

    #[test]
    fn program_termination_accepts_runtime_observations() {
        let language = ObservationLanguage;

        crate::program::ProgramTestSuite::new(&language)
            .source("rho-call")
            .expect_terminates(1)
            .run()
            .expect("terminal runtime observations should satisfy termination");
    }
}
