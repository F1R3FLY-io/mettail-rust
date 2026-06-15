//! Algebraic property assertions: equation symmetry, rewrite progress,
//! rewrite-to, normal form checking.

use crate::runtime_report;
use mettail_runtime::Language;

/// Run the selected runtime backend on lhs, verify rhs appears in the reported
/// outputs, and vice versa.
pub fn assert_equation_symmetry(
    lang: &dyn Language,
    lhs_str: &str,
    rhs_str: &str,
) -> Result<(), String> {
    // Forward: lhs => check rhs in equiv class
    mettail_runtime::clear_var_cache();
    let lhs = lang
        .parse_term(lhs_str)
        .map_err(|e| format!("Failed to parse LHS '{}': {}", lhs_str, e))?;

    let report = runtime_report::run_ascent_oracle_report(
        lang,
        lhs.as_ref(),
        &format!("equation symmetry LHS '{}'", lhs_str),
    )?;

    if !runtime_report::report_contains_expected(&report, rhs_str) {
        let all_displays = runtime_report::report_observed_outputs(&report);
        return Err(format!(
            "Equation LHS->RHS failed: '{}' does not produce '{}'\n  reachable: {:?}",
            lhs_str, rhs_str, all_displays
        ));
    }

    // Backward: rhs => check lhs in equiv class
    mettail_runtime::clear_var_cache();
    let rhs = lang
        .parse_term(rhs_str)
        .map_err(|e| format!("Failed to parse RHS '{}': {}", rhs_str, e))?;

    let report = runtime_report::run_ascent_oracle_report(
        lang,
        rhs.as_ref(),
        &format!("equation symmetry RHS '{}'", rhs_str),
    )?;

    if !runtime_report::report_contains_expected(&report, lhs_str) {
        let all_displays = runtime_report::report_observed_outputs(&report);
        return Err(format!(
            "Equation RHS->LHS failed: '{}' does not produce '{}'\n  reachable: {:?}",
            rhs_str, lhs_str, all_displays
        ));
    }

    Ok(())
}

/// Run Ascent on term, verify at least one rewrite fires.
pub fn assert_rewrite_fires(lang: &dyn Language, input: &str) -> Result<(), String> {
    mettail_runtime::clear_var_cache();
    let term = lang
        .parse_term(input)
        .map_err(|e| format!("Failed to parse '{}': {}", input, e))?;

    let report = runtime_report::run_ascent_oracle_report(
        lang,
        term.as_ref(),
        &format!("rewrite firing check for '{}'", input),
    )?;
    let results = runtime_report::expect_ascent_graph(report, "rewrite firing check")?;

    if results.rewrites.is_empty() {
        return Err(format!("Expected at least one rewrite to fire for '{}', but none did", input));
    }

    Ok(())
}

/// Run Ascent, verify rewrite reaches expected normal form.
pub fn assert_rewrites_to(lang: &dyn Language, input: &str, expected: &str) -> Result<(), String> {
    mettail_runtime::clear_var_cache();
    let term = lang
        .parse_term(input)
        .map_err(|e| format!("Failed to parse '{}': {}", input, e))?;

    let report = runtime_report::run_ascent_oracle_report(
        lang,
        term.as_ref(),
        &format!("rewrite-to check for '{}'", input),
    )?;
    if runtime_report::report_contains_expected(&report, expected) {
        return Ok(());
    }

    let observed = runtime_report::report_observed_outputs(&report);
    Err(format!(
        "Rewrite mismatch:\n  input:    '{}'\n  expected: '{}'\n  got:      {:?}",
        input, expected, observed
    ))
}

/// Verify term is in normal form (no rewrites apply).
pub fn assert_normal_form(lang: &dyn Language, input: &str) -> Result<(), String> {
    mettail_runtime::clear_var_cache();
    let term = lang
        .parse_term(input)
        .map_err(|e| format!("Failed to parse '{}': {}", input, e))?;

    let report = runtime_report::run_ascent_oracle_report(
        lang,
        term.as_ref(),
        &format!("normal-form check for '{}'", input),
    )?;
    let results = runtime_report::expect_ascent_graph(report, "normal-form check")?;

    if !results.rewrites.is_empty() {
        let targets: Vec<String> = results
            .rewrites
            .iter()
            .filter_map(|rw| {
                results
                    .all_terms
                    .iter()
                    .find(|t| t.term_id == rw.to_id)
                    .map(|t| t.display.clone())
            })
            .collect();
        return Err(format!(
            "Expected '{}' to be in normal form, but rewrites fired to: {:?}",
            input, targets
        ));
    }

    Ok(())
}

#[cfg(test)]
mod tests {
    use std::any::Any;

    use mettail_runtime::{
        AscentResults, BackendCapabilityDef, LanguageMetadata, RuntimeBackend,
        RuntimeBackendArtifact, RuntimeBackendReport, RuntimeChannelObservation,
        RuntimeObservationValue, Term, TermType, VarTypeInfo,
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
            17
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
            "AlgebraicObservationLanguage"
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
            "AlgebraicObservationLanguage"
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
            panic!("equation symmetry must use the selected runtime report, not Ascent")
        }

        fn run_backend_report(
            &self,
            backend: RuntimeBackend,
            term: &dyn Term,
        ) -> Result<RuntimeBackendReport, String> {
            let term = term
                .as_any()
                .downcast_ref::<ObservationTerm>()
                .ok_or_else(|| "unexpected term type".to_string())?;
            let observed = match term.0.as_str() {
                "left" => "right",
                "right" => "left",
                other => other,
            };
            match backend {
                RuntimeBackend::RhoMachine => RuntimeBackendReport::try_observations(
                    RuntimeBackend::RhoMachine,
                    RuntimeBackendArtifact::RhoNormalizedAst,
                    vec![RuntimeChannelObservation::new(
                        "OUT",
                        vec![RuntimeObservationValue::Text(observed.to_string())],
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
    fn equation_symmetry_accepts_runtime_observations() {
        assert_equation_symmetry(&ObservationLanguage, "left", "right")
            .expect("observation-shaped runtime report should prove equation symmetry");
    }
}
