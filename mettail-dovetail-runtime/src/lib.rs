//! Runtime adapter for checked Dovetail reports.
//!
//! The `dovetail` crate stays substrate-neutral and does not depend on
//! `mettail-runtime`. This crate is the one-way adapter that projects a
//! `dovetail::report::DovetailRunReport` into the generic
//! `RuntimeBackendReport` envelope and installs it as `RuntimeBackend::Dovetail`
//! for a concrete `Language` value.

#![forbid(unsafe_code)]

use std::any::Any;
use std::fmt;

use dovetail::extract::ExtractionCompleteness;
use dovetail::report::DovetailRunReport;
use mettail_runtime::{
    AscentResults, Language, RuntimeBackend, RuntimeBackendCapability, RuntimeBackendReport,
    RuntimeDovetailCompleteness, RuntimeDovetailDerivationEdge, RuntimeDovetailRunReport,
    RuntimeDovetailTermRecord, SeedFacts, Term, TermType, VarTypeInfo, WeightedRewriteSeed,
    WeightedSeedId,
};

/// Convert a checked Dovetail report into the runtime-neutral report projection.
///
/// This copies exact keys and derivation edges without hashing or display-string
/// equality. `Display` is used only for reader-facing operator and weight fields
/// in the generic runtime envelope.
pub fn project_dovetail_report<L, W>(report: &DovetailRunReport<L, W>) -> RuntimeDovetailRunReport
where
    L: fmt::Display,
    W: fmt::Display,
{
    RuntimeDovetailRunReport {
        roots: report
            .roots
            .iter()
            .map(|key| key.as_bytes().to_vec())
            .collect(),
        root_ordinals: report.root_ordinals.clone(),
        terms: report
            .terms
            .iter()
            .map(|term| RuntimeDovetailTermRecord {
                ordinal: term.ordinal,
                class_id: term.class.0,
                key: term.key.as_bytes().to_vec(),
                op_display: term.op.to_string(),
                weight_display: term.weight.to_string(),
                is_root: term.is_root,
            })
            .collect(),
        derivation_edges: report
            .derivation_edges
            .iter()
            .map(|edge| RuntimeDovetailDerivationEdge {
                ordinal: edge.ordinal,
                parent_key: edge.parent_key.as_bytes().to_vec(),
                child_key: edge.child_key.as_bytes().to_vec(),
                child_index: edge.child_index,
            })
            .collect(),
        completeness: match report.completeness {
            ExtractionCompleteness::Complete => RuntimeDovetailCompleteness::Complete,
            ExtractionCompleteness::BoundedByCycleCut => {
                RuntimeDovetailCompleteness::BoundedByCycleCut
            },
        },
    }
}

/// Runtime adapter that selects a complete Dovetail report as the default
/// backend for a concrete language value.
///
/// The wrapped language remains the authority for parsing, environments, type
/// inference, and the Ascent oracle. This adapter only changes runtime backend
/// selection: `RuntimeBackend::Dovetail` becomes the default, explicit Ascent
/// requests still delegate to the wrapped language, and incomplete Dovetail
/// reports fail closed instead of being advertised as production results.
pub struct DovetailRuntimeBackedLanguage<L, F> {
    inner: L,
    evidence_refs: Vec<String>,
    runner: F,
}

/// Failure installing a Dovetail runtime-backed default on a generated language.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum DovetailRuntimeBackedLanguageError {
    /// A production Dovetail default must carry the evidence references that
    /// justify installing it.
    MissingEvidenceRefs,
    /// Evidence references must be stable nonblank identifiers. Accepted
    /// references are stored without surrounding whitespace.
    BlankEvidenceRef { index: usize },
}

impl fmt::Display for DovetailRuntimeBackedLanguageError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::MissingEvidenceRefs => {
                write!(f, "Dovetail backend installation requires evidence references")
            },
            Self::BlankEvidenceRef { index } => {
                write!(f, "Dovetail backend evidence reference at index {index} is blank")
            },
        }
    }
}

impl std::error::Error for DovetailRuntimeBackedLanguageError {}

impl<L, F> DovetailRuntimeBackedLanguage<L, F>
where
    F: Fn(&dyn Term) -> Result<RuntimeDovetailRunReport, String> + Send + Sync,
{
    pub fn new(
        inner: L,
        evidence_refs: Vec<String>,
        runner: F,
    ) -> Result<Self, DovetailRuntimeBackedLanguageError> {
        if evidence_refs.is_empty() {
            return Err(DovetailRuntimeBackedLanguageError::MissingEvidenceRefs);
        }

        let mut normalized_evidence_refs = Vec::with_capacity(evidence_refs.len());
        for (index, evidence_ref) in evidence_refs.into_iter().enumerate() {
            let trimmed = evidence_ref.trim();
            if trimmed.is_empty() {
                return Err(DovetailRuntimeBackedLanguageError::BlankEvidenceRef { index });
            }
            normalized_evidence_refs.push(trimmed.to_string());
        }

        Ok(Self {
            inner,
            evidence_refs: normalized_evidence_refs,
            runner,
        })
    }

    pub fn inner(&self) -> &L {
        &self.inner
    }

    pub fn evidence_refs(&self) -> &[String] {
        &self.evidence_refs
    }
}

impl<L, F> Language for DovetailRuntimeBackedLanguage<L, F>
where
    L: Language,
    F: Fn(&dyn Term) -> Result<RuntimeDovetailRunReport, String> + Send + Sync,
{
    fn name(&self) -> &'static str {
        self.inner.name()
    }

    fn metadata(&self) -> &'static dyn mettail_runtime::LanguageMetadata {
        self.inner.metadata()
    }

    fn parse_term(&self, input: &str) -> Result<Box<dyn Term>, String> {
        self.inner.parse_term(input)
    }

    fn parse_term_for_env(&self, input: &str) -> Result<Box<dyn Term>, String> {
        self.inner.parse_term_for_env(input)
    }

    fn parse_term_with_weighted_seed_ids(
        &self,
        input: &str,
    ) -> Result<(Box<dyn Term>, Vec<WeightedSeedId>), String> {
        self.inner.parse_term_with_weighted_seed_ids(input)
    }

    fn parse_term_with_weighted_rewrite_seeds(
        &self,
        input: &str,
    ) -> Result<(Box<dyn Term>, Vec<WeightedRewriteSeed>), String> {
        self.inner.parse_term_with_weighted_rewrite_seeds(input)
    }

    fn run_ascent(&self, term: &dyn Term) -> Result<AscentResults, String> {
        self.inner.run_ascent(term)
    }

    fn default_runtime_backend(&self) -> RuntimeBackend {
        RuntimeBackend::Dovetail
    }

    fn runtime_backend_capabilities(&self) -> Vec<RuntimeBackendCapability> {
        let inner_capabilities = self.inner.runtime_backend_capabilities();
        let mut capabilities = Vec::with_capacity(inner_capabilities.len().saturating_add(1));
        capabilities.push(RuntimeBackendCapability {
            backend: RuntimeBackend::Dovetail,
            is_default: true,
            evidence_refs: self.evidence_refs.clone(),
        });
        capabilities.extend(
            inner_capabilities
                .into_iter()
                .filter(|capability| capability.backend != RuntimeBackend::Dovetail)
                .map(|mut capability| {
                    capability.is_default = false;
                    capability
                }),
        );
        capabilities
    }

    fn supports_runtime_backend(&self, backend: RuntimeBackend) -> bool {
        backend == RuntimeBackend::Dovetail || self.inner.supports_runtime_backend(backend)
    }

    fn run_backend_report(
        &self,
        backend: RuntimeBackend,
        term: &dyn Term,
    ) -> Result<RuntimeBackendReport, String> {
        match backend {
            RuntimeBackend::Dovetail => {
                let report = (self.runner)(term).map_err(|err| {
                    format!(
                        "Dovetail backend for language {} could not build a checked report: {err}",
                        self.name()
                    )
                })?;
                report.assert_complete().map_err(|status| {
                    format!(
                        "Dovetail backend for language {} produced incomplete report: {status}",
                        self.name()
                    )
                })?;
                RuntimeBackendReport::try_dovetail(report, self.evidence_refs.clone()).map_err(
                    |err| {
                        format!(
                            "Dovetail backend for language {} produced malformed report: {err}",
                            self.name()
                        )
                    },
                )
            },
            other => self.inner.run_backend_report(other, term),
        }
    }

    fn run_ascent_with_facts(
        &self,
        term: &dyn Term,
        facts: &SeedFacts,
    ) -> Result<AscentResults, String> {
        self.inner.run_ascent_with_facts(term, facts)
    }

    fn run_backend_report_with_facts(
        &self,
        backend: RuntimeBackend,
        term: &dyn Term,
        facts: &SeedFacts,
    ) -> Result<RuntimeBackendReport, String> {
        match backend {
            RuntimeBackend::Dovetail if facts.is_empty() => self.run_backend_report(backend, term),
            RuntimeBackend::Dovetail => Err(format!(
                "Dovetail backend for language {} does not accept Ascent-shaped seeded facts",
                self.name()
            )),
            other => self.inner.run_backend_report_with_facts(other, term, facts),
        }
    }

    fn try_direct_eval(&self, term: &dyn Term) -> Option<Box<dyn Term>> {
        self.inner.try_direct_eval(term)
    }

    fn normalize_term(&self, term: &dyn Term) -> Box<dyn Term> {
        self.inner.normalize_term(term)
    }

    fn format_term(&self, term: &dyn Term) -> String {
        self.inner.format_term(term)
    }

    fn create_env(&self) -> Box<dyn Any + Send + Sync> {
        self.inner.create_env()
    }

    fn add_to_env(&self, env: &mut dyn Any, name: &str, term: &dyn Term) -> Result<(), String> {
        self.inner.add_to_env(env, name, term)
    }

    fn remove_from_env(&self, env: &mut dyn Any, name: &str) -> Result<bool, String> {
        self.inner.remove_from_env(env, name)
    }

    fn clear_env(&self, env: &mut dyn Any) {
        self.inner.clear_env(env)
    }

    fn substitute_env(&self, term: &dyn Term, env: &dyn Any) -> Result<Box<dyn Term>, String> {
        self.inner.substitute_env(term, env)
    }

    fn substitute_env_preserve_structure(
        &self,
        term: &dyn Term,
        env: &dyn Any,
    ) -> Result<Box<dyn Term>, String> {
        self.inner.substitute_env_preserve_structure(term, env)
    }

    fn list_env(&self, env: &dyn Any) -> Vec<(String, String, Option<String>)> {
        self.inner.list_env(env)
    }

    fn set_env_comment(
        &self,
        env: &mut dyn Any,
        name: &str,
        comment: String,
    ) -> Result<(), String> {
        self.inner.set_env_comment(env, name, comment)
    }

    fn is_env_empty(&self, env: &dyn Any) -> bool {
        self.inner.is_env_empty(env)
    }

    fn get_env_term(&self, env: &dyn Any, name: &str) -> Option<Box<dyn Term>> {
        self.inner.get_env_term(env, name)
    }

    fn infer_term_type(&self, term: &dyn Term) -> TermType {
        self.inner.infer_term_type(term)
    }

    fn infer_var_types(&self, term: &dyn Term) -> Vec<VarTypeInfo> {
        self.inner.infer_var_types(term)
    }

    fn infer_var_type(&self, term: &dyn Term, var_name: &str) -> Option<TermType> {
        self.inner.infer_var_type(term, var_name)
    }
}

#[cfg(test)]
mod tests {
    use std::collections::HashMap;
    use std::fmt;

    use dovetail::egraph::{EGraph, ENode};
    use dovetail::extract::Extractor;
    use dovetail::report::report_from_extraction;
    use mettail_runtime::{
        AscentResults, BackendCapabilityDef, LanguageMetadata, RuntimeBackend,
        RuntimeBackendArtifact, RuntimeBackendOutput, SeedFacts, Term,
    };
    use rigail::TropicalWeight;

    use super::*;

    #[derive(Clone, Debug)]
    struct DummyTerm(String);

    impl fmt::Display for DummyTerm {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            write!(f, "{}", self.0)
        }
    }

    impl Term for DummyTerm {
        fn clone_box(&self) -> Box<dyn Term> {
            Box::new(self.clone())
        }

        fn term_id(&self) -> u64 {
            1
        }

        fn term_eq(&self, other: &dyn Term) -> bool {
            other
                .as_any()
                .downcast_ref::<DummyTerm>()
                .map(|other| other.0 == self.0)
                .unwrap_or(false)
        }

        fn as_any(&self) -> &dyn Any {
            self
        }
    }

    struct DummyMetadata;

    static TYPE_DEFS: &[mettail_runtime::TypeDef] = &[mettail_runtime::TypeDef {
        name: "Expr",
        native_type: None,
        is_primary: true,
    }];

    impl LanguageMetadata for DummyMetadata {
        fn name(&self) -> &'static str {
            "DovetailDummy"
        }

        fn types(&self) -> &'static [mettail_runtime::TypeDef] {
            TYPE_DEFS
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
            mettail_runtime::DEFAULT_ASCENT_BACKEND_CAPABILITIES
        }
    }

    static METADATA: DummyMetadata = DummyMetadata;

    struct DummyLanguage;

    impl Language for DummyLanguage {
        fn name(&self) -> &'static str {
            "DovetailDummy"
        }

        fn metadata(&self) -> &'static dyn LanguageMetadata {
            &METADATA
        }

        fn parse_term(&self, input: &str) -> Result<Box<dyn Term>, String> {
            Ok(Box::new(DummyTerm(input.to_string())))
        }

        fn parse_term_for_env(&self, input: &str) -> Result<Box<dyn Term>, String> {
            self.parse_term(input)
        }

        fn run_ascent(&self, _term: &dyn Term) -> Result<AscentResults, String> {
            Ok(AscentResults::empty())
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

    fn complete_runtime_report() -> RuntimeDovetailRunReport {
        let mut eg = EGraph::<String>::new();
        let x = eg.add(ENode::leaf("x".to_string()));
        let y = eg.add(ENode::leaf("y".to_string()));
        let pair = eg.add(ENode::new("pair".to_string(), vec![x, y]));
        let mut extractor = Extractor::new(&eg, |_| TropicalWeight(1.0));
        let report = report_from_extraction(extractor.derivations(pair).collect_checked());
        project_dovetail_report(&report)
    }

    fn bounded_runtime_report() -> RuntimeDovetailRunReport {
        RuntimeDovetailRunReport {
            roots: vec![b"root".to_vec()],
            root_ordinals: vec![0],
            terms: vec![RuntimeDovetailTermRecord {
                ordinal: 0,
                class_id: 0,
                key: b"root".to_vec(),
                op_display: "cycle".to_string(),
                weight_display: "1".to_string(),
                is_root: true,
            }],
            derivation_edges: Vec::new(),
            completeness: RuntimeDovetailCompleteness::BoundedByCycleCut,
        }
    }

    fn malformed_complete_runtime_report() -> RuntimeDovetailRunReport {
        let mut report = complete_runtime_report();
        report.root_ordinals[0] = 99;
        report
    }

    #[test]
    fn projection_preserves_report_identity_and_completeness() {
        let projected = complete_runtime_report();

        assert_eq!(projected.completeness, RuntimeDovetailCompleteness::Complete);
        assert_eq!(projected.root_count(), 1);
        assert_eq!(projected.root_ordinals, vec![0]);
        projected
            .validate_shape()
            .expect("projected Dovetail report is structurally valid");
        assert_eq!(projected.terms.len(), 3);
        assert_eq!(projected.terms[0].op_display, "pair");
        assert!(projected.terms[0].is_root);
        assert_eq!(projected.derivation_edges.len(), 2);
        assert!(projected.term_by_key(&projected.roots[0]).is_some());
    }

    #[test]
    fn dovetail_wrapper_installs_complete_report_backend() {
        let language = DovetailRuntimeBackedLanguage::new(
            DummyLanguage,
            vec!["dovetail/formal/rocq/theories/Refinement/RuntimeReportBridge.v".to_string()],
            |_term| Ok(complete_runtime_report()),
        )
        .expect("nonblank Dovetail evidence refs should install the wrapper");
        let term = language.parse_term("pair(x,y)").expect("parse");

        assert_eq!(language.default_runtime_backend(), RuntimeBackend::Dovetail);
        assert!(language.supports_runtime_backend(RuntimeBackend::Dovetail));
        assert!(language.supports_runtime_backend(RuntimeBackend::Ascent));
        assert!(!language.supports_runtime_backend(RuntimeBackend::RhoMachine));

        let capabilities = language.runtime_backend_capabilities();
        assert_eq!(capabilities.len(), 2);
        assert_eq!(capabilities[0].backend, RuntimeBackend::Dovetail);
        assert!(capabilities[0].is_default);
        assert_eq!(
            capabilities[0].evidence_refs,
            vec!["dovetail/formal/rocq/theories/Refinement/RuntimeReportBridge.v".to_string()]
        );
        assert_eq!(capabilities[1].backend, RuntimeBackend::Ascent);
        assert!(!capabilities[1].is_default);

        let report = language
            .run_default_backend_report(term.as_ref())
            .expect("complete Dovetail report should run");
        assert_eq!(report.backend(), RuntimeBackend::Dovetail);
        assert_eq!(report.artifact(), RuntimeBackendArtifact::DovetailRunReport);
        let RuntimeBackendOutput::Dovetail(dovetail_report) = report.into_output() else {
            panic!("expected Dovetail report output");
        };
        assert!(dovetail_report.is_complete());
        assert_eq!(dovetail_report.root_count(), 1);

        let compat_err = language
            .run_default_backend(term.as_ref())
            .expect_err("Ascent-shaped compatibility API must reject Dovetail reports");
        assert!(
            compat_err
                .contains("Dovetail backend for language DovetailDummy returned DovetailRunReport"),
            "{compat_err}"
        );
    }

    #[test]
    fn dovetail_wrapper_rejects_bounded_reports_and_ascent_facts() {
        let language = DovetailRuntimeBackedLanguage::new(
            DummyLanguage,
            vec!["dovetail/formal/rocq/theories/Extraction/CycleCutBoundary.v".to_string()],
            |_term| Ok(bounded_runtime_report()),
        )
        .expect("nonblank Dovetail evidence refs should install the wrapper");
        let term = language.parse_term("cycle").expect("parse");

        let err = language
            .run_default_backend_report(term.as_ref())
            .expect_err("bounded report must not be advertised as complete");
        assert!(err.contains("produced incomplete report: BoundedByCycleCut"), "{err}");

        let mut facts = SeedFacts::new();
        facts.insert("fact".to_string(), vec![vec!["value".to_string()]]);
        let seeded_err = language
            .run_backend_report_with_facts(RuntimeBackend::Dovetail, term.as_ref(), &facts)
            .expect_err("Dovetail path must reject Ascent-shaped fact seeding");
        assert!(
            seeded_err.contains("does not accept Ascent-shaped seeded facts"),
            "{seeded_err}"
        );
    }

    #[test]
    fn dovetail_wrapper_rejects_malformed_complete_reports() {
        let language = DovetailRuntimeBackedLanguage::new(
            DummyLanguage,
            vec!["dovetail/formal/rocq/theories/Refinement/RuntimeReportBridge.v".to_string()],
            |_term| Ok(malformed_complete_runtime_report()),
        )
        .expect("nonblank Dovetail evidence refs should install the wrapper");
        let term = language.parse_term("bad-report").expect("parse");

        let err = language
            .run_default_backend_report(term.as_ref())
            .expect_err("malformed complete reports must fail closed");
        assert!(err.contains("produced malformed report"), "{err}");
        assert!(err.contains("term ordinal 99"), "{err}");
    }

    #[test]
    fn explicit_ascent_still_delegates_to_inner_language() {
        let language = DovetailRuntimeBackedLanguage::new(
            DummyLanguage,
            vec!["dovetail evidence".to_string()],
            |_term| Ok(complete_runtime_report()),
        )
        .expect("nonblank Dovetail evidence refs should install the wrapper");
        let term = language.parse_term("x").expect("parse");
        let report = language
            .run_backend_report(RuntimeBackend::Ascent, term.as_ref())
            .expect("explicit Ascent should delegate");
        assert_eq!(report.backend(), RuntimeBackend::Ascent);
        assert!(report.as_ascent_results().is_some());
    }

    #[test]
    fn wrapper_passes_empty_fact_set_to_default_dovetail_report() {
        let language = DovetailRuntimeBackedLanguage::new(
            DummyLanguage,
            vec!["dovetail evidence".to_string()],
            |_term| Ok(complete_runtime_report()),
        )
        .expect("nonblank Dovetail evidence refs should install the wrapper");
        let term = language.parse_term("x").expect("parse");
        let report = language
            .run_default_backend_report_with_facts(term.as_ref(), &HashMap::new())
            .expect("empty fact set matches default Dovetail execution");
        assert_eq!(report.backend(), RuntimeBackend::Dovetail);
    }

    #[test]
    fn dovetail_wrapper_rejects_missing_or_blank_evidence_refs() {
        let missing = DovetailRuntimeBackedLanguage::new(DummyLanguage, Vec::new(), |_term| {
            Ok(complete_runtime_report())
        });
        assert!(missing.is_err(), "Dovetail default installation must require evidence refs");
        assert_eq!(missing.err(), Some(DovetailRuntimeBackedLanguageError::MissingEvidenceRefs));

        let blank = DovetailRuntimeBackedLanguage::new(
            DummyLanguage,
            vec![
                "dovetail/formal/rocq/theories/Refinement/RuntimeReportBridge.v".to_string(),
                "  ".to_string(),
            ],
            |_term| Ok(complete_runtime_report()),
        );
        assert!(blank.is_err(), "blank Dovetail evidence refs must fail installation");
        assert_eq!(
            blank.err(),
            Some(DovetailRuntimeBackedLanguageError::BlankEvidenceRef { index: 1 })
        );

        let normalized = DovetailRuntimeBackedLanguage::new(
            DummyLanguage,
            vec!["  dovetail/formal/rocq/theories/Refinement/RuntimeReportBridge.v  ".to_string()],
            |_term| Ok(complete_runtime_report()),
        )
        .expect("nonblank Dovetail evidence refs should install the wrapper");
        let normalized_refs = normalized
            .evidence_refs()
            .iter()
            .map(String::as_str)
            .collect::<Vec<_>>();
        assert_eq!(
            normalized_refs,
            vec!["dovetail/formal/rocq/theories/Refinement/RuntimeReportBridge.v"]
        );
    }
}
