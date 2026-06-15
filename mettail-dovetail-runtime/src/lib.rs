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
/// inference, and transition-only oracle construction outside the production
/// wrapper. This adapter changes the public runtime view:
/// `RuntimeBackend::Dovetail` becomes the default, the legacy Ascent runtime is
/// not exposed through the wrapped value, and incomplete Dovetail reports fail
/// closed instead of being advertised as production results.
pub struct DovetailRuntimeBackedLanguage<L, F> {
    inner: L,
    runner: DovetailCompilerStage<F>,
}

/// Language-specific Dovetail compiler stage derived from a generated
/// `LanguageDef`.
///
/// This is implementation identity data, not a proof artifact. It lets the
/// runtime adapter reject a Dovetail report producer that was built from a
/// different macro-expanded language definition than the generated language
/// being wrapped.
pub struct DovetailCompilerStage<F> {
    definition_fingerprint: String,
    compiler: F,
}

impl<F> DovetailCompilerStage<F> {
    pub fn new(definition_fingerprint: impl Into<String>, compiler: F) -> Self {
        Self {
            definition_fingerprint: definition_fingerprint.into(),
            compiler,
        }
    }

    pub fn definition_fingerprint(&self) -> &str {
        &self.definition_fingerprint
    }
}

/// Failure installing a Dovetail backend runner on a generated language.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum DovetailRuntimeBackedLanguageError {
    /// The generated language metadata did not expose the macro-derived
    /// definition fingerprint required for production Dovetail installation.
    MissingLanguageDefinitionFingerprint { language_name: String },
    /// The Dovetail compiler stage was derived from a different generated
    /// definition than the wrapped language.
    CompilerDefinitionMismatch {
        language_name: String,
        language_definition_fingerprint: String,
        compiler_definition_fingerprint: String,
    },
}

impl fmt::Display for DovetailRuntimeBackedLanguageError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::MissingLanguageDefinitionFingerprint { language_name } => write!(
                f,
                "Dovetail production backend for language {language_name} requires generated LanguageDef fingerprint metadata"
            ),
            Self::CompilerDefinitionMismatch {
                language_name,
                language_definition_fingerprint,
                compiler_definition_fingerprint,
            } => write!(
                f,
                "Dovetail compiler fingerprint {compiler_definition_fingerprint} cannot be installed on generated language {language_name} fingerprint {language_definition_fingerprint}"
            ),
        }
    }
}

impl std::error::Error for DovetailRuntimeBackedLanguageError {}

impl<L, F> DovetailRuntimeBackedLanguage<L, F>
where
    L: Language,
    F: for<'a> Fn(&'a dyn Term) -> Result<RuntimeDovetailRunReport, String> + Send + Sync,
{
    /// Install a checked Dovetail report runner as the runtime default.
    ///
    /// Formal models: `DovetailLanguageBackendWrapper.v` and
    /// `dovetail/formal/rocq/theories/Refinement/RuntimeReportBridge.v`.
    pub fn new(
        inner: L,
        runner: DovetailCompilerStage<F>,
    ) -> Result<Self, DovetailRuntimeBackedLanguageError> {
        let language_name = inner.name();
        let language_definition_fingerprint =
            inner.metadata().definition_fingerprint().ok_or_else(|| {
                DovetailRuntimeBackedLanguageError::MissingLanguageDefinitionFingerprint {
                    language_name: language_name.to_string(),
                }
            })?;
        if language_definition_fingerprint != runner.definition_fingerprint() {
            return Err(DovetailRuntimeBackedLanguageError::CompilerDefinitionMismatch {
                language_name: language_name.to_string(),
                language_definition_fingerprint: language_definition_fingerprint.to_string(),
                compiler_definition_fingerprint: runner.definition_fingerprint().to_string(),
            });
        }

        Ok(Self { inner, runner })
    }

    pub fn inner(&self) -> &L {
        &self.inner
    }
}

impl<L, F> Language for DovetailRuntimeBackedLanguage<L, F>
where
    L: Language,
    F: for<'a> Fn(&'a dyn Term) -> Result<RuntimeDovetailRunReport, String> + Send + Sync,
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
        let _ = term;
        Err(format!(
            "legacy Ascent runtime is not exposed by Dovetail-backed language {}",
            self.name()
        ))
    }

    fn default_runtime_backend(&self) -> Option<RuntimeBackend> {
        Some(RuntimeBackend::Dovetail)
    }

    fn runtime_backend_capabilities(&self) -> Vec<RuntimeBackendCapability> {
        let inner_capabilities = self.inner.runtime_backend_capabilities();
        let mut capabilities = Vec::with_capacity(inner_capabilities.len().saturating_add(1));
        capabilities.push(RuntimeBackendCapability {
            backend: RuntimeBackend::Dovetail,
            is_default: true,
        });
        capabilities.extend(
            inner_capabilities
                .into_iter()
                .filter(|capability| {
                    capability.backend != RuntimeBackend::Dovetail
                        && capability.backend != RuntimeBackend::Ascent
                })
                .map(|mut capability| {
                    capability.is_default = false;
                    capability
                }),
        );
        capabilities
    }

    fn supports_runtime_backend(&self, backend: RuntimeBackend) -> bool {
        match backend {
            RuntimeBackend::Dovetail => true,
            RuntimeBackend::Ascent => false,
            other => self.inner.supports_runtime_backend(other),
        }
    }

    fn run_backend_report(
        &self,
        backend: RuntimeBackend,
        term: &dyn Term,
    ) -> Result<RuntimeBackendReport, String> {
        match backend {
            RuntimeBackend::Dovetail => {
                let report = (self.runner.compiler)(term).map_err(|err| {
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
                RuntimeBackendReport::try_dovetail(report).map_err(|err| {
                    format!(
                        "Dovetail backend for language {} produced malformed report: {err}",
                        self.name()
                    )
                })
            },
            RuntimeBackend::Ascent => Err(format!(
                "legacy Ascent runtime is not exposed by Dovetail-backed language {}",
                self.name()
            )),
            other => self.inner.run_backend_report(other, term),
        }
    }

    fn run_ascent_with_facts(
        &self,
        term: &dyn Term,
        facts: &SeedFacts,
    ) -> Result<AscentResults, String> {
        let _ = (term, facts);
        Err(format!(
            "legacy Ascent runtime is not exposed by Dovetail-backed language {}",
            self.name()
        ))
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
            RuntimeBackend::Ascent => Err(format!(
                "legacy Ascent runtime is not exposed by Dovetail-backed language {}",
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
    use dovetail::egraph::{EGraph, ENode};
    use dovetail::extract::Extractor;
    use dovetail::report::report_from_extraction;
    use mettail_runtime::{
        AscentResults, BackendCapabilityDef, LanguageMetadata, RuntimeBackend,
        RuntimeBackendArtifact, RuntimeBackendOutput, SeedFacts, Term,
    };
    use rigail::TropicalWeight;
    use std::collections::HashMap;
    use std::fmt;

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

        fn definition_fingerprint(&self) -> Option<&'static str> {
            Some("dovetail-dummy-definition")
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

    fn compiler_stage<F>(compiler: F) -> DovetailCompilerStage<F>
    where
        F: for<'a> Fn(&'a dyn Term) -> Result<RuntimeDovetailRunReport, String> + Send + Sync,
    {
        DovetailCompilerStage::new("dovetail-dummy-definition", compiler)
    }

    fn complete_report_runner(_term: &dyn Term) -> Result<RuntimeDovetailRunReport, String> {
        Ok(complete_runtime_report())
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
            compiler_stage(|_term| Ok(complete_runtime_report())),
        )
        .expect("matching Dovetail compiler should install");
        let term = language.parse_term("pair(x,y)").expect("parse");

        assert_eq!(language.default_runtime_backend(), Some(RuntimeBackend::Dovetail));
        assert!(language.supports_runtime_backend(RuntimeBackend::Dovetail));
        assert!(!language.supports_runtime_backend(RuntimeBackend::Ascent));
        assert!(!language.supports_runtime_backend(RuntimeBackend::RhoMachine));

        let capabilities = language.runtime_backend_capabilities();
        assert_eq!(capabilities.len(), 1);
        assert_eq!(capabilities[0].backend, RuntimeBackend::Dovetail);
        assert!(capabilities[0].is_default);

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

        assert!(language
            .run_backend_report(RuntimeBackend::Ascent, term.as_ref())
            .expect_err("production Dovetail wrapper must reject explicit Ascent")
            .contains("legacy Ascent runtime is not exposed"));
    }

    #[test]
    fn dovetail_wrapper_rejects_bounded_reports_and_ascent_facts() {
        let language = DovetailRuntimeBackedLanguage::new(
            DummyLanguage,
            compiler_stage(|_term| Ok(bounded_runtime_report())),
        )
        .expect("matching Dovetail compiler should install");
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
            compiler_stage(|_term| Ok(malformed_complete_runtime_report())),
        )
        .expect("matching Dovetail compiler should install");
        let term = language.parse_term("bad-report").expect("parse");

        let err = language
            .run_default_backend_report(term.as_ref())
            .expect_err("malformed complete reports must fail closed");
        assert!(err.contains("produced malformed report"), "{err}");
        assert!(err.contains("term ordinal 99"), "{err}");
    }

    #[test]
    fn production_wrapper_rejects_explicit_ascent_runtime() {
        let language = DovetailRuntimeBackedLanguage::new(
            DummyLanguage,
            compiler_stage(|_term| Ok(complete_runtime_report())),
        )
        .expect("matching Dovetail compiler should install");
        let term = language.parse_term("x").expect("parse");
        let report_err = language
            .run_backend_report(RuntimeBackend::Ascent, term.as_ref())
            .expect_err("production Dovetail wrapper must not expose Ascent");
        assert!(report_err.contains("legacy Ascent runtime is not exposed"), "{report_err}");

        let ascent_err = language
            .run_ascent(term.as_ref())
            .expect_err("production Dovetail wrapper must not forward run_ascent");
        assert!(ascent_err.contains("legacy Ascent runtime is not exposed"), "{ascent_err}");
    }

    #[test]
    fn wrapper_passes_empty_fact_set_to_default_dovetail_report() {
        let language = DovetailRuntimeBackedLanguage::new(
            DummyLanguage,
            compiler_stage(|_term| Ok(complete_runtime_report())),
        )
        .expect("matching Dovetail compiler should install");
        let term = language.parse_term("x").expect("parse");
        let report = language
            .run_default_backend_report_with_facts(term.as_ref(), &HashMap::new())
            .expect("empty fact set matches default Dovetail execution");
        assert_eq!(report.backend(), RuntimeBackend::Dovetail);
    }

    #[test]
    fn dovetail_wrapper_rejects_mismatched_compiler_definition() {
        let err = match DovetailRuntimeBackedLanguage::new(
            DummyLanguage,
            DovetailCompilerStage::new("different-definition", complete_report_runner),
        ) {
            Ok(_) => panic!("mismatched Dovetail compiler must not install"),
            Err(err) => err,
        };

        assert!(
            matches!(err, DovetailRuntimeBackedLanguageError::CompilerDefinitionMismatch { .. }),
            "{err}"
        );
        assert!(err.to_string().contains("different-definition"), "{err}");
    }
}
