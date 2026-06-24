use crate::examples::{Example, ExampleCategory};
use crate::pretty::format_term_pretty;
use crate::registry::LanguageRegistry;
use crate::state::ReplState;
use anyhow::Result;
use colored::Colorize;
use mettail_query::run_query_report as query_run_query_report;
use mettail_runtime::{
    Language, RelationData, RuntimeBackend, RuntimeBackendOutput, RuntimeBackendReport,
    RuntimeDovetailRunReport,
};
use rustyline::error::ReadlineError;
use rustyline::{DefaultEditor, Result as RustyResult};
use std::any::Any;
use std::collections::HashMap;
use std::time::Instant;

/// Extract the term portion from a REPL command line.
///
/// Commands like `exec 2 ! 3` or `step x + y` pass only the term part (`2 ! 3` / `x + y`)
/// to the parser. Parse error positions are relative to this substring, so the error display
/// must use the term input (not the full command line) for correct caret positioning.
fn extract_parsed_input(line: &str) -> &str {
    // Commands that strip a prefix before parsing
    for prefix in &["exec ", "step "] {
        if let Some(rest) = line.strip_prefix(prefix) {
            return rest.trim();
        }
    }
    // Assignment: "name = term" — parser sees the term part
    if let Some(eq_pos) = line.find('=') {
        let before = &line[..eq_pos];
        // Only treat as assignment if before '=' is a simple identifier
        if before
            .trim()
            .chars()
            .all(|c| c.is_alphanumeric() || c == '_')
        {
            return line[eq_pos + 1..].trim();
        }
    }
    // Fallback: use the whole line (query mode, etc.)
    line
}

fn runtime_backend_summary(language: &dyn Language) -> String {
    let capabilities = language.runtime_backend_capabilities();
    if capabilities.is_empty() {
        return "runtime: none installed".to_string();
    }

    capabilities
        .iter()
        .map(|capability| {
            if capability.is_default {
                format!("{} (default)", capability.backend)
            } else {
                capability.backend.to_string()
            }
        })
        .collect::<Vec<_>>()
        .join(", ")
}

#[cfg(test)]
mod tests {
    use super::*;
    use mettail_runtime::{
        AscentResults, BackendCapabilityDef, LanguageMetadata, RuntimeBackendArtifact,
        RuntimeBackendReport, RuntimeChannelObservation, RuntimeDovetailCompleteness,
        RuntimeDovetailDerivationEdge, RuntimeDovetailRunReport, RuntimeDovetailTermRecord,
        RuntimeObservationValue, Term, TermType, VarTypeInfo,
    };
    use std::fmt;

    #[derive(Debug, Clone)]
    struct TestTerm {
        display: &'static str,
        id: u64,
    }

    impl fmt::Display for TestTerm {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            write!(f, "{}", self.display)
        }
    }

    impl Term for TestTerm {
        fn clone_box(&self) -> Box<dyn Term> {
            Box::new(self.clone())
        }

        fn term_id(&self) -> u64 {
            self.id
        }

        fn term_eq(&self, other: &dyn Term) -> bool {
            other
                .as_any()
                .downcast_ref::<TestTerm>()
                .is_some_and(|rhs| rhs.id == self.id && rhs.display == self.display)
        }

        fn as_any(&self) -> &dyn Any {
            self
        }
    }

    struct RhoDefaultMetadata;

    static RHO_DEFAULT_BACKENDS: &[BackendCapabilityDef] = &[
        BackendCapabilityDef {
            backend: RuntimeBackend::RhoMachine,
            is_default: true,
        },
        BackendCapabilityDef {
            backend: RuntimeBackend::Ascent,
            is_default: false,
        },
    ];

    impl LanguageMetadata for RhoDefaultMetadata {
        fn name(&self) -> &'static str {
            "BypassProbe"
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
            RHO_DEFAULT_BACKENDS
        }
    }

    static RHO_DEFAULT_METADATA: RhoDefaultMetadata = RhoDefaultMetadata;

    struct DovetailDefaultMetadata;

    static DOVETAIL_DEFAULT_BACKENDS: &[BackendCapabilityDef] = &[BackendCapabilityDef {
        backend: RuntimeBackend::Dovetail,
        is_default: true,
    }];

    impl LanguageMetadata for DovetailDefaultMetadata {
        fn name(&self) -> &'static str {
            "DovetailProbe"
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
            DOVETAIL_DEFAULT_BACKENDS
        }
    }

    static DOVETAIL_DEFAULT_METADATA: DovetailDefaultMetadata = DovetailDefaultMetadata;

    struct NoRuntimeMetadata;

    impl LanguageMetadata for NoRuntimeMetadata {
        fn name(&self) -> &'static str {
            "ParseOnly"
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
    }

    static NO_RUNTIME_METADATA: NoRuntimeMetadata = NoRuntimeMetadata;

    struct NoRuntimeLanguage;

    impl Language for NoRuntimeLanguage {
        fn name(&self) -> &'static str {
            "ParseOnly"
        }

        fn metadata(&self) -> &'static dyn LanguageMetadata {
            &NO_RUNTIME_METADATA
        }

        fn parse_term(&self, _input: &str) -> Result<Box<dyn Term>, String> {
            Ok(Box::new(TestTerm { display: "parsed", id: 10 }))
        }

        fn parse_term_for_env(&self, input: &str) -> Result<Box<dyn Term>, String> {
            self.parse_term(input)
        }

        fn run_ascent(&self, _term: &dyn Term) -> Result<AscentResults, String> {
            panic!("parse-only REPL test language must fail before any backend runs")
        }

        fn try_direct_eval(&self, _term: &dyn Term) -> Option<Box<dyn Term>> {
            Some(Box::new(TestTerm { display: "direct-eval", id: 11 }))
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

    struct RhoDefaultLanguage;

    impl Language for RhoDefaultLanguage {
        fn name(&self) -> &'static str {
            "BypassProbe"
        }

        fn metadata(&self) -> &'static dyn LanguageMetadata {
            &RHO_DEFAULT_METADATA
        }

        fn parse_term(&self, _input: &str) -> Result<Box<dyn Term>, String> {
            Ok(Box::new(TestTerm { display: "parsed", id: 1 }))
        }

        fn parse_term_for_env(&self, input: &str) -> Result<Box<dyn Term>, String> {
            self.parse_term(input)
        }

        fn run_ascent(&self, _term: &dyn Term) -> Result<AscentResults, String> {
            panic!("REPL exec must not fall back to Ascent for a Rho-default language")
        }

        fn run_backend_report(
            &self,
            backend: RuntimeBackend,
            _term: &dyn Term,
        ) -> Result<RuntimeBackendReport, String> {
            match backend {
                RuntimeBackend::RhoMachine => RuntimeBackendReport::try_observations(
                    RuntimeBackend::RhoMachine,
                    RuntimeBackendArtifact::RhoNormalizedAst,
                    vec![RuntimeChannelObservation::new(
                        "OUT",
                        vec![RuntimeObservationValue::Text("rho-backend".to_string())],
                    )],
                )
                .map_err(|err| err.to_string()),
                other => Err(format!("unexpected backend: {other}")),
            }
        }

        fn try_direct_eval(&self, _term: &dyn Term) -> Option<Box<dyn Term>> {
            Some(Box::new(TestTerm { display: "direct-eval", id: 2 }))
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

    fn dovetail_probe_report() -> RuntimeDovetailRunReport {
        RuntimeDovetailRunReport {
            roots: vec![b"root".to_vec()],
            root_ordinals: vec![0],
            terms: vec![
                RuntimeDovetailTermRecord {
                    ordinal: 0,
                    class_id: 0,
                    key: b"root".to_vec(),
                    op_display: "root".to_string(),
                    weight_display: "0".to_string(),
                    is_root: true,
                },
                RuntimeDovetailTermRecord {
                    ordinal: 1,
                    class_id: 1,
                    key: b"child".to_vec(),
                    op_display: "child".to_string(),
                    weight_display: "0".to_string(),
                    is_root: false,
                },
            ],
            derivation_edges: vec![RuntimeDovetailDerivationEdge {
                ordinal: 0,
                parent_key: b"root".to_vec(),
                child_key: b"child".to_vec(),
                child_index: 0,
            }],
            rule_firings: Vec::new(),
            completeness: RuntimeDovetailCompleteness::Complete,
        }
    }

    struct DovetailDefaultLanguage;

    impl Language for DovetailDefaultLanguage {
        fn name(&self) -> &'static str {
            "DovetailProbe"
        }

        fn metadata(&self) -> &'static dyn LanguageMetadata {
            &DOVETAIL_DEFAULT_METADATA
        }

        fn parse_term(&self, input: &str) -> Result<Box<dyn Term>, String> {
            let display = match input {
                "root" => "root",
                "child" => "child",
                _ => "parsed",
            };
            Ok(Box::new(TestTerm { display, id: 30 }))
        }

        fn parse_term_for_env(&self, input: &str) -> Result<Box<dyn Term>, String> {
            self.parse_term(input)
        }

        fn run_ascent(&self, _term: &dyn Term) -> Result<AscentResults, String> {
            panic!("Dovetail-default REPL test language must not run Ascent")
        }

        fn run_backend_report(
            &self,
            backend: RuntimeBackend,
            _term: &dyn Term,
        ) -> Result<RuntimeBackendReport, String> {
            match backend {
                RuntimeBackend::Dovetail => {
                    RuntimeBackendReport::try_dovetail(dovetail_probe_report())
                        .map_err(|err| err.to_string())
                },
                other => Err(format!("unexpected backend: {other}")),
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
    fn exec_uses_selected_backend_report_instead_of_legacy_direct_eval() {
        let mut registry = LanguageRegistry::new();
        registry.register(Box::new(RhoDefaultLanguage));
        let mut repl = Repl::new(registry).expect("test REPL can be constructed");

        repl.load_language("BypassProbe")
            .expect("test language is registered");
        repl.cmd_exec_term("input")
            .expect("Rho backend observations should execute through exec");

        let report = repl
            .state
            .backend_report()
            .expect("exec stores the selected runtime backend report");
        assert_eq!(report.backend(), RuntimeBackend::RhoMachine);
        assert_eq!(report.artifact(), RuntimeBackendArtifact::RhoNormalizedAst);

        let out = report
            .observations_for_channel("OUT")
            .expect("Rho backend report carries the OUT channel");
        assert_eq!(
            out.membership_fingerprint(),
            std::collections::BTreeSet::from([RuntimeObservationValue::Text(
                "rho-backend".to_string()
            )])
        );
        assert_eq!(format!("{}", repl.state.current_term().unwrap()), "\"rho-backend\"");
    }

    #[test]
    fn registry_runtime_summary_distinguishes_parse_only_and_rho_default_values() {
        let mut registry = LanguageRegistry::new();
        registry.register(Box::new(NoRuntimeLanguage));
        registry.register(Box::new(RhoDefaultLanguage));

        let infos = registry.list_with_runtime();
        let parse_only = infos
            .iter()
            .find(|info| info.name == "ParseOnly")
            .expect("parse-only language should be listed");
        assert_eq!(parse_only.default_backend, None);
        assert!(parse_only.runtime_backends.is_empty());

        let rho_default = infos
            .iter()
            .find(|info| info.name == "BypassProbe")
            .expect("Rho-default language should be listed");
        assert_eq!(rho_default.default_backend, Some(RuntimeBackend::RhoMachine));
        assert!(rho_default
            .runtime_backends
            .iter()
            .any(|capability| capability.backend == RuntimeBackend::RhoMachine
                && capability.is_default));
    }

    #[test]
    fn exec_without_runtime_wrapper_fails_with_dovetail_rho_guidance() {
        let mut registry = LanguageRegistry::new();
        registry.register(Box::new(NoRuntimeLanguage));
        let mut repl = Repl::new(registry).expect("test REPL can be constructed");

        repl.load_language("ParseOnly")
            .expect("test language is registered");
        let err = repl
            .cmd_exec_term("input")
            .expect_err("parse-only language should fail before backend execution");
        let message = err.to_string();
        assert!(message.contains("checked Dovetail/Rho runtime wrapper"), "{message}");
    }

    #[test]
    fn step_and_graph_commands_read_dovetail_derivation_reports() {
        let mut registry = LanguageRegistry::new();
        registry.register(Box::new(DovetailDefaultLanguage));
        let mut repl = Repl::new(registry).expect("test REPL can be constructed");

        repl.load_language("DovetailProbe")
            .expect("test language is registered");
        repl.cmd_step_term("input")
            .expect("Dovetail step should start at the derivation root");

        let report = repl
            .state
            .backend_report()
            .expect("step stores the selected runtime backend report");
        assert_eq!(report.backend(), RuntimeBackend::Dovetail);
        assert_eq!(report.artifact(), RuntimeBackendArtifact::DovetailRunReport);
        assert_eq!(repl.state.current_graph_id(), Some(0));

        repl.cmd_rewrites()
            .expect("Dovetail derivation dependencies should list as graph edges");
        repl.cmd_relation(&["derivation_edges"])
            .expect("Dovetail derivation edge relation should be visible");
        repl.cmd_apply(&["0"])
            .expect("Dovetail graph apply should move to the child derivation");
        assert_eq!(repl.state.current_graph_id(), Some(1));
        assert_eq!(format!("{}", repl.state.current_term().unwrap()), "child");

        repl.cmd_normal_forms()
            .expect("Dovetail extracted roots should be visible as graph normal forms");
        repl.cmd_goto(&["0"])
            .expect("Dovetail goto should navigate to the extracted root");
        assert_eq!(repl.state.current_graph_id(), Some(0));
    }

    #[test]
    fn dovetail_multi_root_graph_entry_is_not_a_report_root() {
        let mut report = dovetail_probe_report();
        report.roots.push(b"other_root".to_vec());
        report.root_ordinals.push(2);
        report.terms.push(RuntimeDovetailTermRecord {
            ordinal: 2,
            class_id: 2,
            key: b"other_root".to_vec(),
            op_display: "other_root".to_string(),
            weight_display: "0".to_string(),
            is_root: true,
        });

        let backend_report = RuntimeBackendReport::try_dovetail(report)
            .expect("multi-root report should satisfy Dovetail shape validation");
        let graph = runtime_graph_view(&backend_report)
            .expect("multi-root Dovetail report should project to a graph");

        assert_eq!(graph.entry_id, Some(DOVETAIL_SYNTHETIC_ROOT_ID));
        let entry = graph.entry_term().expect("synthetic graph entry exists");
        assert_eq!(entry.display, "DovetailRoots([root, other_root])");
        assert!(!entry.is_root);
        assert!(!entry.is_normal_form);

        let roots: Vec<_> = graph
            .terms
            .iter()
            .filter(|term| term.is_root)
            .map(|term| term.display.as_str())
            .collect();
        assert_eq!(roots, vec!["root", "other_root"]);

        let normal_forms: Vec<_> = graph
            .normal_forms()
            .iter()
            .map(|term| term.display.as_str())
            .collect();
        assert_eq!(normal_forms, vec!["root", "other_root"]);
    }

    #[test]
    fn query_command_reads_rho_runtime_report_observations() {
        let mut registry = LanguageRegistry::new();
        registry.register(Box::new(RhoDefaultLanguage));
        let mut repl = Repl::new(registry).expect("test REPL can be constructed");

        repl.load_language("BypassProbe")
            .expect("test language is registered");
        repl.cmd_exec_term("input")
            .expect("Rho backend observations should execute through exec");

        repl.cmd_query("query(value) <-- runtime_observation(OUT, value).")
            .expect("query command should read observation-shaped runtime reports");
    }
}

/// Fallback term used when a displayed normal form cannot be reparsed.
///
/// This keeps REPL state navigable for display/history even when display syntax
/// is not round-trippable through the concrete parser (e.g. large BigInt shown
/// without an explicit literal suffix).
#[derive(Debug, Clone)]
struct DisplayTerm {
    display: String,
    id: u64,
}

impl std::fmt::Display for DisplayTerm {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.display)
    }
}

impl mettail_runtime::Term for DisplayTerm {
    fn clone_box(&self) -> Box<dyn mettail_runtime::Term> {
        Box::new(self.clone())
    }

    fn term_id(&self) -> u64 {
        self.id
    }

    fn term_eq(&self, other: &dyn mettail_runtime::Term) -> bool {
        self.term_id() == other.term_id()
    }

    fn as_any(&self) -> &dyn Any {
        self
    }
}

const DOVETAIL_SYNTHETIC_ROOT_ID: u64 = u64::MAX;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum RuntimeGraphKind {
    AscentRewriteGraph,
    DovetailDerivationGraph,
}

impl RuntimeGraphKind {
    fn edge_relation_name(self) -> &'static str {
        match self {
            RuntimeGraphKind::AscentRewriteGraph => "rewrites",
            RuntimeGraphKind::DovetailDerivationGraph => "derivation_edges",
        }
    }

    fn edge_label(self) -> &'static str {
        match self {
            RuntimeGraphKind::AscentRewriteGraph => "rewrite",
            RuntimeGraphKind::DovetailDerivationGraph => "derivation dependency",
        }
    }
}

#[derive(Debug, Clone)]
struct RuntimeGraphTerm {
    id: u64,
    display: String,
    is_normal_form: bool,
    is_root: bool,
}

#[derive(Debug, Clone)]
struct RuntimeGraphEdge {
    from_id: u64,
    to_id: u64,
    label: Option<String>,
}

#[derive(Debug, Clone)]
struct RuntimeGraphEquivalence {
    term_ids: Vec<u64>,
}

#[derive(Debug, Clone)]
struct RuntimeGraphRelation {
    param_types: Vec<String>,
    tuples: Vec<Vec<String>>,
}

#[derive(Debug, Clone)]
struct RuntimeGraphView {
    kind: RuntimeGraphKind,
    entry_id: Option<u64>,
    terms: Vec<RuntimeGraphTerm>,
    edges: Vec<RuntimeGraphEdge>,
    equivalences: Vec<RuntimeGraphEquivalence>,
    custom_relations: HashMap<String, RuntimeGraphRelation>,
}

impl RuntimeGraphView {
    fn term_by_id(&self, id: u64) -> Option<&RuntimeGraphTerm> {
        self.terms.iter().find(|term| term.id == id)
    }

    fn entry_term(&self) -> Option<&RuntimeGraphTerm> {
        self.entry_id.and_then(|id| self.term_by_id(id))
    }

    fn normal_forms(&self) -> Vec<&RuntimeGraphTerm> {
        self.terms
            .iter()
            .filter(|term| term.is_normal_form)
            .collect()
    }
}

fn runtime_graph_view(report: &RuntimeBackendReport) -> Result<RuntimeGraphView> {
    match report.output() {
        RuntimeBackendOutput::Ascent(results) => {
            let terms = results
                .all_terms
                .iter()
                .map(|term| RuntimeGraphTerm {
                    id: term.term_id,
                    display: term.display.clone(),
                    is_normal_form: term.is_normal_form,
                    is_root: false,
                })
                .collect();
            let edges = results
                .rewrites
                .iter()
                .map(|rewrite| RuntimeGraphEdge {
                    from_id: rewrite.from_id,
                    to_id: rewrite.to_id,
                    label: rewrite.rule_name.clone(),
                })
                .collect();
            let equivalences = results
                .equivalences
                .iter()
                .map(|equivalence| RuntimeGraphEquivalence {
                    term_ids: equivalence.term_ids.clone(),
                })
                .collect();
            let custom_relations = results
                .custom_relations
                .iter()
                .map(|(name, relation)| {
                    (name.clone(), runtime_graph_relation_from_ascent(relation))
                })
                .collect();

            Ok(RuntimeGraphView {
                kind: RuntimeGraphKind::AscentRewriteGraph,
                entry_id: None,
                terms,
                edges,
                equivalences,
                custom_relations,
            })
        },
        RuntimeBackendOutput::Dovetail(dovetail_report) => {
            dovetail_report
                .validate_shape()
                .map_err(|err| anyhow::anyhow!("Dovetail report is malformed: {}", err))?;

            let mut key_to_id = HashMap::with_capacity(dovetail_report.terms.len());
            for term in &dovetail_report.terms {
                key_to_id.insert(term.key.clone(), term.ordinal as u64);
            }

            let mut terms = Vec::with_capacity(
                dovetail_report
                    .terms
                    .len()
                    .saturating_add(usize::from(dovetail_report.root_ordinals.len() != 1)),
            );
            let mut edges = Vec::with_capacity(
                dovetail_report
                    .derivation_edges
                    .len()
                    .saturating_add(dovetail_report.root_ordinals.len().saturating_sub(1)),
            );

            let entry_id = match dovetail_report.root_ordinals.as_slice() {
                [] => None,
                [single] => Some(*single as u64),
                roots => {
                    let display = roots
                        .iter()
                        .filter_map(|ordinal| dovetail_report.terms.get(*ordinal))
                        .map(|term| term.op_display.as_str())
                        .collect::<Vec<_>>()
                        .join(", ");
                    terms.push(RuntimeGraphTerm {
                        id: DOVETAIL_SYNTHETIC_ROOT_ID,
                        display: format!("DovetailRoots([{}])", display),
                        is_normal_form: false,
                        is_root: false,
                    });
                    for (index, ordinal) in roots.iter().copied().enumerate() {
                        edges.push(RuntimeGraphEdge {
                            from_id: DOVETAIL_SYNTHETIC_ROOT_ID,
                            to_id: ordinal as u64,
                            label: Some(format!("root[{index}]")),
                        });
                    }
                    Some(DOVETAIL_SYNTHETIC_ROOT_ID)
                },
            };

            terms.extend(dovetail_report.terms.iter().map(|term| RuntimeGraphTerm {
                id: term.ordinal as u64,
                display: term.op_display.clone(),
                is_normal_form: term.is_root,
                is_root: term.is_root,
            }));

            edges.extend(dovetail_report.derivation_edges.iter().filter_map(|edge| {
                let from_id = key_to_id.get(&edge.parent_key)?;
                let to_id = key_to_id.get(&edge.child_key)?;
                Some(RuntimeGraphEdge {
                    from_id: *from_id,
                    to_id: *to_id,
                    label: Some(format!("child[{}]", edge.child_index)),
                })
            }));

            Ok(RuntimeGraphView {
                kind: RuntimeGraphKind::DovetailDerivationGraph,
                entry_id,
                terms,
                edges,
                equivalences: Vec::new(),
                custom_relations: HashMap::new(),
            })
        },
        RuntimeBackendOutput::Observations(_) => Err(anyhow::anyhow!(
            "Current {} backend report contains runtime observations; this command requires rewrite-graph or derivation-graph evidence.",
            report.backend()
        )),
        _ => Err(anyhow::anyhow!(
            "Current {} backend report contains {}; this command requires rewrite-graph or derivation-graph evidence.",
            report.backend(),
            report.output().kind_name()
        )),
    }
}

fn runtime_graph_relation_from_ascent(relation: &RelationData) -> RuntimeGraphRelation {
    RuntimeGraphRelation {
        param_types: relation.param_types.clone(),
        tuples: relation.tuples.clone(),
    }
}

fn term_from_display_or_fallback(
    language: &dyn Language,
    display: &str,
    graph_id: u64,
) -> Box<dyn mettail_runtime::Term> {
    language.parse_term(display).unwrap_or_else(|_| {
        Box::new(DisplayTerm {
            display: display.to_string(),
            id: graph_id,
        })
    })
}

fn dovetail_report_display(report: &RuntimeDovetailRunReport) -> String {
    let roots = report
        .root_ordinals
        .iter()
        .filter_map(|ordinal| report.terms.get(*ordinal))
        .map(|term| term.op_display.as_str())
        .collect::<Vec<_>>()
        .join(", ");
    format!(
        "DovetailRunReport(completeness={}, roots=[{}], terms={}, edges={})",
        report.completeness,
        roots,
        report.terms.len(),
        report.derivation_edges.len()
    )
}

/// Replace whole-word occurrences of env-bound identifiers in the input with their display form.
/// This allows `x && true` to work when `x = true`, even though the grammar requires `bool:x` for
/// Bool variables (only Int gets bare Ident to avoid reduce-reduce conflicts).
fn pre_substitute_env(input: &str, language: &dyn Language, env: &dyn Any) -> String {
    let bindings = language.list_env(env);
    if bindings.is_empty() {
        return input.to_string();
    }
    // Sort by name length descending so "foobar" is replaced before "foo"
    let mut bindings: Vec<_> = bindings.into_iter().map(|(n, d, _)| (n, d)).collect();
    bindings.sort_by_key(|b| std::cmp::Reverse(b.0.len()));

    let mut result = input.to_string();
    for (name, display) in bindings {
        result = replace_whole_word(&result, &name, &display);
    }
    result
}

/// Replace whole-word occurrences of `needle` with `replacement`.
/// Word boundary: preceded/followed by non-identifier char or start/end.
fn replace_whole_word(haystack: &str, needle: &str, replacement: &str) -> String {
    if needle.is_empty() {
        return haystack.to_string();
    }
    let mut result = String::with_capacity(haystack.len());
    let mut i = 0;
    let haystack_bytes = haystack.as_bytes();
    let needle_bytes = needle.as_bytes();
    let n_len = needle_bytes.len();

    while i <= haystack.len().saturating_sub(n_len) {
        if haystack[i..].starts_with(needle) {
            let at_start = i == 0;
            let at_end = i + n_len == haystack.len();
            let prev_ok = at_start || !is_identifier_char(haystack_bytes[i - 1]);
            let next_ok = at_end || !is_identifier_char(haystack_bytes[i + n_len]);
            if prev_ok && next_ok {
                result.push_str(replacement);
                i += n_len;
                continue;
            }
        }
        result.push(char::from(haystack_bytes[i]));
        i += 1;
    }
    result.push_str(&haystack[i..]);
    result
}

fn is_identifier_char(b: u8) -> bool {
    b.is_ascii_alphanumeric() || b == b'_'
}

/// The main REPL
pub struct Repl {
    state: ReplState,
    registry: LanguageRegistry,
    editor: DefaultEditor,
}

impl Repl {
    /// Create a new REPL
    pub fn new(registry: LanguageRegistry) -> RustyResult<Self> {
        let editor = DefaultEditor::new()?;
        Ok(Self {
            state: ReplState::new(),
            registry,
            editor,
        })
    }

    pub fn name_str(&self) -> Option<&str> {
        self.state.language_name()
    }

    /// Load a language by name (for programmatic use)
    pub fn load_language(&mut self, name: &str) -> Result<()> {
        self.cmd_lang(&[name])
    }

    /// Run the REPL
    pub fn run(&mut self) -> Result<()> {
        self.print_banner();

        loop {
            let prompt = self.make_prompt();
            match self.editor.readline(&prompt) {
                Ok(line) => {
                    self.editor.add_history_entry(&line)?;

                    let line = line.trim();
                    if line.is_empty() {
                        continue;
                    }

                    if let Err(e) = self.handle_command(line) {
                        let error_str = format!("{}", e);
                        // Attempt rich display (works for ParseError strings with L:C: prefix);
                        // falls back to plain "Error: message" for non-parse errors.
                        if crate::pretty::is_parse_error(&error_str) {
                            // Extract the term portion that was actually parsed (after
                            // command prefix like "exec " or "step "). Parser error positions
                            // are relative to this substring, not the full command line.
                            let term_input = extract_parsed_input(line);
                            let display = crate::pretty::format_parse_error_with_context(
                                term_input, &error_str,
                            );
                            eprintln!("{}", display);
                        } else {
                            eprintln!("{} {}", "Error:".red().bold(), error_str);
                        }
                    }
                },
                Err(ReadlineError::Interrupted) => {
                    println!("^C");
                    continue;
                },
                Err(ReadlineError::Eof) => {
                    println!("exit");
                    break;
                },
                Err(err) => {
                    eprintln!("{} {:?}", "Error:".red().bold(), err);
                    break;
                },
            }
        }

        Ok(())
    }

    fn print_banner(&self) {
        println!("{}", "╔════════════════════════════════════════════════════════════╗".cyan());
        println!("{}", "║                   MeTTaIL Term Explorer                    ║".cyan());
        println!("{}", "║                      Version 0.1.0                         ║".cyan());
        println!("{}", "╚════════════════════════════════════════════════════════════╝".cyan());
        println!();
        println!("Type {} for available commands.", "'help'".green());
        println!();
    }

    fn make_prompt(&self) -> String {
        if let Some(language_name) = self.state.language_name() {
            format!("{}> ", language_name.green())
        } else {
            "mettail> ".to_string()
        }
    }

    fn handle_command(&mut self, line: &str) -> Result<()> {
        let parts: Vec<&str> = line.split_whitespace().collect();
        if parts.is_empty() {
            return Ok(());
        }

        // Check for assignment syntax: name = term
        if let Some((name, term_str)) = Self::parse_assignment(line) {
            return self.cmd_assign(&name, &term_str);
        }

        // Query: single rule in Ascent form, e.g. query(result) <-- path(term, result), !rw_proc(result, _).
        if line.contains(" <-- ") {
            return self.cmd_query(line);
        }

        match parts[0] {
            "help" => self.cmd_help(),
            "lang" => self.cmd_lang(&parts[1..]),
            "load-env" => self.cmd_load_env(&parts[1..]),
            "languages" => self.cmd_list_languages(),
            "info" => self.cmd_info(),
            "env" => self.cmd_env(),
            "save" => self.cmd_save(&parts[1..]),
            "clear" => self.cmd_clear(&parts[1..]),
            "clear-all" => self.cmd_clear_all(),
            "term" => self.cmd_term(),
            "type" => self.cmd_type(),
            "typeof" => self.cmd_typeof(&parts[1..]),
            "types" => self.cmd_types(),
            "rewrites" => self.cmd_rewrites(),
            "rewrites-all" => self.cmd_rewrites_all(),
            "equations" => self.cmd_equations(),
            "normal-forms" => self.cmd_normal_forms(),
            "relations" => self.cmd_relations(),
            "relation" => self.cmd_relation(&parts[1..]),
            "apply" => self.cmd_apply(&parts[1..]),
            "goto" => self.cmd_goto(&parts[1..]),
            "example" => self.cmd_example(&parts[1..]),
            "list-examples" => self.cmd_list_examples(self.state.language_name().unwrap()),
            "quit" | "exit" => {
                println!("Goodbye!");
                std::process::exit(0);
                #[allow(unreachable_code)]
                Ok::<(), anyhow::Error>(())
            },
            "exec" => self.cmd_exec_term(line.strip_prefix("exec").unwrap()),
            "step" => self.cmd_step_term(line.strip_prefix("step").unwrap()),
            _ => {
                anyhow::bail!(
                    "Unknown command: '{}'. Type 'help' for available commands.",
                    parts[0]
                )
            },
        }
    }

    /// Parse assignment syntax: name = term
    /// Returns (name, term_string) if it's an assignment, None otherwise
    fn parse_assignment(line: &str) -> Option<(String, String)> {
        // Look for = that's not inside parentheses or brackets
        let mut paren_depth = 0;
        let mut bracket_depth = 0;

        for (i, ch) in line.char_indices() {
            match ch {
                '(' | '{' => paren_depth += 1,
                ')' | '}' => paren_depth -= 1,
                '[' => bracket_depth += 1,
                ']' => bracket_depth -= 1,
                '=' if paren_depth == 0 && bracket_depth == 0 => {
                    let name = line[..i].trim();
                    let term_str = line[i + 1..].trim();

                    // Validate name is a valid identifier (alphanumeric + underscore, starts with letter)
                    if !name.is_empty()
                        && name
                            .chars()
                            .next()
                            .map(|c| c.is_alphabetic())
                            .unwrap_or(false)
                        && name.chars().all(|c| c.is_alphanumeric() || c == '_')
                        && !term_str.is_empty()
                    {
                        return Some((name.to_string(), term_str.to_string()));
                    }
                },
                _ => {},
            }
        }
        None
    }

    fn cmd_help(&self) -> Result<()> {
        println!();
        println!("{}", "Available commands:".bold());
        println!();
        println!("{}", "  Language Management:".yellow());
        println!("    {}        Show available languages", "languages".green());
        println!("    {}  Open language", "lang <name>".green());
        println!("    {}              Show language information", "{lang_name}> info".green());
        println!();
        println!("{}", "  Term Input:".yellow());
        println!(
            "    {}    Execute a program with the selected runtime backend",
            "exec <term>".green()
        );
        println!(
            "    {}    Step-by-step: show initial term, use {} to reduce",
            "step <term>".green(),
            "apply 0".cyan()
        );
        println!("    {}    Load example program", "example <name>".green());
        println!("    {}    List available examples", "list-examples".green());
        println!();
        println!("{}", "  Environment:".yellow());
        println!("    {} Define a named term", "<name> = <term>".green());
        println!("    {}      Save current term to environment", "save <name>".green());
        println!("    {}               Show all environment bindings", "env".green());
        println!("    {}    Remove a binding", "clear <name>".green());
        println!("    {}         Clear all bindings", "clear-all".green());
        println!("    {} Load declarations from file", "load-env <file>".green());
        println!();
        println!("{}", "  Type Inspection:".yellow());
        println!("    {}              Show type of current term", "type".green());
        println!("    {}             Show all variable types", "types".green());
        println!("    {}  Show type of specific variable", "typeof <var>".green());
        println!();
        println!("{}", "  Navigation:".yellow());
        println!("    {}           List rewrites from current term", "rewrites".green());
        println!("    {}         List all rewrites", "rewrites-all".green());
        println!("    {}        Show normal forms", "normal-forms".green());
        println!(
            "    {} Apply one rewrite from current term (use after {})",
            "apply <N>".green(),
            "step".cyan()
        );
        println!("    {}              Go to normal form N", "goto <N>".green());
        println!();
        println!("{}", "  Relations:".yellow());
        println!("    {}         List all computed relations", "relations".green());
        println!("    {} Show tuples in a relation", "relation <name>".green());
        println!();
        println!("{}", "  Query:".yellow());
        println!(
            "    {}  Run a Datalog rule over the current runtime report (e.g. {}).",
            "head(args) <-- body.".green(),
            "query(result) <-- path(current_term, result), !rw_proc(result, _)".dimmed()
        );
        println!();
        println!("{}", "  General:".yellow());
        println!("    {}              Show this help", "help".green());
        println!("    {}        Exit REPL", "quit, exit".green());
        println!();
        Ok(())
    }

    fn cmd_lang(&mut self, args: &[&str]) -> Result<()> {
        if args.is_empty() {
            anyhow::bail!("Usage: lang <language-name>");
        }

        let language_name = args[0];

        if !self.registry.contains(language_name) {
            anyhow::bail!(
                "Language '{}' not found. Use 'list-languages' to see available languages.",
                language_name
            );
        }

        println!("Loading language: {}", language_name.green());

        // Get the theory from the registry (for display info)
        let language = self.registry.get(language_name)?;

        // Print theory info
        // println!("  ✓ {} categories", theory.categories().len());
        // println!("  ✓ {} constructors", theory.constructor_count());
        // println!("  ✓ {} equations", theory.equation_count());
        // println!("  ✓ {} rewrite rules", theory.rewrite_count());

        // Store the theory name in state
        self.state.load_language(language.name());

        // Try to auto-load environment from repl/src/examples/{theory_name}.txt
        let env_file = format!("repl/src/examples/{}.txt", language_name);
        if std::path::Path::new(&env_file).exists() {
            match self.load_env_from_file(&env_file) {
                Ok(count) if count > 0 => {
                    println!("  [{} definitions from {}]", count, env_file);
                },
                Ok(_) => {}, // Empty file, no message
                Err(e) => {
                    println!("  {} Failed to load {}: {}", "⚠".yellow(), env_file, e);
                },
            }
        }
        println!();

        println!("{} Language loaded successfully!", "✓".green());
        println!("  {}  selected runtime backend (result)", "'exec <term>'".cyan());
        println!(
            "  {}  step-by-step, then {} to reduce",
            "'step <term>'".cyan(),
            "apply 0".cyan()
        );
        println!();

        Ok(())
    }

    fn cmd_list_languages(&self) -> Result<()> {
        println!();
        println!("{}", "Available languages:".bold());
        println!();

        let languages = self.registry.list_with_runtime();
        if languages.is_empty() {
            println!("  {}", "No languages available.".yellow());
            println!("  {}", "Build mettail-examples first with: cargo build".dimmed());
        } else {
            for language in languages {
                let runtime = if language.runtime_backends.is_empty() {
                    "runtime: none installed".dimmed()
                } else if let Some(default) = language.default_backend {
                    format!("runtime: {} default", default).dimmed()
                } else {
                    "runtime: no default".dimmed()
                };
                println!("  - {}  {}", language.name.green(), runtime);
            }
        }

        println!();
        Ok(())
    }

    fn cmd_info(&self) -> Result<()> {
        if let Some(language_name) = self.state.language_name() {
            let language = self.registry.get(language_name)?;
            let meta = language.metadata();

            println!();
            println!("{}", "═".repeat(70).cyan());
            println!("{:^70}", format!("{} Language", meta.name()).bold());
            println!("{}", "═".repeat(70).cyan());

            println!();
            println!("{}", "RUNTIME".yellow().bold());
            println!("  {}", runtime_backend_summary(language).green());
            if language.selected_default_runtime_backend().is_none() {
                println!(
                    "  {}",
                    "No production runtime wrapper is installed for this language value.".dimmed()
                );
            }

            // Types
            println!();
            println!("{}", "TYPES".yellow().bold());
            for ty in meta.types() {
                let primary = if ty.is_primary { " (primary)" } else { "" };
                let native = ty
                    .native_type
                    .map(|t| format!(" = {}", t))
                    .unwrap_or_default();
                println!("  {}{}{}", ty.name.cyan(), native.dimmed(), primary.dimmed());
            }

            // Terms grouped by type - format: [Label] syntax:Type -| context
            println!();
            println!("{} ({})", "TERMS".yellow().bold(), meta.terms().len());
            for ty in meta.types() {
                let terms: Vec<_> = meta
                    .terms()
                    .iter()
                    .filter(|t| t.type_name == ty.name)
                    .collect();
                if !terms.is_empty() {
                    println!("  {}:", ty.name);
                    for term in terms {
                        let label = format!("[{}]", term.name).cyan();

                        // Build type context from fields
                        let ctx: Vec<String> = term
                            .fields
                            .iter()
                            .map(|f| format!("{}:{}", f.name, f.ty))
                            .collect();

                        let judgement = if ctx.is_empty() {
                            format!("{}:{}", term.syntax, term.type_name)
                        } else {
                            format!(
                                "{}:{} {} {}",
                                term.syntax,
                                term.type_name,
                                "-|".dimmed(),
                                ctx.join(", ")
                            )
                        };

                        println!("    {} {}", label, judgement.green());

                        // Stage 3.27a (2026-05-04): surface doc-comment
                        // text from `///` lines preceding the rule. Multi-line
                        // descriptions are indented to align under the term row.
                        if let Some(desc) = term.description {
                            for line in desc.lines() {
                                println!("      {}", line.dimmed());
                            }
                        }
                    }
                }
            }

            // Equations - format: [conditions] lhs = rhs
            println!();
            println!("{} ({})", "EQUATIONS".yellow().bold(), meta.equations().len());
            for eq in meta.equations() {
                let cond_str = if eq.conditions.is_empty() {
                    String::new()
                } else {
                    format!("{} {} ", eq.conditions.join(", "), "|-".dimmed())
                };
                println!("  {}{} = {}", cond_str, eq.lhs.green(), eq.rhs.green());
            }

            // Rewrites - format: [premise] lhs ~> rhs
            println!();
            println!("{} ({})", "REWRITES".yellow().bold(), meta.rewrites().len());
            for rw in meta.rewrites() {
                let mut parts = Vec::new();

                // Add freshness conditions
                if !rw.conditions.is_empty() {
                    parts.push(rw.conditions.join(", "));
                }

                // Add premise (congruence rule)
                if let Some((s, t)) = rw.premise {
                    parts.push(format!("{} ~> {}", s, t));
                }

                let prefix = if parts.is_empty() {
                    String::new()
                } else {
                    format!("{} {} ", parts.join(", "), "|-".dimmed())
                };

                // Add optional name
                let name_str = rw
                    .name
                    .map(|n| format!("[{}] ", n).cyan().to_string())
                    .unwrap_or_default();

                println!("  {}{}{} ~> {}", name_str, prefix, rw.lhs.green(), rw.rhs.green());
            }

            // Logic - custom relations and rules
            let logic_relations = meta.logic_relations();
            let logic_rules = meta.logic_rules();
            if !logic_relations.is_empty() || !logic_rules.is_empty() {
                println!();
                println!("{}", "LOGIC".yellow().bold());

                // Relations
                if !logic_relations.is_empty() {
                    println!("  {}:", "Relations".dimmed());
                    for rel in logic_relations {
                        let signature = format!("{}({})", rel.name, rel.param_types.join(", "));
                        println!("    {}", signature.cyan());
                    }
                }

                // Rules
                if !logic_rules.is_empty() {
                    println!("  {}:", "Rules".dimmed());
                    for rule in logic_rules {
                        println!("    {}", rule.rule.green());
                    }
                }
            }

            println!();
            println!("{}", "═".repeat(70).cyan());
            println!();
        } else {
            println!("{} No language loaded. Use 'lang <name>' first.", "Info:".yellow());
        }
        Ok(())
    }

    // === Environment Commands ===

    fn cmd_assign(&mut self, name: &str, term_str: &str) -> Result<()> {
        let language_name = self
            .state
            .language_name()
            .ok_or_else(|| anyhow::anyhow!("No language loaded. Use 'lang <language>' first."))?;

        let language = self.registry.get(language_name)?;

        // Parse the term WITHOUT clearing var cache
        // This allows shared variables across env definitions (e.g., same `n` in multiple terms)
        let term = language
            .parse_term_for_env(term_str)
            .map_err(|e| anyhow::anyhow!("{}", e))?;

        // Ensure environment exists
        let env = self.state.ensure_environment(|| language.create_env());

        // Add to environment
        language
            .add_to_env(env, name, term.as_ref())
            .map_err(|e| anyhow::anyhow!("{}", e))?;

        println!("{} {} added to environment", "✓".green(), name.cyan());
        Ok(())
    }

    fn cmd_env(&self) -> Result<()> {
        let language_name = self
            .state
            .language_name()
            .ok_or_else(|| anyhow::anyhow!("No language loaded. Use 'lang <language>' first."))?;

        let language = self.registry.get(language_name)?;

        println!();
        println!("{}", "Environment:".bold());

        if let Some(env) = self.state.environment() {
            if language.is_env_empty(env) {
                println!("  {}", "(empty)".dimmed());
            } else {
                let bindings = language.list_env(env);
                let mut last_comment: Option<&str> = None;

                for (name, value, comment) in &bindings {
                    // Print section comment if it's different from the last one
                    if let Some(c) = comment {
                        if last_comment != Some(c.as_str()) {
                            println!();
                            println!("  {}", format!("// {}", c).dimmed());
                            last_comment = Some(c.as_str());
                        }
                    } else if last_comment.is_some() {
                        // No comment on this item, reset section tracking
                        last_comment = None;
                    }
                    println!("  {} = {}", name.cyan(), value.green());
                }
            }
        } else {
            println!("  {}", "(empty)".dimmed());
        }

        println!();
        Ok(())
    }

    fn cmd_clear(&mut self, args: &[&str]) -> Result<()> {
        if args.is_empty() {
            anyhow::bail!("Usage: clear <name>");
        }

        let name = args[0];

        let language_name = self
            .state
            .language_name()
            .ok_or_else(|| anyhow::anyhow!("No language loaded."))?;

        let language = self.registry.get(language_name)?;

        if let Some(env) = self.state.environment_mut() {
            if language
                .remove_from_env(env, name)
                .map_err(|e| anyhow::anyhow!("{}", e))?
            {
                println!("{} {} removed from environment", "✓".green(), name.cyan());
            } else {
                println!("{} {} not found in environment", "⚠".yellow(), name);
            }
        } else {
            println!("{} Environment is empty", "⚠".yellow());
        }

        Ok(())
    }

    fn cmd_clear_all(&mut self) -> Result<()> {
        let language_name = self
            .state
            .language_name()
            .ok_or_else(|| anyhow::anyhow!("No language loaded."))?;

        let language = self.registry.get(language_name)?;

        if let Some(env) = self.state.environment_mut() {
            language.clear_env(env);
            println!("{} Environment cleared", "✓".green());
        } else {
            println!("{} Environment is already empty", "⚠".yellow());
        }

        Ok(())
    }

    /// Save the current term to the environment with a given name
    fn cmd_save(&mut self, args: &[&str]) -> Result<()> {
        if args.is_empty() {
            anyhow::bail!("Usage: save <name>");
        }

        let name = args[0];

        // Validate name is a valid identifier
        if !name
            .chars()
            .next()
            .map(|c| c.is_alphabetic())
            .unwrap_or(false)
            || !name.chars().all(|c| c.is_alphanumeric() || c == '_')
        {
            anyhow::bail!("Invalid identifier: '{}'", name);
        }

        let language_name = self
            .state
            .language_name()
            .ok_or_else(|| anyhow::anyhow!("No language loaded."))?;

        // Clone the current term to release the borrow on self.state
        let current_term = self
            .state
            .current_term()
            .ok_or_else(|| anyhow::anyhow!("No current term. Use 'term: <expr>' first."))?
            .clone_box();

        let language = self.registry.get(language_name)?;

        // Ensure environment exists
        self.state.ensure_environment(|| language.create_env());

        // Add the current term to the environment
        if let Some(env) = self.state.environment_mut() {
            language
                .add_to_env(env, name, current_term.as_ref())
                .map_err(|e| anyhow::anyhow!("{}", e))?;
            println!("{} {} added to environment", "✓".green(), name.cyan());
        }

        Ok(())
    }

    /// Load term declarations from a file
    fn cmd_load_env(&mut self, args: &[&str]) -> Result<()> {
        if args.is_empty() {
            anyhow::bail!("Usage: load-env <file>");
        }

        let file_path = args[0];

        match self.load_env_from_file(file_path) {
            Ok(count) => {
                if count > 0 {
                    println!(
                        "{} Loaded {} declaration(s) from '{}'",
                        "✓".green(),
                        count,
                        file_path
                    );
                } else {
                    println!("{} No declarations found in '{}'", "ℹ".blue(), file_path);
                }
                Ok(())
            },
            Err(e) => Err(e),
        }
    }

    /// Helper to load environment from a file, returns count of loaded declarations
    fn load_env_from_file(&mut self, file_path: &str) -> Result<usize> {
        let language_name = self
            .state
            .language_name()
            .ok_or_else(|| anyhow::anyhow!("No language loaded. Use 'lang <language>' first."))?;

        let language = self.registry.get(language_name)?;

        // Ensure environment exists
        self.state.ensure_environment(|| language.create_env());

        // Read the file
        let content = std::fs::read_to_string(file_path)
            .map_err(|e| anyhow::anyhow!("Failed to read file '{}': {}", file_path, e))?;

        let mut count = 0;
        let mut errors = Vec::new();
        // Track the most recent comment block to associate with the next definition
        let mut pending_comment: Option<String> = None;

        for (line_num, line) in content.lines().enumerate() {
            let line = line.trim();

            // Handle empty lines - they break comment association
            if line.is_empty() {
                continue;
            }

            // Handle comments - collect them for the next definition
            if line.starts_with("//") {
                let comment_text = line.trim_start_matches("//").trim();
                pending_comment = Some(comment_text.to_string());
                continue;
            }
            if line.starts_with('#') {
                let comment_text = line.trim_start_matches('#').trim();
                pending_comment = Some(comment_text.to_string());
                continue;
            }

            // Try to parse as assignment
            if let Some((name, term_str)) = Self::parse_assignment(line) {
                // Parse the term (using parse_term_for_env to share variable IDs)
                match language.parse_term_for_env(&term_str) {
                    Ok(term) => {
                        if let Some(env) = self.state.environment_mut() {
                            if let Err(e) = language.add_to_env(env, &name, term.as_ref()) {
                                errors.push(format!("Line {}: {}", line_num + 1, e));
                            } else {
                                // Store the comment if there was one
                                if let Some(comment) = pending_comment.take() {
                                    let _ = language.set_env_comment(env, &name, comment);
                                }
                                count += 1;
                            }
                        }
                    },
                    Err(e) => {
                        errors.push(format!(
                            "Line {}: Failed to parse '{}': {}",
                            line_num + 1,
                            name,
                            e
                        ));
                    },
                }
            } else {
                errors.push(format!("Line {}: Invalid assignment syntax", line_num + 1));
            }

            // Clear pending comment after processing a definition (whether successful or not)
            pending_comment = None;
        }

        // Report errors if any
        if !errors.is_empty() {
            println!();
            println!("{}", "Errors:".red());
            for error in errors {
                println!("  {}", error);
            }
        }

        Ok(count)
    }

    fn cmd_term(&mut self) -> Result<()> {
        println!("{}", "Current term:".bold());
        if let Some(term) = self.state.current_term() {
            let formatted = format_term_pretty(&format!("{}", term));
            println!("{}", formatted.cyan());
        } else {
            println!("{}", "(none)".dimmed());
        }
        println!();
        Ok(())
    }

    // === Type Inspection Commands ===

    fn cmd_type(&self) -> Result<()> {
        let language_name = self
            .state
            .language_name()
            .ok_or_else(|| anyhow::anyhow!("No language loaded. Use 'lang <language>' first."))?;

        let language = self.registry.get(language_name)?;

        println!();
        println!("{}", "Term type:".bold());

        if let Some(term) = self.state.current_term() {
            if term.as_any().is::<DisplayTerm>() {
                println!("  {}", "(type unavailable for non-roundtrippable display term)".dimmed());
                println!();
                return Ok(());
            }
            let term_type = language.infer_term_type(term);
            println!("  {}", format!("{}", term_type).cyan());
        } else {
            println!("  {}", "(no term loaded)".dimmed());
        }

        println!();
        Ok(())
    }

    fn cmd_typeof(&self, args: &[&str]) -> Result<()> {
        if args.is_empty() {
            anyhow::bail!("Usage: typeof <variable-name>");
        }

        let var_name = args[0];

        let language_name = self
            .state
            .language_name()
            .ok_or_else(|| anyhow::anyhow!("No language loaded. Use 'lang <language>' first."))?;

        let language = self.registry.get(language_name)?;

        println!();

        if let Some(term) = self.state.current_term() {
            if term.as_any().is::<DisplayTerm>() {
                println!(
                    "{}",
                    "Type information unavailable for non-roundtrippable display term.".yellow()
                );
                println!();
                return Ok(());
            }
            if let Some(var_type) = language.infer_var_type(term, var_name) {
                println!("{} : {}", var_name.cyan(), format!("{}", var_type).green());
            } else {
                println!(
                    "{}",
                    format!("Variable '{}' not found in current term", var_name).yellow()
                );
            }
        } else {
            println!("{}", "(no term loaded)".dimmed());
        }

        println!();
        Ok(())
    }

    fn cmd_types(&self) -> Result<()> {
        let language_name = self
            .state
            .language_name()
            .ok_or_else(|| anyhow::anyhow!("No language loaded. Use 'lang <language>' first."))?;

        let language = self.registry.get(language_name)?;

        println!();

        if let Some(term) = self.state.current_term() {
            if term.as_any().is::<DisplayTerm>() {
                println!("{} {}", "Free variables:".bold(), "(unavailable)".dimmed());
                println!();
                println!(
                    "{} {}",
                    "Term type:".bold(),
                    "(unavailable for non-roundtrippable display term)".dimmed()
                );
                println!();
                return Ok(());
            }
            // Get term type
            let term_type = language.infer_term_type(term);

            // Get all variable types
            let var_types = language.infer_var_types(term);

            if var_types.is_empty() {
                println!("{}", "Free variables:".bold());
                println!("  {}", "(none - all variables are bound)".dimmed());
            } else {
                println!("{}", "Free variables:".bold());
                for var_info in &var_types {
                    println!("  {} : {}", var_info.name.cyan(), format!("{}", var_info.ty).green());
                }
            }

            println!();
            println!("{}", "Term type:".bold());
            println!("  {}", format!("{}", term_type).cyan());
        } else {
            println!("{}", "(no term loaded)".dimmed());
        }

        println!();
        Ok(())
    }

    fn cmd_exec_term(&mut self, term_str: &str) -> Result<()> {
        self.exec_or_step_term(term_str.trim(), /* step_mode: */ false)
    }

    /// Step-by-step execution: run Ascent but leave current term at the initial term
    /// so the user can type `apply 0` to apply one rewrite at a time.
    /// Step mode requires an Ascent-shaped graph so the user always sees the initial
    /// term and can apply rewrites.
    fn cmd_step_term(&mut self, term_str: &str) -> Result<()> {
        self.exec_or_step_term(term_str.trim(), /* step_mode: */ true)
    }

    /// Shared parse + substitute + selected backend execution.
    ///
    /// `exec` always uses the language's selected default runtime backend so
    /// non-Ascent backends can return their checked runtime reports. `step`
    /// requires the selected backend to produce an Ascent-shaped graph because
    /// graph-navigation commands operate over Ascent results.
    fn exec_or_step_term(&mut self, term_str: &str, step_mode: bool) -> Result<()> {
        let language_name = self
            .state
            .language_name()
            .ok_or_else(|| anyhow::anyhow!("No language loaded. Use 'lang <language>' first."))?;

        let language = self.registry.get(language_name)?;

        println!();
        let trimmed = term_str.trim();
        // If input is a single identifier and it's bound in the env, use the stored term.
        // This avoids parsing "z" as e.g. IVar(z) when z is bound as a Proc, which would leave
        // the variable unsubstituted and panic on eval.
        let (term, from_env) = if !trimmed.is_empty()
            && trimmed
                .chars()
                .all(|c| c.is_alphabetic() || c == '_' || c.is_ascii_digit())
            && trimmed
                .chars()
                .next()
                .map(|c| c.is_alphabetic() || c == '_')
                .unwrap_or(false)
        {
            if let Some(env) = self.state.environment() {
                if let Some(env_term) = language.get_env_term(env, trimmed) {
                    (env_term, true)
                } else {
                    print!("Parsing... ");
                    let t = language
                        .parse_term_for_env(term_str)
                        .map_err(|e| anyhow::anyhow!("{}", e))?;
                    println!("{}", "✓".green());
                    (t, false)
                }
            } else {
                print!("Parsing... ");
                let t = language
                    .parse_term_for_env(term_str)
                    .map_err(|e| anyhow::anyhow!("{}", e))?;
                println!("{}", "✓".green());
                (t, false)
            }
        } else {
            print!("Parsing... ");
            let t = language
                .parse_term_for_env(term_str)
                .map_err(|e| anyhow::anyhow!("{}", e))?;
            println!("{}", "✓".green());
            (t, false)
        };
        if from_env {
            println!("{}", "✓ Resolved from environment".green());
        }

        let term = if let Some(env) = self.state.environment() {
            if !language.is_env_empty(env) {
                print!("Substituting environment... ");
                let substituted = if step_mode {
                    language
                        .substitute_env_preserve_structure(term.as_ref(), env)
                        .map_err(|e| anyhow::anyhow!("{}", e))?
                } else {
                    language
                        .substitute_env(term.as_ref(), env)
                        .map_err(|e| anyhow::anyhow!("{}", e))?
                };
                println!("{}", "✓".green());
                substituted
            } else {
                term
            }
        } else {
            term
        };

        // Normalize (beta-reduce Apply/MApply of Lam/MLam) before evaluation
        let term = language.normalize_term(term.as_ref());

        // Execute using the language's selected backend.
        let backend = language.selected_default_runtime_backend().ok_or_else(|| {
            anyhow::anyhow!(
                "language {} does not advertise a default runtime backend. Raw generated languages are parse/introspection substrates; install a checked Dovetail/Rho runtime wrapper before executing them.",
                language.name()
            )
        })?;
        // Step mode needs graph/derivation evidence; the RhoMachine backend yields runtime
        // observations, not a navigable graph. When the default backend is RhoMachine and the
        // language also supports the Dovetail backend, step against the Dovetail derivation graph
        // instead of bailing (Layer 1: a pure-fold term shows its fold derivation; a pure-COMM
        // term yields a trivial root — the reactive COMM stepper, Layer 2, refines such terms
        // into a live step trace). Bail only when no graph-capable backend exists.
        let start_time = Instant::now();
        let report = if step_mode && backend == RuntimeBackend::RhoMachine {
            if language.supports_runtime_backend(RuntimeBackend::Dovetail) {
                print!("Running {} backend (step)... ", RuntimeBackend::Dovetail);
                language
                    .run_backend_report(RuntimeBackend::Dovetail, term.as_ref())
                    .map_err(|e| anyhow::anyhow!("{}", e))?
            } else {
                anyhow::bail!(
                    "step mode requires rewrite-graph or derivation-graph evidence; the selected default backend is {} and the language exposes no graph-capable backend. Use 'exec' for runtime observations.",
                    backend
                );
            }
        } else {
            print!("Running {} backend... ", backend);
            language
                .run_default_backend_report(term.as_ref())
                .map_err(|e| anyhow::anyhow!("{}", e))?
        };
        let end_time = Instant::now();
        println!("Time taken: {:?}", end_time.duration_since(start_time));
        println!("{}", "Done!".green());

        let initial_id = term.term_id();

        match report.output() {
            RuntimeBackendOutput::Ascent(results) => {
                println!();
                println!("Computed:");
                println!("  - {} terms", results.all_terms.len());
                println!("  - {} rewrites", results.rewrites.len());
                println!("  - {} normal forms", results.normal_forms_iter().count());
                println!();

                if step_mode {
                    // Step: always show initial term so user can apply rewrites one by one
                    let available = results.rewrites_from_iter(initial_id).count();
                    println!("{}", "Current term (initial):".bold());
                    let formatted = format_term_pretty(&format!("{}", term));
                    println!("{}", formatted.cyan());
                    println!();
                    self.state
                        .set_term_with_report(term, report.clone(), initial_id)?;
                    if available > 0 {
                        println!(
                            "  Use {} to apply a rewrite ({} available).",
                            "apply 0".cyan(),
                            available
                        );
                    } else {
                        println!("  No rewrites from this term (already a normal form).");
                    }
                } else {
                    // Exec: show normal forms reachable from the initial term.
                    //
                    // Phase F.12.A (2026-05-20): when the parsed term is an
                    // `Ambiguous` wrapper, `initial_id` (the wrapper hash) is
                    // structurally absent from `results.all_terms`. Use the
                    // multi-source helper which seeds from each exact `rewrite_seeds()`
                    // alt and preserves every reachable NF. For unambiguous inputs the default trait
                    // impl returns one legacy seed and behavior is
                    // identical to the prior single-source call.
                    let seeds = term.rewrite_seeds();
                    let reachable_nfs: Vec<(u64, String)> = results
                        .normal_forms_reachable_from_rewrite_seeds(&seeds)
                        .into_iter()
                        .map(|nf| (nf.term_id, nf.display.clone()))
                        .collect();
                    if reachable_nfs.len() == 1 {
                        let (nf_id, nf_display) = &reachable_nfs[0];
                        let result_term: Box<dyn mettail_runtime::Term> = match language
                            .parse_term(nf_display)
                        {
                            Ok(t) => t,
                            Err(_) => {
                                Box::new(DisplayTerm { display: nf_display.clone(), id: *nf_id })
                            },
                        };
                        println!("{}", "Current term (result):".bold());
                        let formatted = format_term_pretty(nf_display);
                        println!("{}", formatted.cyan());
                        println!();
                        self.state
                            .set_term_with_report(result_term, report.clone(), *nf_id)?;
                        return Ok(());
                    }
                    if !reachable_nfs.is_empty() {
                        println!("{}", "Current terms (results):".bold());
                        for (idx, (_, display)) in reachable_nfs.iter().enumerate() {
                            println!("  {})", idx.to_string().cyan());
                            let formatted = format_term_pretty(display);
                            for line in formatted.lines() {
                                println!("    {}", line.cyan());
                            }
                            println!();
                        }

                        let ambiguous_display = format!(
                            "Ambiguous([{}])",
                            reachable_nfs
                                .iter()
                                .map(|(_, display)| display.as_str())
                                .collect::<Vec<_>>()
                                .join(", ")
                        );
                        let ambiguous_id = {
                            use std::collections::hash_map::DefaultHasher;
                            use std::hash::{Hash, Hasher};
                            let mut hasher = DefaultHasher::new();
                            for nf in &reachable_nfs {
                                nf.hash(&mut hasher);
                            }
                            hasher.finish()
                        };
                        let result_term: Box<dyn mettail_runtime::Term> = Box::new(DisplayTerm {
                            display: ambiguous_display,
                            id: ambiguous_id,
                        });
                        self.state.set_term_with_report(
                            result_term,
                            report.clone(),
                            ambiguous_id,
                        )?;
                        return Ok(());
                    }
                    println!("{}", "Current term:".bold());
                    let formatted = format_term_pretty(&format!("{}", term));
                    println!("{}", formatted.cyan());
                    println!();
                    self.state
                        .set_term_with_report(term, report.clone(), initial_id)?;
                }
            },
            RuntimeBackendOutput::Observations(observations) => {
                if step_mode {
                    anyhow::bail!(
                        "step mode requires rewrite-graph or derivation-graph evidence; {} returned runtime observations",
                        backend
                    );
                }

                println!();
                println!("Computed:");
                println!("  - backend: {}", report.backend());
                println!("  - artifact: {}", report.artifact());
                println!("  - {} observation channel(s)", observations.len());
                for observation in observations {
                    let rendered_values = observation
                        .values
                        .iter()
                        .map(|value| format!("{}", value))
                        .collect::<Vec<_>>()
                        .join(", ");
                    println!(
                        "    {}: [{}] ({} value(s))",
                        observation.channel.cyan(),
                        rendered_values,
                        observation.observed_count()
                    );
                }
                println!();

                let display = if observations.len() == 1 && observations[0].values.len() == 1 {
                    format!("{}", observations[0].values[0])
                } else {
                    let channels = observations
                        .iter()
                        .map(|observation| {
                            let values = observation
                                .values
                                .iter()
                                .map(|value| format!("{}", value))
                                .collect::<Vec<_>>()
                                .join(", ");
                            format!("{}: [{}]", observation.channel, values)
                        })
                        .collect::<Vec<_>>()
                        .join(", ");
                    format!("RuntimeObservations({channels})")
                };
                let result_id = {
                    use std::collections::hash_map::DefaultHasher;
                    use std::hash::{Hash, Hasher};
                    let mut hasher = DefaultHasher::new();
                    report.backend().hash(&mut hasher);
                    report.artifact().hash(&mut hasher);
                    display.hash(&mut hasher);
                    hasher.finish()
                };

                println!("{}", "Current term (result):".bold());
                println!("{}", format_term_pretty(&display).cyan());
                println!();

                let result_term: Box<dyn mettail_runtime::Term> =
                    Box::new(DisplayTerm { display, id: result_id });
                self.state
                    .set_term_with_report(result_term, report.clone(), result_id)?;
            },
            RuntimeBackendOutput::Dovetail(dovetail_report) => {
                println!();
                println!("Computed:");
                println!("  - backend: {}", report.backend());
                println!("  - artifact: {}", report.artifact());
                println!("  - completeness: {}", dovetail_report.completeness);
                println!("  - {} root(s)", dovetail_report.roots.len());
                println!("  - {} term record(s)", dovetail_report.terms.len());
                println!("  - {} derivation edge(s)", dovetail_report.derivation_edges.len());
                println!();

                let display = dovetail_report_display(dovetail_report);
                let summary_id = {
                    use std::collections::hash_map::DefaultHasher;
                    use std::hash::{Hash, Hasher};
                    let mut hasher = DefaultHasher::new();
                    report.backend().hash(&mut hasher);
                    report.artifact().hash(&mut hasher);
                    display.hash(&mut hasher);
                    hasher.finish()
                };

                let graph = runtime_graph_view(&report)?;
                let current = graph.entry_term().cloned().unwrap_or(RuntimeGraphTerm {
                    id: summary_id,
                    display,
                    is_normal_form: true,
                    is_root: false,
                });

                let heading = if step_mode {
                    "Current derivation root:"
                } else {
                    "Current Dovetail result:"
                };
                println!("{}", heading.bold());
                println!("{}", format_term_pretty(&current.display).cyan());
                println!();

                let available = graph
                    .edges
                    .iter()
                    .filter(|edge| edge.from_id == current.id)
                    .count();
                if step_mode {
                    if available > 0 {
                        println!(
                            "  Use {} to inspect a derivation dependency ({} available).",
                            "apply 0".cyan(),
                            available
                        );
                    } else {
                        println!("  No derivation dependencies from this node.");
                    }
                }

                let result_term =
                    term_from_display_or_fallback(language, &current.display, current.id);
                self.state
                    .set_term_with_report(result_term, report.clone(), current.id)?;
            },
            _ => {
                anyhow::bail!("{} backend returned an unsupported report shape", backend);
            },
        }

        println!();
        Ok(())
    }

    fn get_graph_view(&self) -> Result<RuntimeGraphView> {
        let report = self
            .state
            .backend_report()
            .ok_or_else(|| anyhow::anyhow!("No term loaded. Use 'term: <expr>' first."))?;
        runtime_graph_view(report)
    }

    fn cmd_equations(&self) -> Result<()> {
        let graph = self.get_graph_view()?;

        println!();
        println!("{}", "Equivalence Classes:".bold());
        if graph.equivalences.is_empty() {
            println!("  {}", "No equivalence classes in the current graph-shaped report.".dimmed());
        }
        for equ_class in &graph.equivalences {
            let terms = equ_class
                .term_ids
                .iter()
                .filter_map(|id| graph.term_by_id(*id).map(|term| term.display.as_str()))
                .collect::<Vec<_>>();
            println!("  {}", terms.join(" == "));
        }
        println!();
        Ok(())
    }

    fn cmd_rewrites_all(&self) -> Result<()> {
        let graph = self.get_graph_view()?;

        println!();
        println!("{}", graph.kind.edge_relation_name().bold());
        for edge in &graph.edges {
            let from_info = graph
                .term_by_id(edge.from_id)
                .ok_or_else(|| anyhow::anyhow!("Source term not found"))?;
            let to_info = graph
                .term_by_id(edge.to_id)
                .ok_or_else(|| anyhow::anyhow!("Target term not found"))?;
            if let Some(label) = &edge.label {
                println!("  {} → {} ({})", from_info.display, to_info.display, label);
            } else {
                println!("  {} → {}", from_info.display, to_info.display);
            }
        }
        println!();
        Ok(())
    }

    fn cmd_rewrites(&self) -> Result<()> {
        let graph = self.get_graph_view()?;

        let current_id = self
            .state
            .current_graph_id()
            .ok_or_else(|| anyhow::anyhow!("No current term"))?;

        let available_edges: Vec<_> = graph
            .edges
            .iter()
            .filter(|edge| edge.from_id == current_id)
            .collect();

        println!();
        if available_edges.is_empty() {
            println!("{} No {} available from current term.", "✓".green(), graph.kind.edge_label());
        } else {
            println!("{} available from current term:", graph.kind.edge_relation_name().bold());
            println!();
            for (idx, edge) in available_edges.iter().enumerate() {
                let target_info = graph
                    .term_by_id(edge.to_id)
                    .ok_or_else(|| anyhow::anyhow!("Target term not found"))?;
                let target_display = target_info.display.as_str();

                let formatted = format_term_pretty(target_display);

                println!("  {}) {}", idx.to_string().cyan(), "→".yellow());
                if let Some(label) = &edge.label {
                    println!("     {}", label.dimmed());
                }
                // Indent each line of the formatted output
                for line in formatted.lines() {
                    println!("     {}", line.green());
                }
                println!();
            }
        }
        println!();
        Ok(())
    }

    fn cmd_normal_forms(&self) -> Result<()> {
        let graph = self.get_graph_view()?;

        let normal_forms = graph.normal_forms();

        println!();
        if normal_forms.is_empty() {
            println!("{} No normal forms computed.", "Warning:".yellow());
        } else {
            println!("{} ({} total):", "Normal forms".bold(), normal_forms.len());
            println!();
            for (idx, nf) in normal_forms.iter().enumerate() {
                let formatted = format_term_pretty(&nf.display);
                println!("  {})", idx.to_string().cyan());
                for line in formatted.lines() {
                    println!("    {}", line.green());
                }
                println!();
            }
        }
        println!();
        Ok(())
    }

    fn cmd_relations(&self) -> Result<()> {
        let graph = self.get_graph_view()?;

        println!();
        println!("{}", "Computed Relations:".bold());
        println!();

        // Built-in relations
        println!("{}", "  Built-in:".yellow());
        println!("    {} ({} tuples)", "terms".cyan(), graph.terms.len());
        println!("    {} ({} tuples)", graph.kind.edge_relation_name().cyan(), graph.edges.len());
        println!(
            "    {} ({} root terms)",
            "roots".cyan(),
            graph.terms.iter().filter(|term| term.is_root).count()
        );
        println!("    {} ({} classes)", "equivalences".cyan(), graph.equivalences.len());

        // Custom relations
        if !graph.custom_relations.is_empty() {
            println!();
            println!("{}", "  Custom:".yellow());
            for (name, data) in &graph.custom_relations {
                let signature = format!("{}({})", name, data.param_types.join(", "));
                println!("    {} ({} tuples)", signature.cyan(), data.tuples.len());
            }
        }

        println!();
        println!("Use {} to view tuples in a specific relation.", "'relation <name>'".green());
        println!();
        Ok(())
    }

    fn cmd_relation(&self, args: &[&str]) -> Result<()> {
        if args.is_empty() {
            anyhow::bail!("Usage: relation <name>\nUse 'relations' to list available relations.");
        }

        let name = args[0];
        let graph = self.get_graph_view()?;

        // Check built-in relations first
        match name {
            "terms" => {
                println!();
                println!("{} ({} tuples):", "terms(Term)".bold(), graph.terms.len());
                for term_info in &graph.terms {
                    let mut markers = Vec::new();
                    if term_info.is_root {
                        markers.push("root");
                    }
                    if term_info.is_normal_form {
                        markers.push("NF");
                    }
                    let marker = if markers.is_empty() {
                        String::new()
                    } else {
                        format!(" [{}]", markers.join(", "))
                    };
                    println!("  {}{}", term_info.display.green(), marker.dimmed());
                }
                println!();
                return Ok(());
            },
            "rewrites" | "derivations" | "derivation_edges" => {
                println!();
                println!(
                    "{} ({} tuples):",
                    graph.kind.edge_relation_name().bold(),
                    graph.edges.len()
                );
                for edge in &graph.edges {
                    let from = graph.term_by_id(edge.from_id);
                    let to = graph.term_by_id(edge.to_id);
                    if let (Some(from), Some(to)) = (from, to) {
                        let label = edge
                            .label
                            .as_ref()
                            .map(|label| format!(" ({label})"))
                            .unwrap_or_default();
                        println!(
                            "  {} {} {}{}",
                            from.display.green(),
                            "→".yellow(),
                            to.display.green(),
                            label.dimmed()
                        );
                    }
                }
                println!();
                return Ok(());
            },
            "roots" => {
                println!();
                let roots = graph
                    .terms
                    .iter()
                    .filter(|term| term.is_root)
                    .collect::<Vec<_>>();
                println!("{} ({} tuples):", "roots(Term)".bold(), roots.len());
                for root in roots {
                    println!("  {}", root.display.green());
                }
                println!();
                return Ok(());
            },
            "equivalences" => {
                println!();
                println!("{} ({} classes):", "equivalences".bold(), graph.equivalences.len());
                for equiv in &graph.equivalences {
                    let terms: Vec<_> = equiv
                        .term_ids
                        .iter()
                        .filter_map(|id| graph.term_by_id(*id).map(|term| term.display.as_str()))
                        .collect();
                    println!("  {}", terms.join(" == ").green());
                }
                println!();
                return Ok(());
            },
            _ => {},
        }

        // Check custom relations
        if let Some(data) = graph.custom_relations.get(name) {
            println!();
            let signature = format!("{}({})", name, data.param_types.join(", "));
            println!("{} ({} tuples):", signature.bold(), data.tuples.len());
            for tuple in &data.tuples {
                println!("  ({})", tuple.join(", ").green());
            }
            println!();
            Ok(())
        } else {
            Err(anyhow::anyhow!(
                "Unknown relation: '{}'. Use 'relations' to list available relations.",
                name
            ))
        }
    }

    fn cmd_apply(&mut self, args: &[&str]) -> Result<()> {
        if args.is_empty() {
            anyhow::bail!("Usage: apply <rewrite-number>");
        }

        let idx: usize = args[0]
            .parse()
            .map_err(|_| anyhow::anyhow!("Invalid number: {}", args[0]))?;

        let language_name = self
            .state
            .language_name()
            .ok_or_else(|| anyhow::anyhow!("No language loaded"))?;

        let language = self.registry.get(language_name)?;

        let current_id = self
            .state
            .current_graph_id()
            .ok_or_else(|| anyhow::anyhow!("No current term"))?;

        let (target_id, target_display, edge_label) = {
            let graph = self.get_graph_view()?;

            let available_edges: Vec<_> = graph
                .edges
                .iter()
                .filter(|edge| edge.from_id == current_id)
                .collect();

            if idx >= available_edges.len() {
                anyhow::bail!(
                    "{} {} not found. Use 'rewrites' to see available graph edges.",
                    graph.kind.edge_label(),
                    idx
                );
            }

            let edge = available_edges[idx];

            let target_info = graph
                .term_by_id(edge.to_id)
                .ok_or_else(|| anyhow::anyhow!("Target term not found"))?;
            (edge.to_id, target_info.display.clone(), edge.label.clone())
        };

        let target_term = term_from_display_or_fallback(language, &target_display, target_id);

        println!();
        if let Some(label) = edge_label {
            println!("{} {}", "Applied graph edge →".yellow(), label.dimmed());
        } else {
            println!("{}", "Applied graph edge →".yellow());
        }
        let formatted = format_term_pretty(&target_display);
        for line in formatted.lines() {
            println!("  {}", line.green());
        }
        println!();

        // Update state while preserving the checked report that owns the graph.
        self.state
            .set_term_preserving_report(target_term, target_id)?;

        Ok(())
    }

    fn cmd_goto(&mut self, args: &[&str]) -> Result<()> {
        if args.is_empty() {
            anyhow::bail!("Usage: goto <normal-form-number>");
        }

        let idx: usize = args[0]
            .parse()
            .map_err(|_| anyhow::anyhow!("Invalid number: {}", args[0]))?;

        let language_name = self
            .state
            .language_name()
            .ok_or_else(|| anyhow::anyhow!("No language loaded"))?;

        let language = self.registry.get(language_name)?;

        let (target_id, target_display) = {
            let graph = self.get_graph_view()?;
            let normal_forms = graph.normal_forms();

            let target_info = normal_forms.get(idx).ok_or_else(|| {
                anyhow::anyhow!(
                    "Normal form {} not found. Use 'normal-forms' to see available normal forms.",
                    idx
                )
            })?;
            (target_info.id, target_info.display.clone())
        };

        let target_term = term_from_display_or_fallback(language, &target_display, target_id);

        println!();
        println!("{}", "Navigated to normal form:".bold());
        let formatted = format_term_pretty(&target_display);
        for line in formatted.lines() {
            println!("  {}", line.green());
        }
        println!();

        // Update state with the correct graph ID while preserving the report.
        self.state
            .set_term_preserving_report(target_term, target_id)?;

        Ok(())
    }

    /// Run a single Datalog-style rule over the current runtime backend report.
    /// Requires a loaded language, a prior exec/step, and a current term for env substitution.
    /// Environment substitution includes REPL bindings plus "current_term" (display of the current stepped term).
    fn cmd_query(&mut self, line: &str) -> Result<()> {
        let language_name = self
            .state
            .language_name()
            .ok_or_else(|| anyhow::anyhow!("No language loaded. Use 'lang <name>' first."))?;

        let current_term = self
            .state
            .current_term()
            .ok_or_else(|| anyhow::anyhow!("No current term. Use 'step <term>' first."))?
            .clone_box();

        let language = self.registry.get(language_name)?;

        self.state.ensure_environment(|| language.create_env());

        // Substitute env bindings (save t, etc.). We do *not* add "current_term" to env here.
        let mut substituted = pre_substitute_env(line, language, self.state.environment().unwrap());

        // Substitute "current_term" with a Rust string literal so the query parser sees one argument.
        // The term's display can contain { } | . etc. which are valid Rust tokens; only a string literal is safe.
        let current_display = format!("{}", current_term);
        let current_literal = format!(
            "\"{}\"",
            current_display
                .replace('\\', "\\\\")
                .replace('"', "\\\"")
                .replace('\n', "\\n")
                .replace('\r', "\\r")
                .replace('\t', "\\t")
        );
        substituted = replace_whole_word(&substituted, "current_term", &current_literal);

        let report = self.state.backend_report().ok_or_else(|| {
            anyhow::anyhow!("No runtime report. Use 'exec <term>' or 'step <term>' first.")
        })?;

        match query_run_query_report(&substituted, report) {
            Ok(rows) => {
                println!();
                if rows.is_empty() {
                    println!("{} (0 rows)", "Query result:".bold());
                } else {
                    println!("{} ({} row(s)):", "Query result:".bold(), rows.len());
                    for row in &rows {
                        let formatted = if row.len() == 1 {
                            row[0].clone()
                        } else {
                            format!("({})", row.join(", "))
                        };
                        println!("  {}", formatted.green());
                    }
                }
                println!();
                Ok(())
            },
            Err(e) => {
                eprintln!("{}", "Query (after substitution):".yellow().bold());
                eprintln!("{}", substituted.dimmed());
                Err(anyhow::anyhow!("{}", e))
            },
        }
    }

    fn cmd_example(&mut self, args: &[&str]) -> Result<()> {
        if args.is_empty() {
            anyhow::bail!("Usage: example <name>\nUse 'list-examples' to see available examples.");
        }

        let example_name = args[0];

        let example = Example::by_name(example_name).ok_or_else(|| {
            anyhow::anyhow!(
                "Example '{}' not found. Use 'list-examples' to see available examples.",
                example_name
            )
        })?;

        println!();
        println!("{} {}", "Example:".bold(), example.name.cyan());
        println!("{} {}", "Description:".bold(), example.description);
        println!();

        // Parse and load the example
        self.cmd_exec_term(example.source)?;

        Ok(())
    }

    fn cmd_list_examples(&self, language_name: &str) -> Result<()> {
        println!();
        println!("{}", "Available Examples:".bold());
        println!();

        // Group by category
        for &category in &[
            ExampleCategory::Simple,
            ExampleCategory::Branching,
            ExampleCategory::Complex,
            ExampleCategory::Parallel,
            ExampleCategory::Advanced,
            ExampleCategory::Performance,
            ExampleCategory::EdgeCase,
            ExampleCategory::MultiComm,
            ExampleCategory::Mobility,
            ExampleCategory::Security,
        ] {
            let examples = Example::by_language_name_and_category(language_name, category);
            if !examples.is_empty() {
                println!("{}", format!("  {:?}:", category).yellow());
                for ex in examples {
                    println!("    {} - {}", ex.name.cyan(), ex.description.dimmed());
                }
                println!();
            }
        }

        println!("Use {} to load an example.", "example <name>".green());
        println!();

        Ok(())
    }
}
