//! `ProgramTestSuite` builder for application-level testing.
//!
//! Tests programs written in MeTTaIL-defined languages by leveraging
//! the language's semantics (parser, selected runtime backend, type system,
//! etc.) to auto-generate structural, semantic, and behavioral tests.

use crate::runtime_report;
use mettail_runtime::{
    AscentResults, Language, RuntimeBackend, RuntimeBackendOutput, RuntimeBackendReport,
    RuntimeDovetailRunReport,
};

/// Builder for auto-generating tests for a program written in a MeTTaIL language.
///
/// # Example
///
/// ```ignore
/// use mettail_testkit::program::ProgramTestSuite;
/// use mettail_languages::rhocalc::RhoCalcLanguage;
///
/// let suite = ProgramTestSuite::new(&RhoCalcLanguage)
///     .source("for(x <- chan){chan!(*x)}")
///     .expect_parses()
///     .expect_terminates(1000);
/// suite.run().expect("echo program tests");
/// ```
pub struct ProgramTestSuite<'a> {
    language: &'a dyn Language,
    source: Option<String>,
    checks: Vec<ProgramCheck>,
}

enum ProgramCheck {
    Parses,
    Roundtrip,
    Terminates { max_steps: usize },
    NormalizesTo { expected: String },
    RewritesInputTo { input: String, expected: String },
    NoDeadlock,
    Ltl { formula: String },
}

struct RuntimeExecutionNode {
    label: String,
    is_accepting: bool,
}

struct RuntimeExecutionModel {
    nodes: Vec<RuntimeExecutionNode>,
    transitions: Vec<(usize, usize, String)>,
    initial_nodes: Vec<usize>,
}

impl RuntimeExecutionModel {
    fn from_report(report: RuntimeBackendReport, context: &str) -> Result<Self, String> {
        let backend = report.backend();
        match report.into_output() {
            RuntimeBackendOutput::Ascent(results) => Ok(Self::from_ascent_results(results)),
            RuntimeBackendOutput::Dovetail(report) => Self::from_dovetail_report(report, context),
            RuntimeBackendOutput::Observations(_) => Err(format!(
                "{} requires rewrite-graph evidence; {} returned runtime observations",
                context, backend
            )),
            other => Err(format!(
                "{} requires rewrite-graph evidence; {} returned {}",
                context,
                backend,
                other.kind_name()
            )),
        }
    }

    fn from_ascent_results(results: AscentResults) -> Self {
        let normal_forms = results.normal_forms();
        let nodes = results
            .all_terms
            .iter()
            .map(|term| RuntimeExecutionNode {
                label: term.display.clone(),
                is_accepting: normal_forms
                    .iter()
                    .any(|normal_form| normal_form.display == term.display),
            })
            .collect::<Vec<_>>();
        let transitions = results
            .all_terms
            .windows(2)
            .enumerate()
            .map(|(index, terms)| (index, index + 1, terms[0].display.clone()))
            .collect();
        let initial_nodes = if nodes.is_empty() {
            Vec::new()
        } else {
            vec![0]
        };
        Self { nodes, transitions, initial_nodes }
    }

    fn from_dovetail_report(
        report: RuntimeDovetailRunReport,
        context: &str,
    ) -> Result<Self, String> {
        report
            .validate_shape()
            .map_err(|err| format!("{} received malformed Dovetail report: {}", context, err))?;
        report.assert_complete().map_err(|status| {
            format!("{} requires a complete Dovetail report, but received {}", context, status)
        })?;

        let nodes = report
            .terms
            .iter()
            .map(|term| RuntimeExecutionNode {
                label: term.op_display.clone(),
                is_accepting: term.is_root,
            })
            .collect::<Vec<_>>();
        let key_to_ordinal = report
            .terms
            .iter()
            .map(|term| (term.key.as_slice(), term.ordinal))
            .collect::<std::collections::HashMap<_, _>>();
        let mut has_incoming = vec![false; report.terms.len()];
        let mut transitions = Vec::with_capacity(report.derivation_edges.len());

        for edge in &report.derivation_edges {
            let parent = *key_to_ordinal
                .get(edge.parent_key.as_slice())
                .ok_or_else(|| {
                    format!(
                        "{} received Dovetail edge {} with missing parent",
                        context, edge.ordinal
                    )
                })?;
            let child = *key_to_ordinal
                .get(edge.child_key.as_slice())
                .ok_or_else(|| {
                    format!(
                        "{} received Dovetail edge {} with missing child",
                        context, edge.ordinal
                    )
                })?;
            has_incoming[parent] = true;
            transitions.push((child, parent, report.terms[child].op_display.clone()));
        }

        let mut initial_nodes = has_incoming
            .iter()
            .enumerate()
            .filter_map(|(ordinal, incoming)| (!incoming).then_some(ordinal))
            .collect::<Vec<_>>();
        if initial_nodes.is_empty() && !nodes.is_empty() {
            initial_nodes.extend(report.root_ordinals.iter().copied());
        }

        Ok(Self { nodes, transitions, initial_nodes })
    }
}

impl<'a> ProgramTestSuite<'a> {
    /// Create a new test suite for a program in the given language.
    pub fn new(language: &'a dyn Language) -> Self {
        Self {
            language,
            source: None,
            checks: Vec::new(),
        }
    }

    /// Set the program source text.
    pub fn source(mut self, src: &str) -> Self {
        self.source = Some(src.to_string());
        self
    }

    /// Assert the program parses successfully.
    pub fn expect_parses(mut self) -> Self {
        self.checks.push(ProgramCheck::Parses);
        self
    }

    /// Assert parse(display(parse(source))) == parse(source).
    pub fn expect_roundtrip(mut self) -> Self {
        self.checks.push(ProgramCheck::Roundtrip);
        self
    }

    /// Assert the program terminates within the given step bound.
    pub fn expect_terminates(mut self, max_steps: usize) -> Self {
        self.checks.push(ProgramCheck::Terminates { max_steps });
        self
    }

    /// Assert the program normalizes to the expected string.
    pub fn expect_normalizes_to(mut self, expected: &str) -> Self {
        self.checks
            .push(ProgramCheck::NormalizesTo { expected: expected.to_string() });
        self
    }

    /// Assert that providing `input` to the program rewrites to `expected`.
    pub fn expect_rewrite(mut self, input: &str, expected: &str) -> Self {
        self.checks.push(ProgramCheck::RewritesInputTo {
            input: input.to_string(),
            expected: expected.to_string(),
        });
        self
    }

    /// Assert no deadlock via Petri net analysis.
    ///
    /// Constructs a Petri net model from the program's visible channel patterns
    /// (send/receive on named channels) and checks whether any reachable marking
    /// is a deadlock (no enabled transitions). If the program source does not
    /// contain recognizable channel patterns, the check passes vacuously with
    /// a diagnostic note.
    pub fn expect_no_deadlock(mut self) -> Self {
        self.checks.push(ProgramCheck::NoDeadlock);
        self
    }

    /// Assert an LTL temporal property.
    ///
    /// Parses the formula string as an LTL formula, compiles it to a Buchi
    /// automaton via the negation-intersection-emptiness pipeline, and checks
    /// it against a system model derived from the program's rewrite execution.
    pub fn expect_ltl(mut self, formula: &str) -> Self {
        self.checks
            .push(ProgramCheck::Ltl { formula: formula.to_string() });
        self
    }

    /// Run all configured tests. Returns Ok on all pass, Err with details on failure.
    pub fn run(self) -> Result<(), String> {
        let source = self
            .source
            .as_deref()
            .ok_or_else(|| "ProgramTestSuite: no source set".to_string())?;

        let mut failures = Vec::new();

        for check in &self.checks {
            if let Err(e) = self.run_check(source, check) {
                failures.push(e);
            }
        }

        if failures.is_empty() {
            Ok(())
        } else {
            Err(format!("{} check(s) failed:\n{}", failures.len(), failures.join("\n---\n")))
        }
    }

    fn run_check(&self, source: &str, check: &ProgramCheck) -> Result<(), String> {
        match check {
            ProgramCheck::Parses => {
                mettail_runtime::clear_var_cache();
                self.language
                    .parse_term(source)
                    .map_err(|e| format!("Parse failed: {}", e))?;
                Ok(())
            },
            ProgramCheck::Roundtrip => {
                mettail_runtime::clear_var_cache();
                let term = self
                    .language
                    .parse_term(source)
                    .map_err(|e| format!("Parse failed for roundtrip: {}", e))?;
                let displayed = format!("{}", term);

                mettail_runtime::clear_var_cache();
                let reparsed = self
                    .language
                    .parse_term(&displayed)
                    .map_err(|e| format!("Re-parse failed: {}", e))?;

                if !term.term_eq(reparsed.as_ref()) {
                    return Err(format!(
                        "Roundtrip failed:\n  original:  {:?}\n  displayed: '{}'\n  reparsed:  {:?}",
                        term, displayed, reparsed
                    ));
                }
                Ok(())
            },
            ProgramCheck::Terminates { max_steps } => {
                mettail_runtime::clear_var_cache();
                let term = self
                    .language
                    .parse_term(source)
                    .map_err(|e| format!("Parse failed: {}", e))?;

                let report = runtime_report::run_default_backend_report(
                    self.language,
                    term.as_ref(),
                    "program termination check",
                )?;

                let backend = report.backend();
                match report.into_output() {
                    mettail_runtime::RuntimeBackendOutput::Ascent(results) => {
                        let normal_forms = results.normal_forms();
                        if normal_forms.is_empty() && results.all_terms.len() > *max_steps {
                            return Err(format!(
                                "Program did not terminate within {} steps ({} terms explored)",
                                max_steps,
                                results.all_terms.len()
                            ));
                        }
                    },
                    mettail_runtime::RuntimeBackendOutput::Dovetail(dovetail_report) => {
                        if !dovetail_report.is_complete() {
                            return Err(format!(
                                "Program termination check requires a complete Dovetail report; {} returned {}",
                                backend,
                                dovetail_report.completeness
                            ));
                        }
                    },
                    mettail_runtime::RuntimeBackendOutput::Observations(_) => {
                        // Observation-shaped backend reports are terminal runtime
                        // outcomes; they are not rewrite graphs, but they do prove
                        // the selected runtime backend returned within this check.
                    },
                    other => {
                        return Err(format!(
                            "Program termination check does not support {} output from {}",
                            other.kind_name(),
                            backend
                        ));
                    },
                }
                Ok(())
            },
            ProgramCheck::NormalizesTo { expected } => {
                crate::properties::algebraic::assert_rewrites_to(self.language, source, expected)
            },
            ProgramCheck::RewritesInputTo { input, expected } => {
                crate::properties::algebraic::assert_rewrites_to(self.language, input, expected)
            },
            ProgramCheck::NoDeadlock => self.check_no_deadlock(source),
            ProgramCheck::Ltl { formula } => self.check_ltl_property(source, formula),
        }
    }

    /// Check for deadlocks by constructing a Petri net from visible channel patterns.
    ///
    /// Scans the source for channel-like identifiers (patterns matching send/receive
    /// syntax) and builds a Petri net where:
    /// - Each channel becomes a place
    /// - Each send becomes a transition producing a token in the channel's place
    /// - Each receive becomes a transition consuming a token from the channel's place
    ///
    /// Then checks whether any reachable marking is a deadlock.
    fn check_no_deadlock(&self, source: &str) -> Result<(), String> {
        use mettail_prattail::petri;

        // Extract channel names from the source text.
        // We look for patterns common across MeTTaIL languages:
        //   - Rholang-style: `chan!(...)` (send), `for(x <- chan){...}` (receive)
        //   - Generic: identifiers that appear in both send and receive positions
        let channels = extract_channel_names(source);

        if channels.is_empty() {
            // No recognizable channel patterns. The deadlock check passes
            // vacuously: with no concurrent structure, there is no deadlock.
            return Ok(());
        }

        // Build places: one per channel, with 0 initial tokens.
        let places: Vec<(String, u64)> = channels.iter().map(|ch| (ch.clone(), 0u64)).collect();

        // Build transitions from detected send/receive patterns.
        let mut transitions: Vec<(String, Vec<(usize, u64)>, Vec<(usize, u64)>)> = Vec::new();

        for (i, ch) in channels.iter().enumerate() {
            // Check if this channel has sends.
            let send_pattern = format!("{}!", ch);
            if source.contains(&send_pattern) {
                // Send transition: produces a token in the channel's place.
                transitions.push((
                    format!("send_{}", ch),
                    vec![],       // no inputs consumed
                    vec![(i, 1)], // produces 1 token in channel place
                ));
            }

            // Check if this channel has receives.
            let recv_pattern_rho = format!("<- {}", ch); // Rholang: `for(x <- ch)`
            let recv_pattern_generic = format!("{}?", ch); // Generic: `ch?(x)`
            if source.contains(&recv_pattern_rho) || source.contains(&recv_pattern_generic) {
                // Receive transition: consumes a token from the channel's place.
                transitions.push((
                    format!("recv_{}", ch),
                    vec![(i, 1)], // consumes 1 token from channel place
                    vec![],       // no outputs produced
                ));
            }
        }

        if transitions.is_empty() {
            // No send/receive transitions found. Pass vacuously.
            return Ok(());
        }

        let net = petri::construct_petri_net(&places, &transitions);

        // Check for deadlock: if check_deadlock returns true, a deadlock
        // is reachable.
        let has_deadlock = petri::check_deadlock(&net);

        if has_deadlock {
            // Provide a diagnostic message listing the channels involved.
            Err(format!(
                "Deadlock detected: Petri net analysis found a reachable deadlock \
                 state. Channels involved: [{}]. This means there exists a reachable \
                 configuration where no send or receive can proceed.",
                channels.join(", ")
            ))
        } else {
            Ok(())
        }
    }

    /// Check an LTL temporal property against the program's execution model.
    ///
    /// Parses the LTL formula, derives a system Buchi automaton from the
    /// language's rewrite execution, and runs the standard automata-theoretic
    /// model checking pipeline: negate, compile to Buchi, intersect, check
    /// emptiness.
    fn check_ltl_property(&self, source: &str, formula_str: &str) -> Result<(), String> {
        use mettail_prattail::buchi::BuchiAutomaton;
        use mettail_prattail::ltl::{self, LtlProperty};

        // Step 1: Parse the LTL formula.
        let formula = ltl::parse_ltl(formula_str)
            .map_err(|e| format!("Failed to parse LTL formula '{}': {}", formula_str, e))?;

        // Step 2: Build a system Buchi automaton from the program's execution.
        // We construct a simple model:
        // - Parse the source to get the initial term.
        // - Prefer a Dovetail report when the language exposes one; otherwise
        //   run the selected runtime backend.
        // - Each term in the trace becomes a state.
        // - Transitions connect consecutive terms.
        // - Ascent normal forms or Dovetail roots are accepting states.
        mettail_runtime::clear_var_cache();
        let term = self
            .language
            .parse_term(source)
            .map_err(|e| format!("Parse failed for LTL check: {}", e))?;

        let context = "LTL execution-model check";
        let report = if self
            .language
            .supports_runtime_backend(RuntimeBackend::Dovetail)
        {
            self.language
                .run_backend_report(RuntimeBackend::Dovetail, term.as_ref())
                .map_err(|error| format!("{} failed on Dovetail backend: {}", context, error))?
        } else {
            runtime_report::run_default_backend_report(self.language, term.as_ref(), context)?
        };
        let model = RuntimeExecutionModel::from_report(report, context)?;

        let mut system = BuchiAutomaton::new();

        if model.nodes.is_empty() {
            // Empty execution: the system has no states.
            // The LTL property holds vacuously.
            return Ok(());
        }

        // Add a state for each term in the execution. Normal forms are accepting.
        let mut term_to_state = std::collections::HashMap::new();
        for (i, node) in model.nodes.iter().enumerate() {
            let state_id = system.add_state(node.is_accepting);
            term_to_state.insert(i, state_id);
        }

        // Add transitions from the runtime report's execution model.
        // Also add self-loops on normal forms (infinite acceptance).
        for (from, to, label) in model.transitions {
            if let (Some(&src), Some(&tgt)) = (term_to_state.get(&from), term_to_state.get(&to)) {
                system.add_transition(src, Some(label), tgt);
            }
        }

        // Self-loop on accepting terms (for Buchi acceptance of infinite words).
        for (i, node) in model.nodes.iter().enumerate() {
            if node.is_accepting {
                if let Some(&state_id) = term_to_state.get(&i) {
                    system.add_transition(state_id, Some(node.label.clone()), state_id);
                }
            }
        }

        // Set initial states. Ascent uses the first term; Dovetail uses leaves.
        for initial_node in model.initial_nodes {
            if let Some(&initial) = term_to_state.get(&initial_node) {
                system.initial_states.insert(initial);
            }
        }

        // Step 3: Check the LTL property.
        let property = LtlProperty::new(formula_str, formula);
        let check_result = ltl::check_ltl_property(&system, &property);

        match check_result {
            ltl::LtlCheckResult::Satisfied => Ok(()),
            ltl::LtlCheckResult::Violated { prefix, lasso } => {
                let mut msg = format!("LTL property '{}' violated.", formula_str);
                if !prefix.is_empty() {
                    msg.push_str(&format!("\n  Prefix: {}", prefix.join(" -> ")));
                }
                if !lasso.is_empty() {
                    msg.push_str(&format!("\n  Lasso: {}", lasso.join(" -> ")));
                }
                Err(msg)
            },
            ltl::LtlCheckResult::Inconclusive { reason } => {
                Err(format!("LTL property '{}' check was inconclusive: {}", formula_str, reason))
            },
        }
    }
}

/// Extract channel-like names from source text.
///
/// Looks for identifiers that appear in send (`name!`) or receive (`<- name`,
/// `name?`) patterns. Returns deduplicated list of channel names.
fn extract_channel_names(source: &str) -> Vec<String> {
    let mut channels = std::collections::HashSet::new();

    // Pattern 1: Rholang-style sends: `identifier!(...)`
    // Pattern 2: Rholang-style receives: `for(... <- identifier){...}`
    // Pattern 3: Generic: `identifier?(...)` or `identifier!(...)`

    let chars: Vec<char> = source.chars().collect();
    let len = chars.len();
    let mut i = 0;

    while i < len {
        // Look for identifier followed by '!' or '?'
        if chars[i].is_alphabetic() || chars[i] == '_' {
            let start = i;
            while i < len && (chars[i].is_alphanumeric() || chars[i] == '_') {
                i += 1;
            }
            let ident: String = chars[start..i].iter().collect();

            // Check for send/receive suffix
            if i < len && (chars[i] == '!' || chars[i] == '?') {
                // Skip keywords that happen to end with ! or ?
                if ident != "for"
                    && ident != "if"
                    && ident != "match"
                    && ident != "new"
                    && ident != "contract"
                {
                    channels.insert(ident);
                }
            }
            continue;
        }

        // Look for "<- identifier" pattern (Rholang receive)
        if i + 2 < len && chars[i] == '<' && chars[i + 1] == '-' {
            i += 2;
            // Skip whitespace
            while i < len && chars[i].is_whitespace() {
                i += 1;
            }
            if i < len && (chars[i].is_alphabetic() || chars[i] == '_') {
                let start = i;
                while i < len && (chars[i].is_alphanumeric() || chars[i] == '_') {
                    i += 1;
                }
                let ident: String = chars[start..i].iter().collect();
                channels.insert(ident);
            }
            continue;
        }

        i += 1;
    }

    let mut result: Vec<String> = channels.into_iter().collect();
    result.sort(); // Deterministic order
    result
}

#[cfg(test)]
mod tests {
    use std::any::Any;

    use mettail_runtime::{
        AscentResults, BackendCapabilityDef, LanguageMetadata, RuntimeBackend,
        RuntimeBackendReport, RuntimeDovetailCompleteness, RuntimeDovetailRunReport,
        RuntimeDovetailTermRecord, Term, TermType, VarTypeInfo,
    };

    use super::*;

    #[derive(Clone, Debug)]
    struct ProgramTerm(String);

    impl std::fmt::Display for ProgramTerm {
        fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            write!(formatter, "{}", self.0)
        }
    }

    impl Term for ProgramTerm {
        fn clone_box(&self) -> Box<dyn Term> {
            Box::new(self.clone())
        }

        fn term_id(&self) -> u64 {
            11
        }

        fn term_eq(&self, other: &dyn Term) -> bool {
            other
                .as_any()
                .downcast_ref::<ProgramTerm>()
                .is_some_and(|other| self.0 == other.0)
        }

        fn as_any(&self) -> &dyn Any {
            self
        }
    }

    struct DovetailProgramMetadata;

    static DOVETAIL_BACKENDS: &[BackendCapabilityDef] = &[BackendCapabilityDef {
        backend: RuntimeBackend::Dovetail,
        is_default: true,
    }];

    impl LanguageMetadata for DovetailProgramMetadata {
        fn name(&self) -> &'static str {
            "DovetailProgram"
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

    static DOVETAIL_METADATA: DovetailProgramMetadata = DovetailProgramMetadata;

    struct DovetailProgramLanguage {
        completeness: RuntimeDovetailCompleteness,
    }

    impl DovetailProgramLanguage {
        fn new(completeness: RuntimeDovetailCompleteness) -> Self {
            Self { completeness }
        }

        fn report(&self) -> RuntimeDovetailRunReport {
            RuntimeDovetailRunReport {
                roots: vec![b"done".to_vec()],
                root_ordinals: vec![0],
                terms: vec![RuntimeDovetailTermRecord {
                    ordinal: 0,
                    class_id: 0,
                    key: b"done".to_vec(),
                    op_display: "done".to_string(),
                    weight_display: "0".to_string(),
                    is_root: true,
                    source_display: None,
                }],
                derivation_edges: Vec::new(),
                rule_firings: Vec::new(),
                completeness: self.completeness,
            }
        }
    }

    impl Language for DovetailProgramLanguage {
        fn name(&self) -> &'static str {
            "DovetailProgram"
        }

        fn metadata(&self) -> &'static dyn LanguageMetadata {
            &DOVETAIL_METADATA
        }

        fn parse_term(&self, input: &str) -> Result<Box<dyn Term>, String> {
            Ok(Box::new(ProgramTerm(input.to_string())))
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
                    RuntimeBackendReport::try_dovetail(self.report()).map_err(|err| err.to_string())
                },
                RuntimeBackend::Ascent => self.run_ascent(term).map(RuntimeBackendReport::ascent),
                other => Err(format!("{} backend is not installed", other)),
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
    fn termination_check_accepts_complete_dovetail_report() {
        let language = DovetailProgramLanguage::new(RuntimeDovetailCompleteness::Complete);
        ProgramTestSuite::new(&language)
            .source("done")
            .expect_terminates(0)
            .run()
            .expect("complete Dovetail report is terminal runtime evidence");
    }

    #[test]
    fn termination_check_rejects_bounded_dovetail_report() {
        let language = DovetailProgramLanguage::new(RuntimeDovetailCompleteness::BoundedByCycleCut);
        let err = ProgramTestSuite::new(&language)
            .source("cycle")
            .expect_terminates(0)
            .run()
            .expect_err("bounded Dovetail report must not prove termination");
        assert!(
            err.contains("requires a complete Dovetail report")
                && err.contains("BoundedByCycleCut"),
            "{err}"
        );
    }

    #[test]
    fn ltl_check_accepts_complete_dovetail_report() {
        let language = DovetailProgramLanguage::new(RuntimeDovetailCompleteness::Complete);
        ProgramTestSuite::new(&language)
            .source("done")
            .expect_ltl("F done")
            .run()
            .expect("LTL model should use complete Dovetail report evidence");
    }

    #[test]
    fn ltl_check_rejects_bounded_dovetail_report() {
        let language = DovetailProgramLanguage::new(RuntimeDovetailCompleteness::BoundedByCycleCut);
        let err = ProgramTestSuite::new(&language)
            .source("cycle")
            .expect_ltl("F done")
            .run()
            .expect_err("bounded Dovetail report must not prove LTL properties");
        assert!(
            err.contains("requires a complete Dovetail report")
                && err.contains("BoundedByCycleCut"),
            "{err}"
        );
    }
}
