use anyhow::Result;
use mettail_runtime::{AscentResults, RuntimeBackendReport, Term};
use std::any::Any;

/// The current state of the REPL session
pub struct ReplState {
    /// The name of the currently loaded language
    language_name: Option<String>,

    /// The current term being explored
    current_term: Option<Box<dyn Term>>,

    /// The ID of the current term in the rewrite graph (may differ from term.term_id())
    current_graph_id: Option<u64>,

    /// Navigation history
    history: Vec<HistoryEntry>,

    /// Current position in history
    history_idx: usize,

    /// Cached runtime backend report for the current term.
    backend_report: Option<RuntimeBackendReport>,

    /// Environment for variable bindings (theory-specific type)
    environment: Option<Box<dyn Any + Send + Sync>>,
}

/// An entry in the navigation history
#[derive(Debug, Clone)]
pub struct HistoryEntry {
    pub term_id: u64,
    pub display: String,
    pub rewrite_applied: Option<String>,
}

impl ReplState {
    /// Create a new empty state
    pub fn new() -> Self {
        Self {
            language_name: None,
            current_term: None,
            current_graph_id: None,
            history: Vec::new(),
            history_idx: 0,
            backend_report: None,
            environment: None,
        }
    }

    /// Load a language by name
    pub fn load_language(&mut self, name: &str) {
        self.language_name = Some(name.to_string());
        self.current_term = None;
        self.current_graph_id = None;
        self.history.clear();
        self.history_idx = 0;
        self.backend_report = None;
        self.environment = None;
    }

    /// Get the environment (immutable)
    pub fn environment(&self) -> Option<&(dyn Any + Send + Sync)> {
        self.environment.as_ref().map(|b| b.as_ref())
    }

    /// Get the environment (mutable)
    pub fn environment_mut(&mut self) -> Option<&mut (dyn Any + Send + Sync)> {
        self.environment.as_mut().map(|b| b.as_mut())
    }

    /// Set the environment
    pub fn set_environment(&mut self, env: Box<dyn Any + Send + Sync>) {
        self.environment = Some(env);
    }

    /// Ensure environment exists (create if needed)
    pub fn ensure_environment<F>(&mut self, create: F) -> &mut (dyn Any + Send + Sync)
    where
        F: FnOnce() -> Box<dyn Any + Send + Sync>,
    {
        if self.environment.is_none() {
            self.environment = Some(create());
        }
        self.environment.as_mut().unwrap().as_mut()
    }

    /// Get the name of the current language
    pub fn language_name(&self) -> Option<&str> {
        self.language_name.as_deref()
    }

    /// Set the current term from legacy/reference Ascent results.
    pub fn set_term(&mut self, term: Box<dyn Term>, results: AscentResults) -> Result<()> {
        let graph_id = term.term_id();
        self.set_term_with_id(term, results, graph_id)
    }

    /// Set the current term with an explicit graph ID from legacy/reference
    /// Ascent results.
    pub fn set_term_with_id(
        &mut self,
        term: Box<dyn Term>,
        results: AscentResults,
        graph_id: u64,
    ) -> Result<()> {
        self.set_term_with_report(term, RuntimeBackendReport::ascent(results), graph_id)
    }

    /// Set the current term with an explicit graph ID and runtime backend
    /// report. Non-Ascent reports keep the REPL state current, but
    /// graph-navigation/query commands require `ascent_results()`.
    pub fn set_term_with_report(
        &mut self,
        term: Box<dyn Term>,
        report: RuntimeBackendReport,
        graph_id: u64,
    ) -> Result<()> {
        // Update state
        self.current_term = Some(term.clone_box());
        self.current_graph_id = Some(graph_id);
        self.backend_report = Some(report);

        // Add to history
        let entry = HistoryEntry {
            term_id: graph_id,
            display: format!("{}", term),
            rewrite_applied: None,
        };
        self.history.push(entry);
        self.history_idx = self.history.len() - 1;

        Ok(())
    }

    /// Get the current term's ID in the rewrite graph
    pub fn current_graph_id(&self) -> Option<u64> {
        self.current_graph_id
    }

    /// Get the current term
    pub fn current_term(&self) -> Option<&dyn Term> {
        self.current_term.as_ref().map(|b| b.as_ref())
    }

    /// Get the Ascent results
    pub fn ascent_results(&self) -> Option<&AscentResults> {
        self.backend_report
            .as_ref()
            .and_then(RuntimeBackendReport::as_ascent_results)
    }

    /// Get the current runtime backend report.
    pub fn backend_report(&self) -> Option<&RuntimeBackendReport> {
        self.backend_report.as_ref()
    }

    /// Get the history
    pub fn history(&self) -> &[HistoryEntry] {
        &self.history
    }

    /// Get the current history index
    pub fn history_index(&self) -> usize {
        self.history_idx
    }

    /// Navigate back in history
    pub fn go_back(&mut self) -> Option<&HistoryEntry> {
        if self.history_idx > 0 {
            self.history_idx -= 1;
            Some(&self.history[self.history_idx])
        } else {
            None
        }
    }

    /// Navigate forward in history
    pub fn go_forward(&mut self) -> Option<&HistoryEntry> {
        if self.history_idx + 1 < self.history.len() {
            self.history_idx += 1;
            Some(&self.history[self.history_idx])
        } else {
            None
        }
    }

    /// Jump to a specific history entry
    pub fn goto(&mut self, idx: usize) -> Option<&HistoryEntry> {
        if idx < self.history.len() {
            self.history_idx = idx;
            Some(&self.history[self.history_idx])
        } else {
            None
        }
    }

    /// Clear the history
    pub fn clear_history(&mut self) {
        self.history.clear();
        self.history_idx = 0;
    }
}

impl Default for ReplState {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use mettail_runtime::{
        RuntimeBackend, RuntimeBackendArtifact, RuntimeBackendReport, RuntimeChannelObservation,
        RuntimeObservationValue,
    };

    #[derive(Debug, Clone)]
    struct TestTerm {
        display: &'static str,
        id: u64,
    }

    impl std::fmt::Display for TestTerm {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
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
            self.term_id() == other.term_id()
        }

        fn as_any(&self) -> &dyn Any {
            self
        }
    }

    #[test]
    fn ascent_results_are_projected_from_backend_report() {
        let mut state = ReplState::new();
        let term: Box<dyn Term> = Box::new(TestTerm { display: "x", id: 7 });
        state
            .set_term(term, AscentResults::empty())
            .expect("set Ascent term");

        assert!(state.backend_report().is_some());
        assert!(state.ascent_results().is_some());
        assert_eq!(state.current_graph_id(), Some(7));
    }

    #[test]
    fn observation_report_does_not_fabricate_ascent_results() {
        let mut state = ReplState::new();
        let term: Box<dyn Term> = Box::new(TestTerm { display: "5", id: 5 });
        let report = RuntimeBackendReport::try_observations(
            RuntimeBackend::RhoMachine,
            RuntimeBackendArtifact::RhoNormalizedAst,
            vec![RuntimeChannelObservation::new("OUT", vec![RuntimeObservationValue::Int(5)])],
        )
        .expect("test Rho observation report is shape-valid");
        state
            .set_term_with_report(term, report, 5)
            .expect("set Rho observation term");

        let report = state
            .backend_report()
            .expect("runtime backend report must be cached");
        assert_eq!(report.backend(), RuntimeBackend::RhoMachine);
        assert!(state.ascent_results().is_none());
        assert_eq!(state.current_graph_id(), Some(5));
    }
}
