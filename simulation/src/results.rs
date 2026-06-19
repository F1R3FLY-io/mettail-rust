//! Campaign results and failure reporting.
//!
//! `CampaignResults` aggregates the outcomes of an entire simulation campaign
//! (multiple test cases). `SimulationFailure` records individual failures
//! with their input, seed, trace, and error message for reproducibility.

use crate::morphology::MorphologySummary;
use crate::trace::ExecutionTrace;
use std::collections::HashMap;
use std::fmt;

/// Results of a simulation campaign (multiple test cases).
#[derive(Debug)]
pub struct CampaignResults {
    /// Total number of test cases executed.
    pub total_cases: usize,
    /// Number of cases that passed.
    pub passed: usize,
    /// Number of cases that failed.
    pub failed: usize,
    /// All failures encountered during the campaign.
    pub failures: Vec<SimulationFailure>,
    /// Rule coverage statistics.
    pub coverage: RuleCoverage,
    /// Aggregate morphology summary across all cases (if tracking was enabled).
    pub aggregate_morphology: Option<MorphologySummary>,
}

impl CampaignResults {
    /// Create an empty results container.
    pub fn new() -> Self {
        Self {
            total_cases: 0,
            passed: 0,
            failed: 0,
            failures: Vec::new(),
            coverage: RuleCoverage::new(),
            aggregate_morphology: None,
        }
    }

    /// Record a passed case.
    pub fn record_pass(&mut self) {
        self.total_cases += 1;
        self.passed += 1;
    }

    /// Record a failed case.
    pub fn record_failure(&mut self, failure: SimulationFailure) {
        self.total_cases += 1;
        self.failed += 1;
        self.failures.push(failure);
    }

    /// Whether the campaign succeeded (no failures).
    pub fn is_success(&self) -> bool {
        self.failures.is_empty()
    }
}

impl Default for CampaignResults {
    fn default() -> Self {
        Self::new()
    }
}

impl fmt::Display for CampaignResults {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(
            f,
            "Campaign: {} total, {} passed, {} failed",
            self.total_cases, self.passed, self.failed
        )?;
        if !self.failures.is_empty() {
            writeln!(f, "Failures:")?;
            for (i, failure) in self.failures.iter().enumerate() {
                writeln!(
                    f,
                    "  [{}] seed={}, input={:?}, error={}",
                    i, failure.seed, failure.input, failure.error,
                )?;
            }
        }
        write!(f, "Coverage: {}", self.coverage)
    }
}

/// A single simulation failure within a campaign.
#[derive(Debug)]
pub struct SimulationFailure {
    /// Seed that triggered this failure (for reproducibility).
    pub seed: String,
    /// The input string that caused the failure.
    pub input: String,
    /// Full execution trace leading to the failure.
    pub trace: ExecutionTrace,
    /// Human-readable error message.
    pub error: String,
}

/// Rule coverage statistics from a simulation campaign.
#[derive(Debug, Clone)]
pub struct RuleCoverage {
    /// Count of how many times each rule fired.
    pub rules_fired: HashMap<String, usize>,
    /// Total number of rules in the language.
    pub total_rules: usize,
    /// Percentage of rules that fired at least once.
    pub coverage_pct: f64,
}

impl RuleCoverage {
    /// Create empty coverage.
    pub fn new() -> Self {
        Self {
            rules_fired: HashMap::new(),
            total_rules: 0,
            coverage_pct: 0.0,
        }
    }

    /// Record that a rule fired.
    pub fn record_rule(&mut self, rule_name: &str) {
        *self.rules_fired.entry(rule_name.to_string()).or_insert(0) += 1;
    }

    /// Finalize coverage computation given the total number of rules.
    pub fn finalize(&mut self, total_rules: usize) {
        self.total_rules = total_rules;
        if total_rules > 0 {
            let covered = self.rules_fired.len().min(total_rules);
            self.coverage_pct = (covered as f64 / total_rules as f64) * 100.0;
        } else {
            self.coverage_pct = 100.0;
        }
    }

    /// Merge another RuleCoverage into this one (for aggregation).
    pub fn merge(&mut self, other: &RuleCoverage) {
        for (rule, count) in &other.rules_fired {
            *self.rules_fired.entry(rule.clone()).or_insert(0) += count;
        }
    }
}

impl Default for RuleCoverage {
    fn default() -> Self {
        Self::new()
    }
}

impl fmt::Display for RuleCoverage {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{}/{} rules covered ({:.1}%), {} total firings",
            self.rules_fired.len(),
            self.total_rules,
            self.coverage_pct,
            self.rules_fired.values().sum::<usize>(),
        )
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::trace::{ExecutionTrace, TraceOutcome};

    #[test]
    fn test_campaign_results_tracking() {
        let mut results = CampaignResults::new();
        results.record_pass();
        results.record_pass();

        let trace = ExecutionTrace {
            seed: "seed1".to_string(),
            language: "Test".to_string(),
            steps: vec![],
            outcome: TraceOutcome::Error { message: "test error".to_string() },
            morphology: None,
        };
        results.record_failure(SimulationFailure {
            seed: "seed1".to_string(),
            input: "bad input".to_string(),
            trace,
            error: "test error".to_string(),
        });

        assert_eq!(results.total_cases, 3);
        assert_eq!(results.passed, 2);
        assert_eq!(results.failed, 1);
        assert!(!results.is_success());
    }

    #[test]
    fn test_rule_coverage() {
        let mut coverage = RuleCoverage::new();
        coverage.record_rule("AddInt");
        coverage.record_rule("AddInt");
        coverage.record_rule("SubInt");
        coverage.finalize(10);

        assert_eq!(coverage.rules_fired.len(), 2);
        assert_eq!(coverage.rules_fired["AddInt"], 2);
        assert_eq!(coverage.rules_fired["SubInt"], 1);
        assert_eq!(coverage.total_rules, 10);
        assert!((coverage.coverage_pct - 20.0).abs() < 0.01);
    }

    #[test]
    fn test_campaign_display() {
        let mut results = CampaignResults::new();
        results.record_pass();
        results.coverage.record_rule("Rule1");
        results.coverage.finalize(5);
        let display = format!("{}", results);
        assert!(display.contains("1 total"));
        assert!(display.contains("1 passed"));
    }
}
