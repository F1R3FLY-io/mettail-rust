//! Coverage-Guided Generation
//!
//! Tracks which rewrite rules and constructors are exercised during simulation,
//! enabling coverage-guided test generation. The `SimulationCoverage` struct
//! records rule firings and constructor hits, computes coverage percentages,
//! and identifies uncovered rules.
//!
//! ## Architecture
//!
//! ```text
//! ExecutionTrace ── coverage_from_trace() ──┐
//!                                           ▼
//! explicit AscentResults ── coverage_from_ascent() ── SimulationCoverage
//!   ├── rule_firings: HashMap<String, usize>
//!   ├── constructor_hits: HashMap<String, usize>
//!   └── total_steps: usize
//!         │
//!         ├── coverage_pct(total_rules) ──→ f64
//!         ├── uncovered_rules(all_rules) ──→ Vec<String>
//!         └── merge(other) ──→ combined coverage
//! ```

use std::collections::HashMap;

use mettail_runtime::{AscentResults, Language};
use proptest::strategy::Strategy;

use crate::results::SimulationFailure;
use crate::runner::{SimulationConfig, SimulationRunner};
use crate::trace::ExecutionTrace;

/// Coverage tracker for simulation runs.
///
/// Records which rewrite rules have fired and which constructors have been
/// encountered, along with the total number of simulation steps. This
/// information drives coverage-guided test generation by identifying
/// under-explored areas of the language.
#[derive(Debug, Clone)]
pub struct SimulationCoverage {
    /// Map from rule name to the number of times it fired.
    pub rule_firings: HashMap<String, usize>,
    /// Map from constructor name to the number of times it was encountered.
    pub constructor_hits: HashMap<String, usize>,
    /// Total simulation steps recorded.
    pub total_steps: usize,
}

impl SimulationCoverage {
    /// Create a new empty coverage tracker.
    pub fn new() -> Self {
        SimulationCoverage {
            rule_firings: HashMap::new(),
            constructor_hits: HashMap::new(),
            total_steps: 0,
        }
    }

    /// Record a rewrite rule firing.
    ///
    /// Increments the count for the given rule name and the total step count.
    pub fn record_rewrite(&mut self, rule_name: &str) {
        *self.rule_firings.entry(rule_name.to_string()).or_insert(0) += 1;
        self.total_steps += 1;
    }

    /// Record a constructor being encountered.
    ///
    /// Increments the count for the given constructor name.
    pub fn record_constructor(&mut self, ctor_name: &str) {
        *self
            .constructor_hits
            .entry(ctor_name.to_string())
            .or_insert(0) += 1;
    }

    /// Compute the coverage percentage.
    ///
    /// Returns the fraction of `total_rules` that have been fired at least
    /// once, expressed as a percentage (0.0 to 100.0).
    ///
    /// # Arguments
    ///
    /// * `total_rules` - The total number of rules in the language.
    ///
    /// # Returns
    ///
    /// Coverage percentage. Returns 100.0 if `total_rules` is 0.
    pub fn coverage_pct(&self, total_rules: usize) -> f64 {
        if total_rules == 0 {
            return 100.0;
        }
        let covered = self.rule_firings.len();
        (covered as f64 / total_rules as f64) * 100.0
    }

    /// Identify rules that have not been covered.
    ///
    /// Returns the subset of `all_rules` that do not appear in the
    /// `rule_firings` map.
    ///
    /// # Arguments
    ///
    /// * `all_rules` - The complete list of rule names in the language.
    ///
    /// # Returns
    ///
    /// A vector of rule names that have zero firings.
    pub fn uncovered_rules(&self, all_rules: &[String]) -> Vec<String> {
        all_rules
            .iter()
            .filter(|rule| !self.rule_firings.contains_key(rule.as_str()))
            .cloned()
            .collect()
    }

    /// Merge another coverage report into this one.
    ///
    /// Combines rule firings and constructor hits by summing counts,
    /// and adds the total steps.
    pub fn merge(&mut self, other: &SimulationCoverage) {
        for (rule, count) in &other.rule_firings {
            *self.rule_firings.entry(rule.clone()).or_insert(0) += count;
        }
        for (ctor, count) in &other.constructor_hits {
            *self.constructor_hits.entry(ctor.clone()).or_insert(0) += count;
        }
        self.total_steps += other.total_steps;
    }
}

impl Default for SimulationCoverage {
    fn default() -> Self {
        Self::new()
    }
}

/// Compute coverage from Ascent execution results.
///
/// Extracts rule firing information from the rewrite trace and constructor
/// hit information from the term graph. Each rewrite with a named rule
/// is recorded as a rule firing. Each unique term display string is parsed
/// for its top-level constructor name.
///
/// # Arguments
///
/// * `results` - The Ascent execution results containing terms and rewrites.
///
/// # Returns
///
/// A `SimulationCoverage` populated from the results.
pub fn coverage_from_ascent(results: &AscentResults) -> SimulationCoverage {
    let mut coverage = SimulationCoverage::new();

    // Record rule firings from rewrites.
    for rewrite in &results.rewrites {
        if let Some(ref name) = rewrite.rule_name {
            coverage.record_rewrite(name);
        } else {
            // Anonymous rewrites are recorded under a synthetic name.
            coverage.record_rewrite("__anonymous__");
        }
    }

    // Record constructor hits from terms.
    // The constructor name is extracted as the first identifier-like token
    // from the term's display string. For terms like "(AddInt 3 5)" or
    // "PZero" or "*(n)", we extract the constructor name.
    for term_info in &results.all_terms {
        let ctor_name = extract_constructor_name(&term_info.display);
        if !ctor_name.is_empty() {
            coverage.record_constructor(&ctor_name);
        }
    }

    coverage
}

/// Compute coverage from a report-aware simulation trace.
///
/// Rewrite operations are recorded as rule firings. All step displays are
/// scanned for constructor-shape diversity. Terminal runtime-report and
/// runtime-observation steps therefore contribute constructor coverage without
/// fabricating rewrite-rule firings.
pub fn coverage_from_trace(trace: &ExecutionTrace) -> SimulationCoverage {
    let mut coverage = SimulationCoverage::new();

    for entry in &trace.steps {
        if let Some(rule_name) = entry.operation.strip_prefix("rewrite:") {
            coverage.record_rewrite(rule_name);
        } else if entry.operation == "rewrite" {
            coverage.record_rewrite("__anonymous__");
        }

        let ctor_name = extract_constructor_name(&entry.term_display);
        if !ctor_name.is_empty() {
            coverage.record_constructor(&ctor_name);
        }
    }

    coverage
}

/// Extract the constructor name from a term display string.
///
/// Handles formats like:
/// - "(AddInt 3 5)" -> "AddInt"
/// - "PZero" -> "PZero"
/// - "*(n)" -> "*"
/// - "3" -> "3" (literal)
/// - "@({})" -> "@"
fn extract_constructor_name(display: &str) -> String {
    let trimmed = display.trim();
    if trimmed.is_empty() {
        return String::new();
    }

    // Strip leading '(' if present (e.g., "(AddInt 3 5)")
    let inner = if trimmed.starts_with('(') {
        &trimmed[1..]
    } else {
        trimmed
    };

    // Extract the first "word" (sequence of alphanumeric chars or common operators)
    let mut chars = inner.chars();
    let first = match chars.next() {
        Some(c) => c,
        None => return String::new(),
    };

    if first.is_alphabetic() || first == '_' {
        // Identifier: collect alphanumeric + underscore
        let mut name = String::with_capacity(16);
        name.push(first);
        for c in chars {
            if c.is_alphanumeric() || c == '_' {
                name.push(c);
            } else {
                break;
            }
        }
        name
    } else if first.is_ascii_digit() || first == '-' {
        // Numeric literal
        let mut name = String::with_capacity(8);
        name.push(first);
        for c in chars {
            if c.is_ascii_digit() || c == '.' {
                name.push(c);
            } else {
                break;
            }
        }
        name
    } else {
        // Operator or symbol (e.g., *, @, {})
        first.to_string()
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// CoverageGuidedCampaign — iterative feedback loop
// ══════════════════════════════════════════════════════════════════════════════

/// Configuration and driver for a coverage-guided simulation campaign.
///
/// Each iteration generates random terms via a proptest strategy, simulates
/// them through the language's parse/rewrite pipeline, and collects rule
/// firing coverage. Coverage is accumulated across iterations. When the
/// improvement plateaus (i.e., the increase in coverage percentage falls
/// below `plateau_threshold` per iteration), the campaign stops.
///
/// ## Feedback Loop
///
/// ```text
/// ┌──────────────────────────────────────┐
/// │  1. Generate random terms via strategy │
/// │  2. Run SimulationRunner::run_campaign │
/// │  3. Extract coverage via              │
/// │     coverage_from_trace per term      │
/// │  4. Merge into accumulated coverage   │
/// │  5. Compute improvement vs previous   │
/// │  6. If improvement < threshold, stop  │
/// └──────────────────────────────────────┘
/// ```
pub struct CoverageGuidedCampaign<'a> {
    /// The language under test.
    language: &'a dyn Language,
    /// Maximum number of feedback iterations.
    max_iterations: usize,
    /// Number of proptest cases to generate per iteration.
    cases_per_iteration: u32,
    /// Maximum rewrite steps per simulation run.
    max_steps: usize,
    /// Stop when the per-iteration coverage improvement (in percentage points)
    /// falls below this threshold.
    plateau_threshold: f64,
}

/// Aggregate results from a coverage-guided campaign.
#[derive(Debug)]
pub struct CoverageGuidedResults {
    /// Total number of simulation runs executed across all iterations.
    pub total_runs: usize,
    /// Number of iterations completed.
    pub iterations: usize,
    /// The final accumulated coverage snapshot.
    pub final_coverage: SimulationCoverage,
    /// Coverage percentage at the end of each iteration.
    pub coverage_history: Vec<f64>,
    /// All failures encountered across all iterations.
    pub failures: Vec<SimulationFailure>,
}

impl<'a> CoverageGuidedCampaign<'a> {
    /// Create a new coverage-guided campaign with default parameters.
    ///
    /// Defaults:
    /// - `max_iterations`: 20
    /// - `cases_per_iteration`: 50
    /// - `max_steps`: 1000
    /// - `plateau_threshold`: 1.0 (1 percentage point)
    pub fn new(language: &'a dyn Language) -> Self {
        CoverageGuidedCampaign {
            language,
            max_iterations: 20,
            cases_per_iteration: 50,
            max_steps: 1000,
            plateau_threshold: 1.0,
        }
    }

    /// Set the maximum number of iterations.
    pub fn max_iterations(mut self, n: usize) -> Self {
        self.max_iterations = n;
        self
    }

    /// Set the number of proptest cases per iteration.
    pub fn cases_per_iteration(mut self, n: u32) -> Self {
        self.cases_per_iteration = n;
        self
    }

    /// Set the maximum rewrite steps per simulation run.
    pub fn max_steps(mut self, n: usize) -> Self {
        self.max_steps = n;
        self
    }

    /// Set the plateau threshold (in percentage points).
    ///
    /// The campaign stops when the per-iteration coverage improvement
    /// drops below this value.
    pub fn plateau_threshold(mut self, threshold: f64) -> Self {
        self.plateau_threshold = threshold;
        self
    }

    /// Run the coverage-guided campaign.
    ///
    /// The `strategy_factory` is called once per iteration to produce a fresh
    /// strategy. This avoids requiring `Clone` on strategy types (many proptest
    /// combinators such as `prop_oneof!` do not implement `Clone`).
    ///
    /// The feedback loop:
    /// 1. Generate random terms via the strategy returned by `strategy_factory`.
    /// 2. Run simulation via `SimulationRunner::run_campaign()`, collecting
    ///    rule firing coverage.
    /// 3. Compute coverage improvement vs the previous iteration.
    /// 4. If improvement < `plateau_threshold`, stop.
    /// 5. Otherwise, continue with the next iteration.
    ///
    /// Returns aggregate results with coverage history.
    pub fn run<S, F>(&self, strategy_factory: F) -> CoverageGuidedResults
    where
        S: Strategy<Value = String>,
        F: Fn() -> S,
    {
        let total_rules = self.language.metadata().rewrites().len();
        let mut accumulated_coverage = SimulationCoverage::new();
        let mut coverage_history: Vec<f64> = Vec::with_capacity(self.max_iterations);
        let mut all_failures: Vec<SimulationFailure> = Vec::new();
        let mut total_runs: usize = 0;
        let mut iterations_completed: usize = 0;

        for _iteration in 0..self.max_iterations {
            let config = SimulationConfig {
                max_steps: self.max_steps,
                proptest_cases: self.cases_per_iteration,
                track_morphology: false,
                ..SimulationConfig::default()
            };

            let mut runner = SimulationRunner::new(self.language, config);
            let strategy = strategy_factory();
            let campaign_results = runner.run_campaign(strategy);

            total_runs += campaign_results.total_cases;

            // Collect failures.
            all_failures.extend(campaign_results.failures);

            // Merge rule coverage from this iteration's campaign results
            // into the accumulated coverage.
            for (rule_name, &count) in &campaign_results.coverage.rules_fired {
                for _ in 0..count {
                    accumulated_coverage.record_rewrite(rule_name);
                }
            }

            // Compute coverage after this iteration.
            let current_pct = accumulated_coverage.coverage_pct(total_rules);
            let previous_pct = coverage_history.last().copied().unwrap_or(0.0);
            let improvement = current_pct - previous_pct;

            coverage_history.push(current_pct);
            iterations_completed += 1;

            // Check for plateau: if the improvement in this iteration is below
            // the threshold, stop the campaign.
            if improvement < self.plateau_threshold && iterations_completed > 1 {
                break;
            }

            // If we've reached 100% coverage, no point continuing.
            if current_pct >= 100.0 {
                break;
            }
        }

        CoverageGuidedResults {
            total_runs,
            iterations: iterations_completed,
            final_coverage: accumulated_coverage,
            coverage_history,
            failures: all_failures,
        }
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// Tests
// ══════════════════════════════════════════════════════════════════════════════

#[cfg(test)]
mod tests {
    use super::*;
    use crate::trace::{ExecutionTrace, TraceEntry, TraceOutcome};
    use mettail_runtime::{Rewrite, TermInfo};

    #[test]
    fn test_coverage_tracking() {
        let mut coverage = SimulationCoverage::new();

        // Record some rewrites
        coverage.record_rewrite("Comm");
        coverage.record_rewrite("Exec");
        coverage.record_rewrite("Comm");
        coverage.record_rewrite("Comm");

        // Verify counts
        assert_eq!(coverage.rule_firings.get("Comm"), Some(&3));
        assert_eq!(coverage.rule_firings.get("Exec"), Some(&1));
        assert_eq!(coverage.total_steps, 4);

        // Record constructors
        coverage.record_constructor("PZero");
        coverage.record_constructor("PPar");
        coverage.record_constructor("PZero");

        assert_eq!(coverage.constructor_hits.get("PZero"), Some(&2));
        assert_eq!(coverage.constructor_hits.get("PPar"), Some(&1));

        // Coverage: 2 rules covered out of 5 total
        let pct = coverage.coverage_pct(5);
        assert!((pct - 40.0).abs() < f64::EPSILON);
    }

    #[test]
    fn test_coverage_merge() {
        let mut cov_a = SimulationCoverage::new();
        cov_a.record_rewrite("Comm");
        cov_a.record_rewrite("Comm");
        cov_a.record_constructor("PZero");
        cov_a.record_constructor("PPar");

        let mut cov_b = SimulationCoverage::new();
        cov_b.record_rewrite("Exec");
        cov_b.record_rewrite("Comm");
        cov_b.record_constructor("PZero");
        cov_b.record_constructor("NQuote");

        // Merge B into A
        cov_a.merge(&cov_b);

        // Rule firings should be summed
        assert_eq!(cov_a.rule_firings.get("Comm"), Some(&3));
        assert_eq!(cov_a.rule_firings.get("Exec"), Some(&1));

        // Constructor hits should be summed
        assert_eq!(cov_a.constructor_hits.get("PZero"), Some(&2));
        assert_eq!(cov_a.constructor_hits.get("PPar"), Some(&1));
        assert_eq!(cov_a.constructor_hits.get("NQuote"), Some(&1));

        // Total steps should be summed
        assert_eq!(cov_a.total_steps, 4); // 2 from A + 2 from B

        // Coverage: 2 unique rules out of 4 total
        let pct = cov_a.coverage_pct(4);
        assert!((pct - 50.0).abs() < f64::EPSILON);
    }

    #[test]
    fn test_uncovered_detection() {
        let mut coverage = SimulationCoverage::new();
        coverage.record_rewrite("Comm");
        coverage.record_rewrite("Exec");

        let all_rules: Vec<String> = vec![
            "Comm".to_string(),
            "Exec".to_string(),
            "ParCong".to_string(),
            "NewCong".to_string(),
            "AddCongL".to_string(),
        ];

        let uncovered = coverage.uncovered_rules(&all_rules);
        assert_eq!(uncovered.len(), 3);
        assert!(uncovered.contains(&"ParCong".to_string()));
        assert!(uncovered.contains(&"NewCong".to_string()));
        assert!(uncovered.contains(&"AddCongL".to_string()));

        // Comm and Exec should NOT be in uncovered
        assert!(!uncovered.contains(&"Comm".to_string()));
        assert!(!uncovered.contains(&"Exec".to_string()));
    }

    #[test]
    fn test_coverage_pct_edge_cases() {
        let coverage = SimulationCoverage::new();

        // Zero total rules: 100% coverage (vacuous)
        assert!((coverage.coverage_pct(0) - 100.0).abs() < f64::EPSILON);

        // Zero covered, some total: 0%
        assert!((coverage.coverage_pct(5) - 0.0).abs() < f64::EPSILON);
    }

    #[test]
    fn test_coverage_from_ascent() {
        let results = AscentResults {
            all_terms: vec![
                TermInfo {
                    term_id: 1,
                    exact_key: None,
                    display: "(AddInt 3 5)".to_string(),
                    is_normal_form: false,
                },
                TermInfo {
                    term_id: 2,
                    exact_key: None,
                    display: "8".to_string(),
                    is_normal_form: true,
                },
                TermInfo {
                    term_id: 3,
                    exact_key: None,
                    display: "(SubInt 10 2)".to_string(),
                    is_normal_form: false,
                },
            ],
            rewrites: vec![
                Rewrite {
                    from_id: 1,
                    to_id: 2,
                    from_key: None,
                    to_key: None,
                    rule_name: Some("fold_AddInt".to_string()),
                },
                Rewrite {
                    from_id: 3,
                    to_id: 2,
                    from_key: None,
                    to_key: None,
                    rule_name: Some("fold_SubInt".to_string()),
                },
                Rewrite {
                    from_id: 1,
                    to_id: 3,
                    from_key: None,
                    to_key: None,
                    rule_name: None,
                },
            ],
            equivalences: vec![],
            custom_relations: std::collections::HashMap::new(),
        };

        let coverage = coverage_from_ascent(&results);

        // 2 named rules + 1 anonymous
        assert_eq!(coverage.rule_firings.get("fold_AddInt"), Some(&1));
        assert_eq!(coverage.rule_firings.get("fold_SubInt"), Some(&1));
        assert_eq!(coverage.rule_firings.get("__anonymous__"), Some(&1));
        assert_eq!(coverage.total_steps, 3);

        // Constructors extracted from terms
        assert_eq!(coverage.constructor_hits.get("AddInt"), Some(&1));
        assert_eq!(coverage.constructor_hits.get("SubInt"), Some(&1));
        assert_eq!(coverage.constructor_hits.get("8"), Some(&1));
    }

    #[test]
    fn test_coverage_from_trace_records_rewrite_rules_and_constructors() {
        let trace = ExecutionTrace {
            seed: "case_0".to_string(),
            language: "TraceLang".to_string(),
            steps: vec![
                TraceEntry {
                    step_index: 0,
                    term_display: "(AddInt 3 5)".to_string(),
                    operation: "parse".to_string(),
                    metrics: None,
                },
                TraceEntry {
                    step_index: 1,
                    term_display: "8".to_string(),
                    operation: "rewrite:fold_AddInt".to_string(),
                    metrics: None,
                },
            ],
            outcome: TraceOutcome::NormalForm { term: "8".to_string(), steps: 2 },
            morphology: None,
        };

        let coverage = coverage_from_trace(&trace);

        assert_eq!(coverage.rule_firings.get("fold_AddInt"), Some(&1));
        assert_eq!(coverage.total_steps, 1);
        assert_eq!(coverage.constructor_hits.get("AddInt"), Some(&1));
        assert_eq!(coverage.constructor_hits.get("8"), Some(&1));
    }

    #[test]
    fn test_coverage_from_trace_does_not_fabricate_runtime_rule_firings() {
        let trace = ExecutionTrace {
            seed: "case_1".to_string(),
            language: "RuntimeLang".to_string(),
            steps: vec![
                TraceEntry {
                    step_index: 0,
                    term_display: "source".to_string(),
                    operation: "parse".to_string(),
                    metrics: None,
                },
                TraceEntry {
                    step_index: 1,
                    term_display:
                        "DovetailRunReport(completeness=Complete, roots=[root], terms=1, edges=0)"
                            .to_string(),
                    operation: "runtime:Dovetail:DovetailRunReport".to_string(),
                    metrics: None,
                },
            ],
            outcome: TraceOutcome::RuntimeReport {
                backend: "Dovetail".to_string(),
                artifact: "DovetailRunReport".to_string(),
                summary: "DovetailRunReport(completeness=Complete, roots=[root], terms=1, edges=0)"
                    .to_string(),
            },
            morphology: None,
        };

        let coverage = coverage_from_trace(&trace);

        assert!(coverage.rule_firings.is_empty());
        assert_eq!(coverage.total_steps, 0);
        assert_eq!(coverage.constructor_hits.get("source"), Some(&1));
        assert_eq!(coverage.constructor_hits.get("DovetailRunReport"), Some(&1));
    }

    #[test]
    fn test_extract_constructor_name() {
        assert_eq!(extract_constructor_name("(AddInt 3 5)"), "AddInt");
        assert_eq!(extract_constructor_name("PZero"), "PZero");
        assert_eq!(extract_constructor_name("*(n)"), "*");
        assert_eq!(extract_constructor_name("@({})"), "@");
        assert_eq!(extract_constructor_name("42"), "42");
        assert_eq!(extract_constructor_name("-7"), "-7");
        assert_eq!(extract_constructor_name(""), "");
        assert_eq!(extract_constructor_name("   "), "");
        assert_eq!(extract_constructor_name("(PPar {PZero, PZero})"), "PPar");
    }
}
