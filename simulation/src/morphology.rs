//! Term morphology tracking.
//!
//! Tracks structural metrics of terms across simulation steps to detect
//! anomalies such as unbounded growth, stagnation, or structural collapse.
//!
//! `TermMetrics` are computed heuristically from a term's display string
//! by counting parentheses (depth) and tokens (size). This works across
//! all languages without requiring language-specific AST access.

use serde::{Deserialize, Serialize};
use std::collections::hash_map::DefaultHasher;
use std::hash::{Hash, Hasher};

/// Structural metrics for a single term.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TermMetrics {
    /// Number of tokens (approximation of AST node count).
    pub node_count: usize,
    /// Maximum nesting depth (parenthesis depth).
    pub depth: usize,
    /// A hash fingerprint of the term's structure.
    pub structural_fingerprint: u64,
}

impl TermMetrics {
    /// Compute metrics from a term's display string.
    ///
    /// - `node_count`: number of whitespace-separated tokens.
    /// - `depth`: maximum nesting depth of parentheses / brackets / braces.
    /// - `structural_fingerprint`: hash of the display string.
    pub fn from_display(display: &str) -> Self {
        let node_count = display.split_whitespace().count().max(1);

        // Compute maximum parenthesis depth (trampoline-style iterative).
        let mut max_depth: usize = 0;
        let mut current_depth: usize = 0;
        for ch in display.chars() {
            match ch {
                '(' | '[' | '{' => {
                    current_depth += 1;
                    if current_depth > max_depth {
                        max_depth = current_depth;
                    }
                },
                ')' | ']' | '}' => {
                    current_depth = current_depth.saturating_sub(1);
                },
                _ => {},
            }
        }

        let structural_fingerprint = fingerprint_of(display);

        TermMetrics {
            node_count,
            depth: max_depth,
            structural_fingerprint,
        }
    }
}

/// Compute the structural fingerprint of a term's display string.
///
/// Shared between per-step `TermMetrics::from_display` and aggregate
/// campaign recording so both sites hash with the same function. This
/// matters: the stagnation detector compares fingerprints by equality,
/// so any hash the campaign records must be in the same value domain
/// as per-step fingerprints or aggregate comparisons become garbage.
pub fn fingerprint_of(display: &str) -> u64 {
    let mut hasher = DefaultHasher::new();
    display.hash(&mut hasher);
    hasher.finish()
}

/// Alerts emitted by the morphology tracker when anomalous patterns are detected.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct MorphologyAlert {
    /// Step index at which the alert was triggered.
    pub step: usize,
    /// Description of the anomaly.
    pub message: String,
}

/// Summary of morphology metrics aggregated over a simulation trace.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct MorphologySummary {
    /// Number of steps recorded.
    pub total_steps: usize,
    /// Minimum node count observed.
    pub min_nodes: usize,
    /// Maximum node count observed.
    pub max_nodes: usize,
    /// Mean node count.
    pub mean_nodes: f64,
    /// Minimum depth observed.
    pub min_depth: usize,
    /// Maximum depth observed.
    pub max_depth: usize,
    /// Mean depth.
    pub mean_depth: f64,
    /// Number of distinct structural fingerprints (unique term shapes).
    pub distinct_shapes: usize,
    /// Any alerts raised during tracking.
    pub alerts: Vec<MorphologyAlert>,
}

/// Tracks term morphology across simulation steps.
///
/// Records `TermMetrics` for each step and computes summary statistics.
/// Detects anomalies such as monotonically increasing size (potential
/// non-termination) or structural stagnation.
pub struct MorphologyTracker {
    /// All metrics recorded, one per step.
    metrics: Vec<TermMetrics>,
    /// Alerts accumulated during tracking.
    alerts: Vec<MorphologyAlert>,
    /// Window size for trend detection.
    trend_window: usize,
}

impl MorphologyTracker {
    /// Create a new tracker with a default trend window of 10 steps.
    pub fn new() -> Self {
        Self {
            metrics: Vec::new(),
            alerts: Vec::new(),
            trend_window: 10,
        }
    }

    /// Create a tracker with a custom trend window size.
    pub fn with_trend_window(trend_window: usize) -> Self {
        Self {
            metrics: Vec::new(),
            alerts: Vec::new(),
            trend_window: trend_window.max(2),
        }
    }

    /// Record metrics for a new step.
    pub fn record(&mut self, metrics: TermMetrics) {
        self.metrics.push(metrics);
        // Check for trends after accumulating enough data.
        self.check_trends();
    }

    /// Check for morphological anomalies in recent data.
    fn check_trends(&mut self) {
        let len = self.metrics.len();
        if len < self.trend_window {
            return;
        }

        let window = &self.metrics[len - self.trend_window..];

        // Check for monotonically increasing node count (potential non-termination).
        let monotone_increasing = window
            .windows(2)
            .all(|pair| pair[1].node_count >= pair[0].node_count)
            && window.last().expect("window non-empty").node_count
                > window.first().expect("window non-empty").node_count;

        if monotone_increasing {
            self.alerts.push(MorphologyAlert {
                step: len - 1,
                message: format!(
                    "Node count monotonically increasing over last {} steps ({} -> {})",
                    self.trend_window,
                    window.first().expect("window non-empty").node_count,
                    window.last().expect("window non-empty").node_count,
                ),
            });
        }

        // Check for structural stagnation (all fingerprints identical).
        let first_fp = window
            .first()
            .expect("window non-empty")
            .structural_fingerprint;
        let all_same = window.iter().all(|m| m.structural_fingerprint == first_fp);
        if all_same && len > self.trend_window {
            self.alerts.push(MorphologyAlert {
                step: len - 1,
                message: format!(
                    "Term structurally stagnant for {} steps (fingerprint={:#x})",
                    self.trend_window, first_fp,
                ),
            });
        }
    }

    /// Return all alerts accumulated so far.
    pub fn check(&self) -> Vec<MorphologyAlert> {
        self.alerts.clone()
    }

    /// Compute a summary of all recorded metrics.
    pub fn summary(&self) -> MorphologySummary {
        if self.metrics.is_empty() {
            return MorphologySummary {
                total_steps: 0,
                min_nodes: 0,
                max_nodes: 0,
                mean_nodes: 0.0,
                min_depth: 0,
                max_depth: 0,
                mean_depth: 0.0,
                distinct_shapes: 0,
                alerts: self.alerts.clone(),
            };
        }

        let total_steps = self.metrics.len();
        let mut min_nodes = usize::MAX;
        let mut max_nodes = 0usize;
        let mut sum_nodes: u64 = 0;
        let mut min_depth = usize::MAX;
        let mut max_depth = 0usize;
        let mut sum_depth: u64 = 0;
        let mut fingerprints = std::collections::HashSet::with_capacity(total_steps);

        for m in &self.metrics {
            if m.node_count < min_nodes {
                min_nodes = m.node_count;
            }
            if m.node_count > max_nodes {
                max_nodes = m.node_count;
            }
            sum_nodes += m.node_count as u64;

            if m.depth < min_depth {
                min_depth = m.depth;
            }
            if m.depth > max_depth {
                max_depth = m.depth;
            }
            sum_depth += m.depth as u64;

            fingerprints.insert(m.structural_fingerprint);
        }

        MorphologySummary {
            total_steps,
            min_nodes,
            max_nodes,
            mean_nodes: sum_nodes as f64 / total_steps as f64,
            min_depth,
            max_depth,
            mean_depth: sum_depth as f64 / total_steps as f64,
            distinct_shapes: fingerprints.len(),
            alerts: self.alerts.clone(),
        }
    }
}

impl Default for MorphologyTracker {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_term_metrics_from_display_simple() {
        let m = TermMetrics::from_display("42");
        assert_eq!(m.node_count, 1);
        assert_eq!(m.depth, 0);
    }

    #[test]
    fn test_term_metrics_from_display_nested() {
        let m = TermMetrics::from_display("(1 + (2 * 3))");
        assert_eq!(m.depth, 2);
        assert!(m.node_count >= 5);
    }

    #[test]
    fn test_morphology_tracker_basic() {
        let mut tracker = MorphologyTracker::new();
        tracker.record(TermMetrics::from_display("1 + 2"));
        tracker.record(TermMetrics::from_display("3"));
        let summary = tracker.summary();
        assert_eq!(summary.total_steps, 2);
        assert!(summary.min_nodes >= 1);
    }

    #[test]
    fn test_morphology_tracker_monotone_alert() {
        let mut tracker = MorphologyTracker::with_trend_window(3);
        // Feed strictly increasing sizes.
        for i in 0..5 {
            let display = "x ".repeat(i + 1);
            tracker.record(TermMetrics::from_display(&display));
        }
        let alerts = tracker.check();
        assert!(
            alerts
                .iter()
                .any(|a| a.message.contains("monotonically increasing")),
            "Expected monotone increasing alert, got: {:?}",
            alerts,
        );
    }

    #[test]
    fn test_morphology_summary_empty() {
        let tracker = MorphologyTracker::new();
        let summary = tracker.summary();
        assert_eq!(summary.total_steps, 0);
        assert_eq!(summary.distinct_shapes, 0);
    }
}
