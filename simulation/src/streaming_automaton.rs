//! Streaming automata for real-time invariant monitoring.
//!
//! Streaming monitors process trace events one at a time without buffering,
//! maintaining a finite state that summarizes the trace seen so far. This
//! enables memory-bounded monitoring of arbitrarily long simulation traces.
//!
//! ## Architecture
//!
//! ```text
//! trace events ──→ StreamingMonitor ──→ alerts/metrics
//!                    │
//!                    ├── WindowedMonitor (sliding window)
//!                    ├── AggregateMonitor (running statistics)
//!                    └── CompositeMonitor (parallel composition)
//! ```
//!
//! ## Composability
//!
//! Multiple monitors run in parallel over the same trace. Each processes
//! the same event independently, producing its own alerts. The
//! `CompositeMonitor` coordinates multiple monitors and merges their outputs.

use std::collections::VecDeque;
use std::fmt;

/// A single event in a simulation trace.
#[derive(Debug, Clone, serde::Serialize, serde::Deserialize)]
pub struct TraceEvent {
    /// Step index (0-based).
    pub step: usize,
    /// Display representation of the current term.
    pub term_display: String,
    /// Name of the operation applied (rewrite rule name, "parse", "normalize", etc.).
    pub operation: String,
    /// Term size (number of AST nodes).
    pub term_size: usize,
    /// Term depth (maximum nesting).
    pub term_depth: usize,
}

/// An alert emitted by a streaming monitor.
#[derive(Debug, Clone, serde::Serialize, serde::Deserialize)]
pub struct MonitorAlert {
    /// Step at which the alert was triggered.
    pub step: usize,
    /// Monitor that produced the alert.
    pub monitor_name: String,
    /// Alert severity.
    pub severity: AlertSeverity,
    /// Human-readable message.
    pub message: String,
}

/// Alert severity levels.
#[derive(Debug, Clone, Copy, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub enum AlertSeverity {
    /// Informational (no action required).
    Info,
    /// Warning (potential issue, may need investigation).
    Warning,
    /// Error (invariant violated, simulation may be unsound).
    Error,
}

impl fmt::Display for AlertSeverity {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            AlertSeverity::Info => write!(f, "INFO"),
            AlertSeverity::Warning => write!(f, "WARN"),
            AlertSeverity::Error => write!(f, "ERROR"),
        }
    }
}

/// Trait for streaming monitors that process trace events one at a time.
///
/// Monitors maintain internal state and emit alerts when conditions are met.
/// Memory usage is O(1) or O(window_size), not O(trace_length).
pub trait StreamingMonitor: Send + Sync {
    /// The monitor's name (for alert attribution).
    fn name(&self) -> &str;

    /// Process a single trace event. Returns alerts (if any) triggered by this event.
    fn process(&mut self, event: &TraceEvent) -> Vec<MonitorAlert>;

    /// Finalize the monitor at the end of the trace. Returns any remaining alerts.
    fn finalize(&mut self) -> Vec<MonitorAlert>;

    /// Reset the monitor to its initial state (for reuse across simulation runs).
    fn reset(&mut self);
}

/// Windowed monitor: tracks metrics over a sliding window of the last N events.
///
/// Useful for detecting local trends (e.g., "term size increased for the last
/// 50 steps") without being affected by early-trace transients.
pub struct WindowedMonitor {
    name: String,
    window_size: usize,
    window: VecDeque<f64>,
    threshold: f64,
    check: WindowCheck,
}

/// What to check in the sliding window.
#[derive(Debug, Clone, Copy)]
pub enum WindowCheck {
    /// Alert if the mean of the window exceeds the threshold.
    MeanAbove,
    /// Alert if the mean of the window falls below the threshold.
    MeanBelow,
    /// Alert if the variance of the window exceeds the threshold.
    VarianceAbove,
    /// Alert if all values in the window are monotonically increasing.
    MonotonicallyIncreasing,
    /// Alert if all values in the window are the same (stagnation).
    Stagnant,
}

impl WindowedMonitor {
    /// Create a new windowed monitor.
    pub fn new(name: impl Into<String>, window_size: usize, threshold: f64, check: WindowCheck) -> Self {
        Self {
            name: name.into(),
            window_size,
            window: VecDeque::with_capacity(window_size),
            threshold,
            check,
        }
    }

    /// Create a monitor that alerts when term size exceeds a threshold.
    pub fn term_size_bound(max_mean_size: f64, window: usize) -> Self {
        Self::new("term_size_bound", window, max_mean_size, WindowCheck::MeanAbove)
    }

    /// Create a monitor that alerts when term size is monotonically increasing.
    pub fn growing_term(window: usize) -> Self {
        Self::new("growing_term", window, 0.0, WindowCheck::MonotonicallyIncreasing)
    }

    /// Create a monitor that alerts when the term is stuck (not changing).
    pub fn stagnation_detector(window: usize) -> Self {
        Self::new("stagnation", window, 0.0, WindowCheck::Stagnant)
    }

    fn extract_metric(&self, event: &TraceEvent) -> f64 {
        event.term_size as f64
    }

    fn check_window(&self) -> Option<MonitorAlert> {
        if self.window.len() < self.window_size {
            return None; // Not enough data yet
        }

        match self.check {
            WindowCheck::MeanAbove => {
                let mean: f64 = self.window.iter().sum::<f64>() / self.window.len() as f64;
                if mean > self.threshold {
                    Some(MonitorAlert {
                        step: 0, // Will be filled by caller
                        monitor_name: self.name.clone(),
                        severity: AlertSeverity::Warning,
                        message: format!("Window mean {:.2} exceeds threshold {:.2}", mean, self.threshold),
                    })
                } else {
                    None
                }
            }
            WindowCheck::MeanBelow => {
                let mean: f64 = self.window.iter().sum::<f64>() / self.window.len() as f64;
                if mean < self.threshold {
                    Some(MonitorAlert {
                        step: 0,
                        monitor_name: self.name.clone(),
                        severity: AlertSeverity::Warning,
                        message: format!("Window mean {:.2} below threshold {:.2}", mean, self.threshold),
                    })
                } else {
                    None
                }
            }
            WindowCheck::VarianceAbove => {
                let mean: f64 = self.window.iter().sum::<f64>() / self.window.len() as f64;
                let variance: f64 = self.window.iter().map(|x| (x - mean).powi(2)).sum::<f64>()
                    / self.window.len() as f64;
                if variance > self.threshold {
                    Some(MonitorAlert {
                        step: 0,
                        monitor_name: self.name.clone(),
                        severity: AlertSeverity::Warning,
                        message: format!("Window variance {:.2} exceeds threshold {:.2}", variance, self.threshold),
                    })
                } else {
                    None
                }
            }
            WindowCheck::MonotonicallyIncreasing => {
                let increasing = self.window.iter().zip(self.window.iter().skip(1))
                    .all(|(a, b)| b >= a);
                if increasing {
                    Some(MonitorAlert {
                        step: 0,
                        monitor_name: self.name.clone(),
                        severity: AlertSeverity::Warning,
                        message: format!("Term size monotonically increasing over {} steps", self.window_size),
                    })
                } else {
                    None
                }
            }
            WindowCheck::Stagnant => {
                let first = self.window.front().copied().unwrap_or(0.0);
                let all_same = self.window.iter().all(|x| (*x - first).abs() < f64::EPSILON);
                if all_same {
                    Some(MonitorAlert {
                        step: 0,
                        monitor_name: self.name.clone(),
                        severity: AlertSeverity::Info,
                        message: format!("Term stagnant (size = {:.0}) for {} steps", first, self.window_size),
                    })
                } else {
                    None
                }
            }
        }
    }
}

impl StreamingMonitor for WindowedMonitor {
    fn name(&self) -> &str {
        &self.name
    }

    fn process(&mut self, event: &TraceEvent) -> Vec<MonitorAlert> {
        let metric = self.extract_metric(event);
        self.window.push_back(metric);
        if self.window.len() > self.window_size {
            self.window.pop_front();
        }

        if let Some(mut alert) = self.check_window() {
            alert.step = event.step;
            vec![alert]
        } else {
            vec![]
        }
    }

    fn finalize(&mut self) -> Vec<MonitorAlert> {
        vec![] // No finalization alerts for windowed monitors
    }

    fn reset(&mut self) {
        self.window.clear();
    }
}

/// Aggregate monitor: tracks running statistics (mean, variance, min, max)
/// using Welford's online algorithm.
///
/// Memory: O(1) regardless of trace length.
pub struct AggregateMonitor {
    name: String,
    count: u64,
    mean: f64,
    m2: f64,
    min: f64,
    max: f64,
    alert_threshold: Option<f64>,
}

impl AggregateMonitor {
    /// Create a new aggregate monitor.
    pub fn new(name: impl Into<String>) -> Self {
        Self {
            name: name.into(),
            count: 0,
            mean: 0.0,
            m2: 0.0,
            min: f64::INFINITY,
            max: f64::NEG_INFINITY,
            alert_threshold: None,
        }
    }

    /// Set an alert threshold: emit a warning if the running mean exceeds this value.
    pub fn with_threshold(mut self, threshold: f64) -> Self {
        self.alert_threshold = Some(threshold);
        self
    }

    /// Get the current variance (population variance).
    pub fn variance(&self) -> f64 {
        if self.count < 2 {
            0.0
        } else {
            self.m2 / self.count as f64
        }
    }

    /// Get the current standard deviation.
    pub fn std_dev(&self) -> f64 {
        self.variance().sqrt()
    }

    /// Get summary statistics.
    pub fn summary(&self) -> AggregateSummary {
        AggregateSummary {
            count: self.count,
            mean: self.mean,
            variance: self.variance(),
            min: self.min,
            max: self.max,
        }
    }
}

/// Summary statistics from an aggregate monitor.
#[derive(Debug, Clone, serde::Serialize, serde::Deserialize)]
pub struct AggregateSummary {
    pub count: u64,
    pub mean: f64,
    pub variance: f64,
    pub min: f64,
    pub max: f64,
}

impl StreamingMonitor for AggregateMonitor {
    fn name(&self) -> &str {
        &self.name
    }

    fn process(&mut self, event: &TraceEvent) -> Vec<MonitorAlert> {
        let x = event.term_size as f64;

        // Welford's online algorithm
        self.count += 1;
        let delta = x - self.mean;
        self.mean += delta / self.count as f64;
        let delta2 = x - self.mean;
        self.m2 += delta * delta2;

        self.min = self.min.min(x);
        self.max = self.max.max(x);

        // Check threshold
        if let Some(threshold) = self.alert_threshold {
            if self.mean > threshold && self.count >= 10 {
                return vec![MonitorAlert {
                    step: event.step,
                    monitor_name: self.name.clone(),
                    severity: AlertSeverity::Warning,
                    message: format!(
                        "Running mean {:.2} exceeds threshold {:.2} (n={}, σ={:.2})",
                        self.mean, threshold, self.count, self.std_dev()
                    ),
                }];
            }
        }

        vec![]
    }

    fn finalize(&mut self) -> Vec<MonitorAlert> {
        vec![MonitorAlert {
            step: self.count as usize,
            monitor_name: self.name.clone(),
            severity: AlertSeverity::Info,
            message: format!(
                "Final stats: mean={:.2}, σ={:.2}, min={:.0}, max={:.0}, n={}",
                self.mean, self.std_dev(), self.min, self.max, self.count
            ),
        }]
    }

    fn reset(&mut self) {
        self.count = 0;
        self.mean = 0.0;
        self.m2 = 0.0;
        self.min = f64::INFINITY;
        self.max = f64::NEG_INFINITY;
    }
}

/// Composite monitor: runs multiple monitors in parallel over the same trace.
///
/// Each monitor processes the same events independently and produces its own alerts.
pub struct CompositeMonitor {
    name: String,
    monitors: Vec<Box<dyn StreamingMonitor>>,
}

impl CompositeMonitor {
    /// Create a new composite monitor.
    pub fn new(name: impl Into<String>) -> Self {
        Self {
            name: name.into(),
            monitors: Vec::new(),
        }
    }

    /// Add a monitor to the composite.
    pub fn add(mut self, monitor: impl StreamingMonitor + 'static) -> Self {
        self.monitors.push(Box::new(monitor));
        self
    }
}

impl StreamingMonitor for CompositeMonitor {
    fn name(&self) -> &str {
        &self.name
    }

    fn process(&mut self, event: &TraceEvent) -> Vec<MonitorAlert> {
        let mut all_alerts = Vec::new();
        for monitor in &mut self.monitors {
            all_alerts.extend(monitor.process(event));
        }
        all_alerts
    }

    fn finalize(&mut self) -> Vec<MonitorAlert> {
        let mut all_alerts = Vec::new();
        for monitor in &mut self.monitors {
            all_alerts.extend(monitor.finalize());
        }
        all_alerts
    }

    fn reset(&mut self) {
        for monitor in &mut self.monitors {
            monitor.reset();
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn make_event(step: usize, size: usize) -> TraceEvent {
        TraceEvent {
            step,
            term_display: format!("term_{}", step),
            operation: "rewrite".into(),
            term_size: size,
            term_depth: 1,
        }
    }

    #[test]
    fn test_windowed_mean_above() {
        let mut monitor = WindowedMonitor::term_size_bound(10.0, 3);
        assert!(monitor.process(&make_event(0, 5)).is_empty());
        assert!(monitor.process(&make_event(1, 8)).is_empty());
        assert!(monitor.process(&make_event(2, 9)).is_empty()); // mean = 7.33
        let alerts = monitor.process(&make_event(3, 20)); // mean = 12.33
        assert_eq!(alerts.len(), 1);
        assert_eq!(alerts[0].severity, AlertSeverity::Warning);
    }

    #[test]
    fn test_aggregate_welford() {
        let mut monitor = AggregateMonitor::new("test");
        for i in 0..100 {
            monitor.process(&make_event(i, i + 1));
        }
        let summary = monitor.summary();
        assert_eq!(summary.count, 100);
        assert!((summary.mean - 50.5).abs() < 0.01);
        assert_eq!(summary.min, 1.0);
        assert_eq!(summary.max, 100.0);
    }

    #[test]
    fn test_composite_parallel() {
        let mut composite = CompositeMonitor::new("composite")
            .add(WindowedMonitor::term_size_bound(5.0, 2))
            .add(AggregateMonitor::new("agg"));

        let alerts = composite.process(&make_event(0, 10));
        assert!(alerts.is_empty()); // Windowed needs 2 events, aggregate has no threshold

        let alerts = composite.process(&make_event(1, 10));
        assert_eq!(alerts.len(), 1); // Windowed fires (mean=10 > 5)
    }

    #[test]
    fn test_stagnation_detection() {
        let mut monitor = WindowedMonitor::stagnation_detector(3);
        monitor.process(&make_event(0, 5));
        monitor.process(&make_event(1, 5));
        let alerts = monitor.process(&make_event(2, 5));
        assert_eq!(alerts.len(), 1);
        assert_eq!(alerts[0].severity, AlertSeverity::Info);
    }
}
