//! Simulation runner for property-based testing of MeTTaIL languages.
//!
//! The `SimulationRunner` wraps proptest's `TestRunner` to orchestrate
//! simulation campaigns: generating random terms via strategies, running
//! them through a language's parse/rewrite pipeline, checking invariants,
//! tracking morphology, and collecting results.
//!
//! ## Key Design Decisions
//!
//! - **Fail-slow**: campaigns collect ALL failures rather than stopping at
//!   the first. This is essential for understanding the failure landscape.
//! - **Deterministic**: seeds are recorded per test case so failures can
//!   be reproduced exactly.
//! - **Report-aware execution**: the runner consumes `RuntimeBackendReport`.
//!   Ascent-shaped reference reports are walked with iterative BFS, complete
//!   Dovetail reports are accepted as terminal rewrite evidence, and Rho
//!   observations remain terminal runtime evidence.

use crate::invariant::{Invariant, InvariantState};
use crate::morphology::{MorphologyTracker, TermMetrics};
use crate::results::{CampaignResults, RuleCoverage, SimulationFailure};
use crate::step::SimOperation;
use crate::temporal::{self, LtlCheckResult};
use crate::trace::{ExecutionTrace, TraceEntry, TraceOutcome};

use mettail_runtime::{Language, RuntimeBackendOutput, RuntimeDovetailRunReport};
use proptest::strategy::{Strategy, ValueTree};
use proptest::test_runner::TestRunner;
use std::io::{BufRead, Write};
use std::path::{Path, PathBuf};

/// Output format for traces during a simulation run.
#[derive(Debug, Clone)]
pub enum TraceOutputFormat {
    /// No trace output.
    None,
    /// Write JSONL traces to the specified path (one file per case, or appended).
    Jsonl { path: PathBuf },
    /// Collect structured traces in memory (available via results).
    Structured,
}

/// Configuration for a simulation run.
pub struct SimulationConfig {
    /// Maximum number of rewrite steps before declaring non-termination.
    pub max_steps: usize,
    /// Maximum allowed term depth (used by morphology tracking).
    pub max_term_depth: u32,
    /// Number of proptest cases to generate per campaign.
    pub proptest_cases: u32,
    /// Optional fixed seed for reproducibility (32 bytes).
    pub seed: Option<[u8; 32]>,
    /// Invariants to check at each step.
    pub invariants: Vec<Box<dyn Invariant>>,
    /// LTL property formulas checked post-hoc against each run's execution
    /// trace.
    ///
    /// When non-empty, [`SimulationRunner::run_to_normal_form`] evaluates every
    /// formula against the assembled trace via
    /// [`crate::temporal::check_trace_ltl`] (over
    /// [`crate::temporal::trace_to_ltl_steps`], using
    /// [`crate::temporal::default_propositions`]) **after** the trace is built —
    /// never inside the rewrite loop, so determinism is preserved. The first
    /// `Violated` formula surfaces as a [`TraceOutcome::LtlViolation`] failure
    /// (and is mirrored into `CampaignResults::ltl_violations`). Defaults to
    /// empty, in which case no LTL check runs and run outcomes are unchanged.
    pub ltl_properties: Vec<String>,
    /// Whether to track term morphology metrics.
    pub track_morphology: bool,
    /// Trace output configuration.
    pub trace_output: TraceOutputFormat,
    /// Path to a `.regressions` file for seed persistence.
    ///
    /// When set, `run_campaign` will:
    /// 1. Load previously-failing seeds and re-run them first.
    /// 2. Remove seeds from the file if they now pass (bug fixed).
    /// 3. Append newly-discovered failing seeds.
    pub regression_path: Option<PathBuf>,
    /// Print one summary line per test case to stderr.
    ///
    /// Mirrors the `--verbose` (`-v`) flag on the generated
    /// `simulate_<lang>` binaries. Output format is one line per
    /// case: `[case_NNNN] pass/fail/panic  steps=N  input="..."  [error/msg]`.
    /// The input string is truncated to 120 chars so pathologically
    /// long generated terms don't flood the terminal.
    pub verbose: bool,
}

impl Default for SimulationConfig {
    fn default() -> Self {
        Self {
            max_steps: 1000,
            max_term_depth: 50,
            proptest_cases: 100,
            seed: None,
            invariants: Vec::new(),
            ltl_properties: Vec::new(),
            track_morphology: true,
            trace_output: TraceOutputFormat::None,
            regression_path: None,
            verbose: false,
        }
    }
}

// =============================================================================
// Regression seed persistence
// =============================================================================

/// Load regression seeds from a `.regressions` file.
///
/// Each line in the file is a hex-encoded 32-byte seed (64 hex characters).
/// Blank lines and lines starting with `#` are ignored.
/// Returns an empty vector if the file does not exist.
pub fn load_regression_seeds(path: &Path) -> Vec<[u8; 32]> {
    let file = match std::fs::File::open(path) {
        Ok(f) => f,
        Err(_) => return Vec::new(),
    };
    let reader = std::io::BufReader::new(file);
    let mut seeds = Vec::new();
    for line in reader.lines() {
        let line = match line {
            Ok(l) => l,
            Err(_) => continue,
        };
        let trimmed = line.trim();
        if trimmed.is_empty() || trimmed.starts_with('#') {
            continue;
        }
        if let Some(seed) = hex_to_seed(trimmed) {
            seeds.push(seed);
        }
    }
    seeds
}

/// Append a regression seed to a `.regressions` file.
///
/// Creates the file if it does not exist. Does not add duplicates.
pub fn save_regression_seed(path: &Path, seed: &[u8; 32]) {
    // Check if seed already exists in the file to avoid duplicates.
    let existing = load_regression_seeds(path);
    if existing.contains(seed) {
        return;
    }

    let mut file = match std::fs::OpenOptions::new()
        .create(true)
        .append(true)
        .open(path)
    {
        Ok(f) => f,
        Err(e) => {
            eprintln!("Warning: failed to save regression seed to {}: {}", path.display(), e);
            return;
        },
    };

    let hex = seed_to_hex(seed);
    if let Err(e) = writeln!(file, "{}", hex) {
        eprintln!("Warning: failed to write regression seed to {}: {}", path.display(), e);
    }
}

/// Remove a passing regression seed from a `.regressions` file.
///
/// Rewrites the file without the specified seed. If the seed is not found,
/// the file is left unchanged. If the file becomes empty, it is removed.
pub fn remove_regression_seed(path: &Path, seed: &[u8; 32]) {
    let existing = load_regression_seeds(path);
    let filtered: Vec<[u8; 32]> = existing.into_iter().filter(|s| s != seed).collect();

    if filtered.is_empty() {
        // Remove the file if no seeds remain.
        let _ = std::fs::remove_file(path);
        return;
    }

    let mut file = match std::fs::File::create(path) {
        Ok(f) => f,
        Err(e) => {
            eprintln!("Warning: failed to rewrite regression file {}: {}", path.display(), e);
            return;
        },
    };

    for s in &filtered {
        let hex = seed_to_hex(s);
        if let Err(e) = writeln!(file, "{}", hex) {
            eprintln!("Warning: failed to write seed to {}: {}", path.display(), e);
            return;
        }
    }
}

/// Convert a 32-byte seed to a 64-character hex string.
pub fn seed_to_hex(seed: &[u8; 32]) -> String {
    let mut hex = String::with_capacity(64);
    for byte in seed {
        hex.push_str(&format!("{:02x}", byte));
    }
    hex
}

/// Parse a 64-character hex string into a 32-byte seed.
/// Returns `None` if the string is not valid hex or wrong length.
fn hex_to_seed(hex: &str) -> Option<[u8; 32]> {
    if hex.len() != 64 {
        return None;
    }
    let mut seed = [0u8; 32];
    for (i, chunk) in hex.as_bytes().chunks(2).enumerate() {
        let high = hex_digit(chunk[0])?;
        let low = hex_digit(chunk[1])?;
        seed[i] = (high << 4) | low;
    }
    Some(seed)
}

/// Convert a single ASCII hex digit to its 4-bit value.
fn hex_digit(b: u8) -> Option<u8> {
    match b {
        b'0'..=b'9' => Some(b - b'0'),
        b'a'..=b'f' => Some(b - b'a' + 10),
        b'A'..=b'F' => Some(b - b'A' + 10),
        _ => None,
    }
}

fn dovetail_report_summary(report: &RuntimeDovetailRunReport) -> String {
    let roots = report
        .root_ordinals
        .iter()
        .filter_map(|ordinal| report.terms.get(*ordinal))
        .map(|term| term.op_display.as_str())
        .collect::<Vec<_>>()
        .join(", ");
    format!(
        "DovetailRunReport(completeness={}, roots=[{}], terms={}, edges={}, rule_firings={})",
        report.completeness,
        roots,
        report.terms.len(),
        report.derivation_edges.len(),
        report
            .rule_firings
            .iter()
            .map(|firing| firing.count)
            .sum::<usize>()
    )
}

fn append_dovetail_rule_firing_steps(
    steps: &mut Vec<TraceEntry>,
    next_step_index: &mut usize,
    summary: &str,
    report: &RuntimeDovetailRunReport,
) {
    for firing in &report.rule_firings {
        let operation = SimOperation::Rewrite { rule_name: firing.label.clone() }.label();
        for _ in 0..firing.count {
            steps.push(TraceEntry {
                step_index: *next_step_index,
                term_display: summary.to_string(),
                operation: operation.clone(),
                metrics: None,
            });
            *next_step_index += 1;
        }
    }
}

/// Extract the funded normal-form term display from a Dovetail report, if the input reduced to a
/// literal value. Post-P6 the Dovetail backend reduces native folds in-engine (e.g. `AddInt(1,2)`
/// is merged into the same e-class as `NumLit(3)`), so the normal form of an input root is the
/// literal term sharing the root's `class_id`. Returns the literal's rendered value (e.g. "3"),
/// or `None` when no root reduced to a literal (free variables, unlowerable folds) — the caller
/// then keeps the raw `RuntimeReport` outcome.
fn dovetail_extract_normal_form(report: &RuntimeDovetailRunReport) -> Option<String> {
    for &ordinal in &report.root_ordinals {
        let class = report.terms.get(ordinal)?.class_id;
        if let Some(value) = report
            .terms
            .iter()
            .filter(|t| t.class_id == class)
            .find_map(|t| literal_display_value(&t.op_display))
        {
            return Some(value);
        }
    }
    None
}

/// If `op_display` is a literal-constructor term — `<Lang>::<Cat>::<Ctor>Lit(<payload>)`, e.g.
/// `Calculator::Int::NumLit(3)` — return the rendered payload (`"3"`). For the integer literals
/// the simulation tests assert, the `{:?}` payload equals the category's own Display of the
/// literal (`NumLit(3)` displays "3"). Non-literal ops (`…::AddInt`, no payload) return `None`.
fn literal_display_value(op_display: &str) -> Option<String> {
    let open = op_display.find('(')?;
    let ctor = op_display[..open].rsplit("::").next()?;
    if !ctor.ends_with("Lit") {
        return None;
    }
    let close = op_display.rfind(')')?;
    if close <= open + 1 {
        return None;
    }
    Some(op_display[open + 1..close].to_string())
}

fn has_normal_form_reachable_invariant(config: &SimulationConfig) -> bool {
    config
        .invariants
        .iter()
        .any(|invariant| invariant.name() == "NormalFormReachable")
}

fn dovetail_report_satisfies_normal_form_reachable(report: &RuntimeDovetailRunReport) -> bool {
    report.is_complete() && !report.root_ordinals.is_empty()
}

fn dovetail_normal_form_reachability_message(
    backend: impl std::fmt::Display,
    report: &RuntimeDovetailRunReport,
) -> String {
    if !report.is_complete() {
        format!(
            "Normal form not proven: {} backend returned a {} Dovetail report, which is non-exhaustive",
            backend, report.completeness
        )
    } else {
        format!(
            "Normal form not reached: {} backend returned a complete Dovetail report with no extracted roots",
            backend
        )
    }
}

/// Extract a human-readable message from a panic payload.
fn panic_payload_to_string(payload: Box<dyn std::any::Any + Send>) -> String {
    if let Some(s) = payload.downcast_ref::<&str>() {
        s.to_string()
    } else if let Some(s) = payload.downcast_ref::<String>() {
        s.clone()
    } else {
        "unknown panic".to_string()
    }
}

/// The simulation runner: orchestrates parse/rewrite/check cycles.
pub struct SimulationRunner<'a> {
    language: &'a dyn Language,
    config: SimulationConfig,
}

impl<'a> SimulationRunner<'a> {
    /// Create a new simulation runner for the given language and configuration.
    pub fn new(language: &'a dyn Language, config: SimulationConfig) -> Self {
        Self { language, config }
    }

    /// Run a single simulation: parse a term, rewrite to normal form, check invariants.
    ///
    /// Returns an `ExecutionTrace` on success, or a `SimulationFailure` on error.
    pub fn run_to_normal_form(&self, input: &str) -> Result<ExecutionTrace, SimulationFailure> {
        let seed_str = "deterministic".to_string();
        let language_name = self.language.name().to_string();

        let mut steps: Vec<TraceEntry> = Vec::new();
        let mut morphology_tracker = if self.config.track_morphology {
            Some(MorphologyTracker::new())
        } else {
            None
        };
        let mut coverage = RuleCoverage::new();
        let mut step_index: usize = 0;

        // Step 1: Parse.
        mettail_runtime::clear_var_cache();
        let term = match self.language.parse_term(input) {
            Ok(t) => t,
            Err(e) => {
                let trace = ExecutionTrace {
                    seed: seed_str.clone(),
                    language: language_name.clone(),
                    steps,
                    outcome: TraceOutcome::Error { message: format!("Parse error: {}", e) },
                    morphology: morphology_tracker.as_ref().map(|t| t.summary()),
                };
                return Err(SimulationFailure {
                    seed: seed_str,
                    input: input.to_string(),
                    trace,
                    error: format!("Parse error: {}", e),
                });
            },
        };

        let term_display = format!("{}", term);
        let metrics = TermMetrics::from_display(&term_display);
        if let Some(ref mut tracker) = morphology_tracker {
            tracker.record(metrics.clone());
        }

        steps.push(TraceEntry {
            step_index,
            term_display: term_display.clone(),
            operation: SimOperation::Parse { input: input.to_string() }.label(),
            metrics: Some(metrics.clone()),
        });

        // Check invariants after parse.
        if let Err(failure) = self.check_invariants_at_step(
            &term_display,
            step_index,
            &metrics,
            &seed_str,
            input,
            &steps,
            &morphology_tracker,
        ) {
            return Err(failure);
        }

        step_index += 1;

        // Step 2: Run the selected backend (rewrite to saturation).
        mettail_runtime::clear_var_cache();
        let backend = match self.language.selected_default_runtime_backend() {
            Some(backend) => backend,
            None => {
                let message = format!(
                    "language {} does not advertise a default runtime backend",
                    self.language.name()
                );
                let trace = ExecutionTrace {
                    seed: seed_str.clone(),
                    language: language_name.clone(),
                    steps,
                    outcome: TraceOutcome::Error { message: message.clone() },
                    morphology: morphology_tracker.as_ref().map(|t| t.summary()),
                };
                return Err(SimulationFailure {
                    seed: seed_str,
                    input: input.to_string(),
                    trace,
                    error: message,
                });
            },
        };
        let report = match self.language.run_default_backend_report(term.as_ref()) {
            Ok(r) => r,
            Err(e) => {
                let trace = ExecutionTrace {
                    seed: seed_str.clone(),
                    language: language_name.clone(),
                    steps,
                    outcome: TraceOutcome::Error {
                        message: format!("{} backend error: {}", backend, e),
                    },
                    morphology: morphology_tracker.as_ref().map(|t| t.summary()),
                };
                return Err(SimulationFailure {
                    seed: seed_str,
                    input: input.to_string(),
                    trace,
                    error: format!("{} backend error: {}", backend, e),
                });
            },
        };
        let backend = report.backend();
        let artifact = report.artifact();
        let results = match report.into_output() {
            RuntimeBackendOutput::Ascent(results) => results,
            RuntimeBackendOutput::Observations(observations) => {
                let summary = observations
                    .iter()
                    .map(|observation| {
                        let values = observation
                            .values
                            .iter()
                            .map(|value| format!("{}", value))
                            .collect::<Vec<_>>()
                            .join(", ");
                        format!("{}=[{}]", observation.channel, values)
                    })
                    .collect::<Vec<_>>()
                    .join("; ");
                let observed_values = observations
                    .iter()
                    .map(|observation| observation.observed_count())
                    .sum::<usize>();
                let operation = format!("runtime:{}:{}", backend, artifact);
                let metrics = TermMetrics::from_display(&summary);
                if let Some(ref mut tracker) = morphology_tracker {
                    tracker.record(metrics.clone());
                }
                steps.push(TraceEntry {
                    step_index,
                    term_display: summary.clone(),
                    operation,
                    metrics: Some(metrics),
                });

                let outcome = TraceOutcome::RuntimeObservations {
                    backend: backend.to_string(),
                    artifact: artifact.to_string(),
                    channels: observations.len(),
                    values: observed_values,
                    summary,
                };
                let morphology = morphology_tracker.as_ref().map(|t| t.summary());

                if has_normal_form_reachable_invariant(&self.config) {
                    let message = format!(
                        "Normal form not reached: {} backend returned runtime observations, not rewrite-result evidence",
                        backend
                    );
                    let trace = ExecutionTrace {
                        seed: seed_str.clone(),
                        language: language_name,
                        steps,
                        outcome: TraceOutcome::InvariantViolation {
                            step: step_index,
                            invariant: "NormalFormReachable".to_string(),
                            message: message.clone(),
                        },
                        morphology,
                    };
                    return Err(SimulationFailure {
                        seed: seed_str,
                        input: input.to_string(),
                        trace,
                        error: message,
                    });
                }

                let trace = ExecutionTrace {
                    seed: seed_str,
                    language: language_name,
                    steps,
                    outcome,
                    morphology,
                };

                if let TraceOutputFormat::Jsonl { ref path } = self.config.trace_output {
                    if let Err(e) = crate::trace::write_trace_jsonl(&trace, path) {
                        eprintln!("Warning: failed to write JSONL trace: {}", e);
                    }
                }

                return self.finalize_with_ltl(trace, input);
            },
            RuntimeBackendOutput::Dovetail(dovetail_report) => {
                let summary = dovetail_report_summary(&dovetail_report);
                let operation = format!("runtime:{}:{}", backend, artifact);
                let metrics = TermMetrics::from_display(&summary);
                if let Some(ref mut tracker) = morphology_tracker {
                    tracker.record(metrics.clone());
                }
                steps.push(TraceEntry {
                    step_index,
                    term_display: summary.clone(),
                    operation,
                    metrics: Some(metrics),
                });
                let mut next_step_index = step_index + 1;
                append_dovetail_rule_firing_steps(
                    &mut steps,
                    &mut next_step_index,
                    &summary,
                    &dovetail_report,
                );

                // Present the reduced normal form when the input folded to a literal (post-P6
                // Dovetail reduces native folds in-engine); otherwise keep the raw report.
                let outcome = match dovetail_extract_normal_form(&dovetail_report) {
                    Some(term) => TraceOutcome::NormalForm {
                        term,
                        steps: next_step_index.saturating_sub(1),
                    },
                    None => TraceOutcome::RuntimeReport {
                        backend: backend.to_string(),
                        artifact: artifact.to_string(),
                        summary,
                    },
                };
                let morphology = morphology_tracker.as_ref().map(|t| t.summary());

                if has_normal_form_reachable_invariant(&self.config)
                    && !dovetail_report_satisfies_normal_form_reachable(&dovetail_report)
                {
                    let message =
                        dovetail_normal_form_reachability_message(backend, &dovetail_report);
                    let trace = ExecutionTrace {
                        seed: seed_str.clone(),
                        language: language_name,
                        steps,
                        outcome: TraceOutcome::InvariantViolation {
                            step: step_index,
                            invariant: "NormalFormReachable".to_string(),
                            message: message.clone(),
                        },
                        morphology,
                    };
                    return Err(SimulationFailure {
                        seed: seed_str,
                        input: input.to_string(),
                        trace,
                        error: message,
                    });
                }

                let trace = ExecutionTrace {
                    seed: seed_str,
                    language: language_name,
                    steps,
                    outcome,
                    morphology,
                };

                if let TraceOutputFormat::Jsonl { ref path } = self.config.trace_output {
                    if let Err(e) = crate::trace::write_trace_jsonl(&trace, path) {
                        eprintln!("Warning: failed to write JSONL trace: {}", e);
                    }
                }

                return self.finalize_with_ltl(trace, input);
            },
            _ => {
                let trace = ExecutionTrace {
                    seed: seed_str.clone(),
                    language: language_name.clone(),
                    steps,
                    outcome: TraceOutcome::Error {
                        message: format!("{} backend returned unsupported report shape", backend),
                    },
                    morphology: morphology_tracker.as_ref().map(|t| t.summary()),
                };
                return Err(SimulationFailure {
                    seed: seed_str,
                    input: input.to_string(),
                    trace,
                    error: format!("{} backend returned unsupported report shape", backend),
                });
            },
        };

        // Step 3: Walk the rewrite graph iteratively (trampoline-style BFS)
        // to build the trace from initial term to normal form.
        //
        // Phase F.12.A (2026-05-20): MULTI-SOURCE BFS. When the parser
        // returns an `Ambiguous` wrapper, its `term_id()` hashes the
        // wrapper variant — that hash is structurally absent from
        // `results.all_terms` because `run_ascent_typed` enumerates the
        // wrapper's `all_alts()` and only pushes single-category alts
        // into `TermInfo`. A single-source BFS from the wrapper's id
        // would find no rewrites_from(wrapper_id), drain the queue,
        // and fall through to a non-deterministic `nfs.first()`.
        //
        // Fix: seed the BFS from EACH alt via the exact `Term::rewrite_seeds()`
        // trait method. For unambiguous inputs the default trait impl returns
        // one legacy seed,
        // preserving the prior single-source behavior. For Ambiguous
        // wrappers, each alt contributes its own search frontier; we
        // pick the canonically-shortest NF across all reachable NFs.
        //
        // Canonical NF picker (lex order, lowest wins):
        //   1. `display.len()` — shorter wins ("0" beats "-0").
        //   2. `display` itself — lex-smallest as tie-break.
        //   3. seed index — declaration-order tie-break (deterministic).
        let seeds = term.rewrite_seeds();

        #[derive(Clone, Debug, Eq, Hash, PartialEq)]
        enum SimReachKey {
            Exact(Vec<u8>),
            Legacy(u64),
        }

        let seed_key = |seed: &mettail_runtime::RewriteSeed| {
            seed.exact_key
                .clone()
                .map(SimReachKey::Exact)
                .unwrap_or(SimReachKey::Legacy(seed.term_id))
        };
        let term_key = |info: &mettail_runtime::TermInfo| {
            info.exact_key
                .clone()
                .map(SimReachKey::Exact)
                .unwrap_or(SimReachKey::Legacy(info.term_id))
        };
        let rewrite_from_key = |rw: &mettail_runtime::Rewrite| {
            rw.from_key
                .clone()
                .map(SimReachKey::Exact)
                .unwrap_or(SimReachKey::Legacy(rw.from_id))
        };
        let rewrite_to_key = |rw: &mettail_runtime::Rewrite| {
            rw.to_key
                .clone()
                .map(SimReachKey::Exact)
                .unwrap_or(SimReachKey::Legacy(rw.to_id))
        };

        // Per-seed BFS, collecting (seed_idx, nf_term_id, path).
        let mut candidates: Vec<(usize, u64, Vec<u64>)> = Vec::new();
        for (seed_idx, seed) in seeds.iter().enumerate() {
            let mut visited = std::collections::HashSet::new();
            let mut queue = std::collections::VecDeque::new();
            let start_key = seed_key(seed);
            queue.push_back((start_key.clone(), Vec::<u64>::new()));
            visited.insert(start_key);
            while let Some((current_key, path)) = queue.pop_front() {
                let info = results
                    .all_terms
                    .iter()
                    .find(|t| term_key(t) == current_key);
                let current_id = info.map(|i| i.term_id).unwrap_or(seed.term_id);
                if info.is_some_and(|i| i.is_normal_form) {
                    let mut full_path = path;
                    full_path.push(current_id);
                    candidates.push((seed_idx, current_id, full_path));
                    break;
                }
                if path.len() >= self.config.max_steps {
                    continue;
                }
                for rw in results
                    .rewrites
                    .iter()
                    .filter(|rw| rewrite_from_key(rw) == current_key)
                {
                    let to_key = rewrite_to_key(rw);
                    if visited.insert(to_key.clone()) {
                        let mut new_path = path.clone();
                        new_path.push(current_id);
                        queue.push_back((to_key, new_path));
                    }
                }
            }
        }

        // Record all rewrites for coverage (unchanged: every rewrite
        // counts, regardless of which seed's path it lies on).
        for rw in &results.rewrites {
            if let Some(ref name) = rw.rule_name {
                coverage.record_rule(name);
            }
        }

        // Canonical NF picker across all seed candidates.
        let chosen = candidates.iter().min_by(|a, b| {
            let info_a = results.all_terms.iter().find(|t| t.term_id == a.1);
            let info_b = results.all_terms.iter().find(|t| t.term_id == b.1);
            match (info_a, info_b) {
                (Some(ia), Some(ib)) => {
                    let ka = (ia.display.len(), ia.display.as_str(), a.0);
                    let kb = (ib.display.len(), ib.display.as_str(), b.0);
                    ka.cmp(&kb)
                },
                _ => a.0.cmp(&b.0),
            }
        });

        let (path_to_normal_form, normal_form_id): (Option<Vec<u64>>, Option<u64>) =
            if let Some(&(_seed_idx, nf_id, ref path)) = chosen {
                (Some(path.clone()), Some(nf_id))
            } else {
                (None, None)
            };

        // Build trace entries for the path.
        if let Some(ref path) = path_to_normal_form {
            // Skip the first element (already recorded as parse step).
            for (i, &tid) in path.iter().enumerate().skip(1) {
                if let Some(info) = results.all_terms.iter().find(|t| t.term_id == tid) {
                    // Find the rewrite that brought us here.
                    let prev_id = path[i - 1];
                    let rule_name = results
                        .rewrites
                        .iter()
                        .find(|r| r.from_id == prev_id && r.to_id == tid)
                        .and_then(|r| r.rule_name.clone());

                    let metrics = TermMetrics::from_display(&info.display);
                    if let Some(ref mut tracker) = morphology_tracker {
                        tracker.record(metrics.clone());
                    }

                    let operation = SimOperation::Rewrite { rule_name };

                    // Check invariants.
                    if let Err(failure) = self.check_invariants_at_step(
                        &info.display,
                        step_index,
                        &metrics,
                        &seed_str,
                        input,
                        &steps,
                        &morphology_tracker,
                    ) {
                        return Err(failure);
                    }

                    steps.push(TraceEntry {
                        step_index,
                        term_display: info.display.clone(),
                        operation: operation.label(),
                        metrics: Some(metrics),
                    });
                    step_index += 1;
                }
            }
        }

        // Determine outcome.
        let outcome = if let Some(nf_id) = normal_form_id {
            let nf_display = results
                .all_terms
                .iter()
                .find(|t| t.term_id == nf_id)
                .map(|t| t.display.clone())
                .unwrap_or_else(|| "?".to_string());
            TraceOutcome::NormalForm { term: nf_display, steps: step_index }
        } else if results.all_terms.len() > self.config.max_steps {
            let last_display = steps
                .last()
                .map(|s| s.term_display.clone())
                .unwrap_or_default();
            TraceOutcome::StepLimitReached { final_term: last_display }
        } else {
            // No normal form found but didn't hit step limit.
            // Check if there are any normal forms at all.
            let mut nfs = results.normal_forms_iter();
            if let Some(nf) = nfs.next() {
                // There is a normal form but we couldn't find a path to it.
                TraceOutcome::NormalForm {
                    term: nf.display.clone(),
                    steps: step_index,
                }
            } else if !results.all_terms.is_empty() {
                TraceOutcome::StepLimitReached {
                    final_term: steps
                        .last()
                        .map(|s| s.term_display.clone())
                        .unwrap_or_default(),
                }
            } else {
                // Truly empty results (identity term?).
                TraceOutcome::NormalForm { term: term_display, steps: step_index }
            }
        };

        // Check NormalFormReachable invariants by convention:
        // Any invariant named "NormalFormReachable" is checked at completion
        // by verifying whether a normal form was reached within the step limit.
        let reached_nf = matches!(outcome, TraceOutcome::NormalForm { .. });
        if !reached_nf {
            for inv in &self.config.invariants {
                if inv.name() == "NormalFormReachable" {
                    let msg = format!(
                        "Normal form not reached after {} steps (max_steps: {})",
                        step_index, self.config.max_steps,
                    );
                    let trace = ExecutionTrace {
                        seed: seed_str.clone(),
                        language: language_name.clone(),
                        steps: steps.clone(),
                        outcome: TraceOutcome::InvariantViolation {
                            step: step_index,
                            invariant: "NormalFormReachable".to_string(),
                            message: msg.clone(),
                        },
                        morphology: morphology_tracker.as_ref().map(|t| t.summary()),
                    };
                    return Err(SimulationFailure {
                        seed: seed_str,
                        input: input.to_string(),
                        trace,
                        error: msg,
                    });
                }
            }
        }

        let morphology_summary = morphology_tracker.as_ref().map(|t| t.summary());

        let trace = ExecutionTrace {
            seed: seed_str,
            language: language_name,
            steps,
            outcome,
            morphology: morphology_summary,
        };

        // Write JSONL if configured.
        if let TraceOutputFormat::Jsonl { ref path } = self.config.trace_output {
            if let Err(e) = crate::trace::write_trace_jsonl(&trace, path) {
                eprintln!("Warning: failed to write JSONL trace: {}", e);
            }
        }

        self.finalize_with_ltl(trace, input)
    }

    /// Post-hoc LTL temporal-property checking over a fully-built trace.
    ///
    /// This is the surface half of the OSLF Phase 5 temporal wire: after a
    /// trace has been assembled (and any JSONL written), the configured
    /// `ltl_properties` are checked against it via
    /// [`temporal::check_trace_ltl`] over the adaptor
    /// [`temporal::trace_to_ltl_steps`], using [`temporal::default_propositions`].
    ///
    /// ## Determinism
    ///
    /// The check runs **strictly post-trace** — the trace (and therefore the
    /// rewrite sequence and every recorded outcome) is already final and is
    /// never re-derived here. No rewrite-loop state is touched, so enabling
    /// `ltl_properties` cannot perturb the deterministic reduction.
    ///
    /// ## Inert-by-default invariant
    ///
    /// When `ltl_properties` is empty (the default), this returns the trace
    /// **unchanged** with no work performed, so the default campaign outcome
    /// is byte-identical to the pre-wire behavior. Only a non-empty
    /// `ltl_properties` triggers evaluation; the first `Violated` formula is
    /// surfaced as a [`TraceOutcome::LtlViolation`] failure (mirroring the
    /// `InvariantViolation` failure path). `ParseError` and `Satisfied`
    /// results do not fail the run (a malformed user formula must not
    /// masquerade as a property violation).
    fn finalize_with_ltl(
        &self,
        trace: ExecutionTrace,
        input: &str,
    ) -> Result<ExecutionTrace, SimulationFailure> {
        if self.config.ltl_properties.is_empty() {
            return Ok(trace);
        }

        let steps = temporal::trace_to_ltl_steps(&trace);
        let propositions = temporal::default_propositions();
        for formula in &self.config.ltl_properties {
            if let LtlCheckResult::Violated { step, message } =
                temporal::check_trace_ltl(&steps, formula, &propositions)
            {
                let violation = ExecutionTrace {
                    seed: trace.seed.clone(),
                    language: trace.language.clone(),
                    steps: trace.steps.clone(),
                    outcome: TraceOutcome::LtlViolation {
                        step,
                        formula: formula.clone(),
                        message: message.clone(),
                    },
                    morphology: trace.morphology.clone(),
                };
                return Err(SimulationFailure {
                    seed: trace.seed.clone(),
                    input: input.to_string(),
                    trace: violation,
                    error: format!("LTL property '{}' violated: {}", formula, message),
                });
            }
        }

        Ok(trace)
    }

    /// Run a campaign: generate random terms via a strategy, simulate each,
    /// collect ALL results (does not stop at first failure).
    ///
    /// Uses proptest's `TestRunner` for generation and shrinking. Each generated
    /// input string is run through `run_to_normal_form`. Failures are collected
    /// with their minimal reproducers.
    ///
    /// When `config.regression_path` is set, the campaign will:
    /// 1. Load previously-failing seeds from the regression file and re-run them.
    /// 2. Remove seeds that now pass (the bug was fixed).
    /// 3. Keep seeds that still fail and include them in the results.
    /// 4. After random exploration, append newly-discovered failing seeds.
    pub fn run_campaign<S: Strategy<Value = String>>(
        &mut self,
        input_strategy: S,
    ) -> CampaignResults {
        let mut results = CampaignResults::new();
        let mut aggregate_tracker = if self.config.track_morphology {
            Some(MorphologyTracker::new())
        } else {
            None
        };

        // Phase 0: Regression seed replay.
        // Load previously-failing seeds, re-run them deterministically,
        // and update the regression file.
        if let Some(ref regression_path) = self.config.regression_path.clone() {
            let regression_seeds = load_regression_seeds(regression_path);
            if !regression_seeds.is_empty() {
                eprintln!(
                    "  Replaying {} regression seed(s) from {}",
                    regression_seeds.len(),
                    regression_path.display()
                );
            }
            for reg_seed in &regression_seeds {
                // Build a deterministic runner with this seed.
                let reg_config = proptest::test_runner::Config { cases: 1, ..Default::default() };
                let mut reg_runner = TestRunner::new_with_rng(
                    reg_config,
                    proptest::test_runner::TestRng::from_seed(
                        proptest::test_runner::RngAlgorithm::ChaCha,
                        reg_seed,
                    ),
                );

                // Generate a single value from the strategy with this seed.
                let value_tree = match input_strategy.new_tree(&mut reg_runner) {
                    Ok(tree) => tree,
                    Err(_) => {
                        // If we can't generate, the seed is stale; remove it.
                        remove_regression_seed(regression_path, reg_seed);
                        continue;
                    },
                };
                let input = value_tree.current();
                let seed_hex = seed_to_hex(reg_seed);

                match std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                    self.run_to_normal_form(&input)
                })) {
                    Ok(Ok(_trace)) => {
                        // Bug fixed: this regression seed now passes.
                        remove_regression_seed(regression_path, reg_seed);
                        results.record_pass();
                        eprintln!(
                            "    Regression seed {} now passes (removed from file)",
                            &seed_hex[..16]
                        );
                    },
                    Ok(Err(failure)) => {
                        // Still fails: keep in file, add to results.
                        results.record_failure(failure);
                        eprintln!("    Regression seed {} still fails", &seed_hex[..16]);
                    },
                    Err(panic_payload) => {
                        // Evaluation panicked (e.g., arithmetic overflow).
                        // Record as failure, keep in regression file.
                        let msg = panic_payload_to_string(panic_payload);
                        results.record_failure(crate::results::SimulationFailure {
                            seed: seed_hex.clone(),
                            input: input.clone(),
                            trace: crate::trace::ExecutionTrace {
                                seed: seed_hex.clone(),
                                language: self.language.name().to_string(),
                                steps: vec![],
                                outcome: crate::trace::TraceOutcome::Error {
                                    message: format!("evaluation panicked: {}", msg),
                                },
                                morphology: None,
                            },
                            error: format!("panic during evaluation: {}", msg),
                        });
                        eprintln!("    Regression seed {} panicked: {}", &seed_hex[..16], msg);
                    },
                }
            }
        }

        // Phase 1: Random exploration.
        // Build proptest config.
        let proptest_config = proptest::test_runner::Config {
            cases: self.config.proptest_cases,
            ..Default::default()
        };

        let mut runner = if let Some(seed) = self.config.seed {
            TestRunner::new_with_rng(
                proptest_config,
                proptest::test_runner::TestRng::from_seed(
                    proptest::test_runner::RngAlgorithm::ChaCha,
                    &seed,
                ),
            )
        } else {
            TestRunner::new(proptest_config)
        };

        // Run each test case. We iterate manually rather than using
        // runner.run() because we want to continue on failure.
        let mut case_index: u32 = 0;
        while case_index < self.config.proptest_cases {
            // Generate a value tree from the strategy.
            let value_tree = match input_strategy.new_tree(&mut runner) {
                Ok(tree) => tree,
                Err(_) => {
                    // Strategy exhausted or generation failure; skip.
                    case_index += 1;
                    continue;
                },
            };

            let input = value_tree.current();
            let seed_str = format!("case_{}", case_index);

            match std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                self.run_to_normal_form(&input)
            })) {
                Ok(Ok(trace)) => {
                    // Record morphology from successful run. Fingerprint
                    // the final-step term shape (fallback: input string)
                    // so the aggregate stagnation detector operates on
                    // real per-case structural identity, not a placeholder.
                    if let Some(ref mut agg) = aggregate_tracker {
                        if let Some(ref morph) = trace.morphology {
                            let final_display = trace
                                .steps
                                .last()
                                .map(|s| s.term_display.as_str())
                                .unwrap_or(input.as_str());
                            agg.record(TermMetrics {
                                node_count: morph.max_nodes,
                                depth: morph.max_depth,
                                structural_fingerprint: crate::morphology::fingerprint_of(
                                    final_display,
                                ),
                            });
                        }
                    }

                    // Record rule coverage from trace.
                    for entry in &trace.steps {
                        if entry.operation.starts_with("rewrite:") {
                            let rule = entry
                                .operation
                                .strip_prefix("rewrite:")
                                .unwrap_or(&entry.operation);
                            results.coverage.record_rule(rule);
                        } else if entry.operation == "rewrite" {
                            results.coverage.record_rule("(unnamed)");
                        }
                    }

                    if self.config.verbose {
                        eprintln!(
                            "  [{}] pass   steps={} input={:?}",
                            seed_str,
                            trace.steps.len(),
                            input,
                        );
                    }

                    results.record_pass();
                },
                Ok(Err(failure)) => {
                    // Also fingerprint into the aggregate tracker on
                    // failure — failing shapes are still part of the
                    // coverage-diversity signal.
                    if let Some(ref mut agg) = aggregate_tracker {
                        if let Some(ref morph) = failure.trace.morphology {
                            let final_display = failure
                                .trace
                                .steps
                                .last()
                                .map(|s| s.term_display.as_str())
                                .unwrap_or(failure.input.as_str());
                            agg.record(TermMetrics {
                                node_count: morph.max_nodes,
                                depth: morph.max_depth,
                                structural_fingerprint: crate::morphology::fingerprint_of(
                                    final_display,
                                ),
                            });
                        }
                    }

                    // Attempt shrinking: try to find a simpler failing input.
                    let shrunk_failure = self.try_shrink(value_tree, failure, &seed_str);

                    // Save the failing seed to the regression file.
                    if let Some(ref regression_path) = self.config.regression_path {
                        if let Some(seed) = self.config.seed {
                            save_regression_seed(regression_path, &seed);
                        } else {
                            let mut derived_seed = [0u8; 32];
                            let idx_bytes = case_index.to_le_bytes();
                            derived_seed[..4].copy_from_slice(&idx_bytes);
                            let mut hasher = std::collections::hash_map::DefaultHasher::new();
                            std::hash::Hash::hash(&shrunk_failure.input, &mut hasher);
                            let hash_bytes = std::hash::Hasher::finish(&hasher).to_le_bytes();
                            derived_seed[4..12].copy_from_slice(&hash_bytes);
                            save_regression_seed(regression_path, &derived_seed);
                        }
                    }

                    if self.config.verbose {
                        eprintln!(
                            "  [{}] fail   steps={} input={:?} error={}",
                            seed_str,
                            shrunk_failure.trace.steps.len(),
                            shrunk_failure.input,
                            shrunk_failure.error,
                        );
                    }

                    results.record_failure(shrunk_failure);
                },
                Err(panic_payload) => {
                    // Evaluation panicked (e.g., arithmetic overflow).
                    let msg = panic_payload_to_string(panic_payload);
                    let failure = crate::results::SimulationFailure {
                        seed: seed_str.clone(),
                        input: input.clone(),
                        trace: crate::trace::ExecutionTrace {
                            seed: seed_str.clone(),
                            language: self.language.name().to_string(),
                            steps: vec![],
                            outcome: crate::trace::TraceOutcome::Error {
                                message: format!("evaluation panicked: {}", msg),
                            },
                            morphology: None,
                        },
                        error: format!("panic during evaluation: {}", msg),
                    };
                    if let Some(ref regression_path) = self.config.regression_path {
                        let mut derived_seed = [0u8; 32];
                        let idx_bytes = case_index.to_le_bytes();
                        derived_seed[..4].copy_from_slice(&idx_bytes);
                        save_regression_seed(regression_path, &derived_seed);
                    }

                    if self.config.verbose {
                        eprintln!("  [{}] panic  input={:?} msg={}", seed_str, input, msg,);
                    }

                    results.record_failure(failure);
                },
            }

            case_index += 1;
        }

        // Finalize coverage.
        let total_rules = self.language.metadata().rewrites().len();
        results.coverage.finalize(total_rules);

        // Finalize aggregate morphology.
        results.aggregate_morphology = aggregate_tracker.as_ref().map(|t| t.summary());

        results
    }

    /// Attempt to shrink a failing input using proptest's value tree.
    ///
    /// Iteratively simplifies the input while it still triggers a failure.
    /// Returns the failure with the smallest reproducing input found.
    fn try_shrink<VT: ValueTree<Value = String>>(
        &self,
        mut value_tree: VT,
        initial_failure: SimulationFailure,
        seed_str: &str,
    ) -> SimulationFailure {
        let mut best_failure = initial_failure;
        let max_shrink_steps = 128;
        let mut shrink_steps = 0;

        // Trampoline-style iterative shrinking.
        loop {
            if shrink_steps >= max_shrink_steps {
                break;
            }
            shrink_steps += 1;

            if !value_tree.simplify() {
                // Try to complicate; if that fails too, we're done.
                if !value_tree.complicate() {
                    break;
                }
            }

            let shrunk_input = value_tree.current();
            match std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                self.run_to_normal_form(&shrunk_input)
            })) {
                Ok(Ok(_)) => {
                    // Shrunk input passes; try complicating.
                    if !value_tree.complicate() {
                        break;
                    }
                },
                Ok(Err(failure)) => {
                    // Still fails; record and try shrinking more.
                    best_failure = SimulationFailure {
                        seed: seed_str.to_string(),
                        input: shrunk_input,
                        trace: failure.trace,
                        error: failure.error,
                    };
                },
                Err(panic_payload) => {
                    // Panicked during shrinking — still a failure.
                    let msg = panic_payload_to_string(panic_payload);
                    best_failure = SimulationFailure {
                        seed: seed_str.to_string(),
                        input: shrunk_input,
                        trace: crate::trace::ExecutionTrace {
                            seed: seed_str.to_string(),
                            language: self.language.name().to_string(),
                            steps: vec![],
                            outcome: crate::trace::TraceOutcome::Error {
                                message: format!("evaluation panicked during shrinking: {}", msg),
                            },
                            morphology: None,
                        },
                        error: format!("panic during shrinking: {}", msg),
                    };
                },
            }
        }

        best_failure
    }

    /// Check all invariants at a given step. Returns Ok(()) or a SimulationFailure.
    fn check_invariants_at_step(
        &self,
        term_display: &str,
        step_index: usize,
        metrics: &TermMetrics,
        seed_str: &str,
        input: &str,
        steps_so_far: &[TraceEntry],
        morphology_tracker: &Option<MorphologyTracker>,
    ) -> Result<(), SimulationFailure> {
        let state = InvariantState {
            current_term_display: term_display,
            step_index,
            term_size: metrics.node_count,
            term_depth: metrics.depth,
            language: self.language,
        };

        for invariant in &self.config.invariants {
            if let Err(msg) = invariant.check(&state) {
                let trace = ExecutionTrace {
                    seed: seed_str.to_string(),
                    language: self.language.name().to_string(),
                    steps: steps_so_far.to_vec(),
                    outcome: TraceOutcome::InvariantViolation {
                        step: step_index,
                        invariant: invariant.name().to_string(),
                        message: msg.clone(),
                    },
                    morphology: morphology_tracker.as_ref().map(|t| t.summary()),
                };
                return Err(SimulationFailure {
                    seed: seed_str.to_string(),
                    input: input.to_string(),
                    trace,
                    error: format!("Invariant '{}' violated: {}", invariant.name(), msg),
                });
            }
        }

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use mettail_runtime::{
        AscentResults, BackendCapabilityDef, LanguageMetadata, RuntimeBackend,
        RuntimeBackendArtifact, RuntimeBackendReport, RuntimeChannelObservation,
        RuntimeDovetailCompleteness, RuntimeDovetailGraphKind, RuntimeDovetailRunReport,
        RuntimeDovetailTermRecord, RuntimeObservationValue, Term, TermType, VarTypeInfo,
    };
    use std::any::Any;

    #[derive(Debug, Clone)]
    struct RuntimeObservationTerm(String);

    impl std::fmt::Display for RuntimeObservationTerm {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            write!(f, "{}", self.0)
        }
    }

    impl Term for RuntimeObservationTerm {
        fn clone_box(&self) -> Box<dyn Term> {
            Box::new(self.clone())
        }

        fn term_id(&self) -> u64 {
            17
        }

        fn term_eq(&self, other: &dyn Term) -> bool {
            other
                .as_any()
                .downcast_ref::<RuntimeObservationTerm>()
                .is_some_and(|other| self.0 == other.0)
        }

        fn as_any(&self) -> &dyn Any {
            self
        }
    }

    struct RuntimeObservationMetadata;

    static RUNTIME_OBSERVATION_BACKENDS: &[BackendCapabilityDef] = &[BackendCapabilityDef {
        backend: RuntimeBackend::RhoMachine,
        is_default: true,
    }];

    static DOVETAIL_REPORT_BACKENDS: &[BackendCapabilityDef] = &[BackendCapabilityDef {
        backend: RuntimeBackend::Dovetail,
        is_default: true,
    }];

    impl LanguageMetadata for RuntimeObservationMetadata {
        fn name(&self) -> &'static str {
            "RuntimeObservationMock"
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
            RUNTIME_OBSERVATION_BACKENDS
        }
    }

    static RUNTIME_OBSERVATION_METADATA: RuntimeObservationMetadata = RuntimeObservationMetadata;

    struct DovetailReportMetadata;

    impl LanguageMetadata for DovetailReportMetadata {
        fn name(&self) -> &'static str {
            "DovetailReportMock"
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
            DOVETAIL_REPORT_BACKENDS
        }
    }

    static DOVETAIL_REPORT_METADATA: DovetailReportMetadata = DovetailReportMetadata;

    struct NoDefaultMetadata;

    impl LanguageMetadata for NoDefaultMetadata {
        fn name(&self) -> &'static str {
            "NoDefaultMock"
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
            &[]
        }
    }

    static NO_DEFAULT_METADATA: NoDefaultMetadata = NoDefaultMetadata;

    struct RuntimeObservationLanguage;

    struct DovetailReportLanguage;

    struct NoDefaultLanguage;

    fn complete_dovetail_runtime_report() -> RuntimeDovetailRunReport {
        RuntimeDovetailRunReport {
            roots: vec![b"root".to_vec()],
            root_ordinals: vec![0],
            terms: vec![RuntimeDovetailTermRecord {
                ordinal: 0,
                class_id: 0,
                key: b"root".to_vec(),
                op_display: "normal-form".to_string(),
                weight_display: "1".to_string(),
                is_root: true,
                source_display: None,
            }],
            derivation_edges: Vec::new(),
            rule_firings: Vec::new(),
            completeness: RuntimeDovetailCompleteness::Complete,
            graph_kind: RuntimeDovetailGraphKind::Derivation,
        }
    }

    fn bounded_dovetail_runtime_report() -> RuntimeDovetailRunReport {
        let mut report = complete_dovetail_runtime_report();
        report.completeness = RuntimeDovetailCompleteness::BoundedByCycleCut;
        report
    }

    impl Language for RuntimeObservationLanguage {
        fn name(&self) -> &'static str {
            "RuntimeObservationMock"
        }

        fn metadata(&self) -> &'static dyn LanguageMetadata {
            &RUNTIME_OBSERVATION_METADATA
        }

        fn parse_term(&self, input: &str) -> Result<Box<dyn Term>, String> {
            Ok(Box::new(RuntimeObservationTerm(input.to_string())))
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
            _term: &dyn Term,
        ) -> Result<RuntimeBackendReport, String> {
            match backend {
                RuntimeBackend::RhoMachine => RuntimeBackendReport::try_observations(
                    RuntimeBackend::RhoMachine,
                    RuntimeBackendArtifact::RhoNormalizedAst,
                    vec![RuntimeChannelObservation::new(
                        "OUT",
                        vec![RuntimeObservationValue::Int(5)],
                    )],
                )
                .map_err(|err| err.to_string()),
                RuntimeBackend::Ascent => self.run_ascent(_term).map(RuntimeBackendReport::ascent),
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

    impl Language for DovetailReportLanguage {
        fn name(&self) -> &'static str {
            "DovetailReportMock"
        }

        fn metadata(&self) -> &'static dyn LanguageMetadata {
            &DOVETAIL_REPORT_METADATA
        }

        fn parse_term(&self, input: &str) -> Result<Box<dyn Term>, String> {
            Ok(Box::new(RuntimeObservationTerm(input.to_string())))
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
            _term: &dyn Term,
        ) -> Result<RuntimeBackendReport, String> {
            match backend {
                RuntimeBackend::Dovetail => {
                    RuntimeBackendReport::try_dovetail(if format!("{}", _term) == "bounded" {
                        bounded_dovetail_runtime_report()
                    } else {
                        complete_dovetail_runtime_report()
                    })
                    .map_err(|err| err.to_string())
                },
                RuntimeBackend::Ascent => self.run_ascent(_term).map(RuntimeBackendReport::ascent),
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

    impl Language for NoDefaultLanguage {
        fn name(&self) -> &'static str {
            "NoDefaultMock"
        }

        fn metadata(&self) -> &'static dyn LanguageMetadata {
            &NO_DEFAULT_METADATA
        }

        fn parse_term(&self, input: &str) -> Result<Box<dyn Term>, String> {
            Ok(Box::new(RuntimeObservationTerm(input.to_string())))
        }

        fn parse_term_for_env(&self, input: &str) -> Result<Box<dyn Term>, String> {
            self.parse_term(input)
        }

        fn run_ascent(&self, _term: &dyn Term) -> Result<AscentResults, String> {
            panic!("simulation must not fabricate an Ascent backend")
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
    fn test_simulation_config_default() {
        let config = SimulationConfig::default();
        assert_eq!(config.max_steps, 1000);
        assert_eq!(config.proptest_cases, 100);
        assert!(config.track_morphology);
        assert!(config.invariants.is_empty());
        assert!(config.regression_path.is_none());
    }

    #[test]
    fn test_seed_to_hex_roundtrip() {
        let seed: [u8; 32] = [
            0x01, 0x23, 0x45, 0x67, 0x89, 0xab, 0xcd, 0xef, 0xfe, 0xdc, 0xba, 0x98, 0x76, 0x54,
            0x32, 0x10, 0x00, 0x11, 0x22, 0x33, 0x44, 0x55, 0x66, 0x77, 0x88, 0x99, 0xaa, 0xbb,
            0xcc, 0xdd, 0xee, 0xff,
        ];
        let hex = seed_to_hex(&seed);
        assert_eq!(hex.len(), 64);
        let recovered = hex_to_seed(&hex).expect("should parse valid hex");
        assert_eq!(recovered, seed);
    }

    #[test]
    fn test_hex_to_seed_invalid() {
        assert!(hex_to_seed("too_short").is_none());
        assert!(hex_to_seed(&"zz".repeat(32)).is_none());
        // Wrong length (63 chars).
        assert!(hex_to_seed(&"a".repeat(63)).is_none());
    }

    #[test]
    fn runtime_observation_backend_returns_observation_trace() {
        let language = RuntimeObservationLanguage;
        let runner = SimulationRunner::new(&language, SimulationConfig::default());

        let trace = runner
            .run_to_normal_form("rho-call")
            .expect("runtime observation report should produce a trace");

        assert_eq!(trace.steps.len(), 2);
        assert_eq!(trace.steps[1].operation, "runtime:RhoMachine:RhoNormalizedAst");
        assert_eq!(trace.steps[1].term_display, "OUT=[5]");
        match trace.outcome {
            TraceOutcome::RuntimeObservations {
                backend,
                artifact,
                channels,
                values,
                summary,
            } => {
                assert_eq!(backend, "RhoMachine");
                assert_eq!(artifact, "RhoNormalizedAst");
                assert_eq!(channels, 1);
                assert_eq!(values, 1);
                assert_eq!(summary, "OUT=[5]");
            },
            other => panic!("expected RuntimeObservations, got {other:?}"),
        }
    }

    #[test]
    fn runtime_observation_does_not_satisfy_normal_form_reachable() {
        let language = RuntimeObservationLanguage;
        let config = SimulationConfig {
            invariants: vec![Box::new(crate::invariant::NormalFormReachable { max_steps: 1 })],
            ..SimulationConfig::default()
        };
        let runner = SimulationRunner::new(&language, config);

        let failure = runner
            .run_to_normal_form("rho-call")
            .expect_err("runtime observations are not normal-form graph evidence");

        assert!(failure.error.contains("runtime observations"));
        match failure.trace.outcome {
            TraceOutcome::InvariantViolation { invariant, message, .. } => {
                assert_eq!(invariant, "NormalFormReachable");
                assert!(message.contains("runtime observations"));
                assert!(message.contains("not rewrite-result evidence"));
            },
            other => panic!("expected NormalFormReachable violation, got {other:?}"),
        }
    }

    #[test]
    fn simulation_runner_does_not_fabricate_ascent_default() {
        let language = NoDefaultLanguage;
        let runner = SimulationRunner::new(&language, SimulationConfig::default());

        let failure = runner
            .run_to_normal_form("parse-only")
            .expect_err("simulation must fail before execution without a selected default backend");

        assert!(
            failure
                .error
                .contains("does not advertise a default runtime backend"),
            "{}",
            failure.error
        );
        assert_eq!(failure.trace.steps.len(), 1);
        match failure.trace.outcome {
            TraceOutcome::Error { message } => {
                assert!(message.contains("does not advertise a default runtime backend"));
            },
            other => panic!("expected no-default runtime error, got {other:?}"),
        }
    }

    #[test]
    fn dovetail_backend_returns_runtime_report_trace() {
        let language = DovetailReportLanguage;
        let runner = SimulationRunner::new(&language, SimulationConfig::default());

        let trace = runner
            .run_to_normal_form("dovetail-call")
            .expect("Dovetail report should produce a trace");

        assert_eq!(trace.steps.len(), 2);
        assert_eq!(trace.steps[1].operation, "runtime:Dovetail:DovetailRunReport");
        assert_eq!(
            trace.steps[1].term_display,
            "DovetailRunReport(completeness=Complete, roots=[normal-form], terms=1, edges=0, rule_firings=0)"
        );
        match trace.outcome {
            TraceOutcome::RuntimeReport { backend, artifact, summary } => {
                assert_eq!(backend, "Dovetail");
                assert_eq!(artifact, "DovetailRunReport");
                assert_eq!(
                    summary,
                    "DovetailRunReport(completeness=Complete, roots=[normal-form], terms=1, edges=0, rule_firings=0)"
                );
            },
            other => panic!("expected RuntimeReport, got {other:?}"),
        }
    }

    #[test]
    fn complete_dovetail_report_satisfies_normal_form_reachable() {
        let language = DovetailReportLanguage;
        let config = SimulationConfig {
            invariants: vec![Box::new(crate::invariant::NormalFormReachable { max_steps: 1 })],
            ..SimulationConfig::default()
        };
        let runner = SimulationRunner::new(&language, config);

        let trace = runner
            .run_to_normal_form("dovetail-call")
            .expect("complete Dovetail roots are terminal rewrite evidence");

        match trace.outcome {
            TraceOutcome::RuntimeReport { backend, artifact, summary } => {
                assert_eq!(backend, "Dovetail");
                assert_eq!(artifact, "DovetailRunReport");
                assert!(summary.contains("completeness=Complete"));
                assert!(summary.contains("roots=[normal-form]"));
            },
            other => panic!("expected RuntimeReport, got {other:?}"),
        }
    }

    #[test]
    fn bounded_dovetail_report_does_not_satisfy_normal_form_reachable() {
        let language = DovetailReportLanguage;
        let config = SimulationConfig {
            invariants: vec![Box::new(crate::invariant::NormalFormReachable { max_steps: 1 })],
            ..SimulationConfig::default()
        };
        let runner = SimulationRunner::new(&language, config);

        let failure = runner
            .run_to_normal_form("bounded")
            .expect_err("cycle-bounded Dovetail reports are not exhaustive evidence");

        assert!(failure.error.contains("BoundedByCycleCut"));
        assert!(failure.error.contains("non-exhaustive"));
        match failure.trace.outcome {
            TraceOutcome::InvariantViolation { invariant, message, .. } => {
                assert_eq!(invariant, "NormalFormReachable");
                assert!(message.contains("BoundedByCycleCut"));
                assert!(message.contains("non-exhaustive"));
            },
            other => panic!("expected NormalFormReachable violation, got {other:?}"),
        }
    }

    #[test]
    fn test_regression_file_roundtrip() {
        let dir = std::env::temp_dir().join("mettail_regression_test");
        let _ = std::fs::create_dir_all(&dir);
        let path = dir.join("test.regressions");

        // Clean up from any previous run.
        let _ = std::fs::remove_file(&path);

        let seed1: [u8; 32] = [1u8; 32];
        let seed2: [u8; 32] = [2u8; 32];
        let seed3: [u8; 32] = [3u8; 32];

        // Initially empty.
        assert!(load_regression_seeds(&path).is_empty());

        // Save seeds.
        save_regression_seed(&path, &seed1);
        save_regression_seed(&path, &seed2);
        save_regression_seed(&path, &seed3);

        // Saving duplicate should not add a second entry.
        save_regression_seed(&path, &seed1);

        let loaded = load_regression_seeds(&path);
        assert_eq!(loaded.len(), 3);
        assert!(loaded.contains(&seed1));
        assert!(loaded.contains(&seed2));
        assert!(loaded.contains(&seed3));

        // Remove seed2.
        remove_regression_seed(&path, &seed2);
        let loaded = load_regression_seeds(&path);
        assert_eq!(loaded.len(), 2);
        assert!(loaded.contains(&seed1));
        assert!(!loaded.contains(&seed2));
        assert!(loaded.contains(&seed3));

        // Remove all remaining.
        remove_regression_seed(&path, &seed1);
        remove_regression_seed(&path, &seed3);
        // File should be removed when empty.
        assert!(!path.exists());
        assert!(load_regression_seeds(&path).is_empty());

        // Clean up.
        let _ = std::fs::remove_dir_all(&dir);
    }
}
