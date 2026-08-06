//! Execution trace recording and JSONL serialization.
//!
//! An `ExecutionTrace` captures the full history of a simulation run:
//! seed, language, every step with its term/operation/metrics, the final
//! outcome, and optional morphology summary.
//!
//! Traces can be serialized to JSONL (one JSON object per line) for
//! post-hoc analysis with standard streaming JSON tools.
//!
//! ## Serialization backends
//!
//! - **JSONL text output**: hand-formatted JSON lines (no serde_json dependency)
//!   to avoid Cranelift aarch64 NEON intrinsic issues on macOS nightly.
//! - **Binary roundtrip**: `postcard` (no SIMD float paths).

use crate::morphology::{MorphologyAlert, MorphologySummary, TermMetrics};
use serde::{Deserialize, Serialize};
use std::io::{BufWriter, Write};
use std::path::Path;

/// A complete execution trace from a single simulation run.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ExecutionTrace {
    /// The seed used for this run (hex-encoded or descriptive).
    pub seed: String,
    /// The language used for this run.
    pub language: String,
    /// Steps in the trace, in order.
    pub steps: Vec<TraceEntry>,
    /// Final outcome of the simulation.
    pub outcome: TraceOutcome,
    /// Optional morphology summary (if tracking was enabled).
    pub morphology: Option<MorphologySummary>,
}

/// A single entry in an execution trace.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TraceEntry {
    /// Zero-based step index.
    pub step_index: usize,
    /// Display representation of the term at this step.
    pub term_display: String,
    /// Label for the operation applied (e.g. "parse", "rewrite:AddIntCongL").
    pub operation: String,
    /// Optional term metrics collected at this step.
    pub metrics: Option<TermMetrics>,
}

/// The final outcome of a simulation run.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum TraceOutcome {
    /// The term reached a normal form.
    NormalForm { term: String, steps: usize },
    /// The selected runtime backend produced substrate observations rather
    /// than rewrite-result evidence.
    RuntimeObservations {
        backend: String,
        artifact: String,
        channels: usize,
        values: usize,
        summary: String,
    },
    /// The selected runtime backend returned a checked terminal backend report
    /// that is not substrate observations.
    RuntimeReport {
        backend: String,
        artifact: String,
        summary: String,
    },
    /// ★ A declared operation REFUSED this input, and said why.
    ///
    /// # Why this is not `NormalForm` and not `Error`
    ///
    /// Until this variant existed a run of `6 / 0` came back as *"the run produced no reduced
    /// value"* — either a bare [`RuntimeReport`](Self::RuntimeReport) summary or, where a term
    /// display was available, a [`NormalForm`](Self::NormalForm) holding the **unreduced redex**.
    /// Both readings say the same thing a totally inert term says, so a partial operation
    /// declining was indistinguishable from a term that was already in normal form. That is the
    /// same conflation the Dovetail dispatcher had, one layer up.
    ///
    /// It is not [`Error`](Self::Error) either: an `Error` is the *simulator* failing (a parse
    /// failure, a backend failure). Here the simulator worked perfectly and the **program** has no
    /// answer — the finding belongs to the program's author.
    ///
    /// ⚠ Produced only when the run reached no reduced value AND the run report carries at least
    /// one semantic decline. A term that DOES reduce still reports [`NormalForm`](Self::NormalForm)
    /// even if some other reading of it declined — that is the lossless-promotion election: when a
    /// wider carrier supplies the value, the program has an answer and the narrower reading's
    /// decline is a note, not the outcome.
    Declined {
        /// The term the run stopped at — the redex, unreduced.
        term: String,
        /// How many trace steps were recorded before the run stopped.
        steps: usize,
        /// The declining fold's published label, e.g. `"Calculator::fold::Int_DivInt"` — the same
        /// string the rule's FIRING would carry.
        label: String,
        /// The operation's short name (`"div"`), when the partiality names one. `None` for a
        /// failure the grammar author declared with `.expect(msg)`, whose content is `detail`.
        operation: Option<String>,
        /// The stable reason discriminant — `"DivisionByZero"`, `"NotRepresentable"`,
        /// `"Declared"`, `"Unreported"`. Consumers should branch on THIS, never on `detail`.
        reason: String,
        /// The full human-readable rendering: the carrier, or the author's own message.
        detail: String,
        /// Every decline the run recorded, rendered — `label` / `reason` / `detail` above are the
        /// first one. A run can decline in several places and all of them are findings.
        all: Vec<String>,
    },
    /// The simulation hit its step limit without reaching a normal form.
    StepLimitReached { final_term: String },
    /// An invariant was violated during execution.
    InvariantViolation {
        step: usize,
        invariant: String,
        message: String,
    },
    /// An LTL temporal property was violated by the execution trace.
    ///
    /// Surfaced post-hoc (after the trace is fully built) by
    /// [`crate::runner::SimulationRunner`] when the configured
    /// `ltl_properties` are checked against the trace via
    /// [`crate::temporal::check_trace_ltl`]. Mirrors `InvariantViolation`:
    /// `step` is the violating trace step (0-based, clamped to the trace
    /// length), `formula` is the offending LTL formula string, and `message`
    /// carries the human-readable counterexample (prefix/lasso) from the
    /// model checker. This outcome is only ever produced when the user opts
    /// in by populating `SimulationConfig::ltl_properties`; the default-empty
    /// configuration never reaches this arm.
    LtlViolation {
        step: usize,
        formula: String,
        message: String,
    },
    /// An error occurred (parse failure, Ascent failure, etc.).
    Error { message: String },
}

// ═══════════════════════════════════════════════════════════════════════════════
// JSON string escaping (no serde_json dependency)
// ═══════════════════════════════════════════════════════════════════════════════

/// Escape a string for embedding in a JSON value.
/// Handles the required JSON escape sequences: `"`, `\`, and control characters.
fn json_escape(s: &str) -> String {
    let mut out = String::with_capacity(s.len() + 8);
    for ch in s.chars() {
        match ch {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            c if c.is_control() => {
                // JSON \uXXXX escape for other control chars.
                for unit in c.encode_utf16(&mut [0u16; 2]) {
                    out.push_str(&format!("\\u{:04x}", unit));
                }
            },
            c => out.push(c),
        }
    }
    out
}

/// Format a `TermMetrics` as a JSON object string, or `null` if `None`.
fn metrics_to_json(m: &Option<TermMetrics>) -> String {
    match m {
        None => "null".to_string(),
        Some(tm) => format!(
            "{{\"node_count\":{},\"depth\":{},\"structural_fingerprint\":{}}}",
            tm.node_count, tm.depth, tm.structural_fingerprint,
        ),
    }
}

/// Format a `TraceOutcome` as the JSON fields inside `{"type":"outcome",...}`.
fn outcome_to_json_fields(outcome: &TraceOutcome) -> String {
    match outcome {
        TraceOutcome::NormalForm { term, steps } => {
            format!(
                "\"kind\":\"NormalForm\",\"term\":\"{}\",\"steps\":{}",
                json_escape(term),
                steps,
            )
        },
        TraceOutcome::RuntimeObservations {
            backend,
            artifact,
            channels,
            values,
            summary,
        } => {
            format!(
                "\"kind\":\"RuntimeObservations\",\"backend\":\"{}\",\"artifact\":\"{}\",\
                 \"channels\":{},\"values\":{},\"summary\":\"{}\"",
                json_escape(backend),
                json_escape(artifact),
                channels,
                values,
                json_escape(summary),
            )
        },
        TraceOutcome::RuntimeReport { backend, artifact, summary } => {
            format!(
                "\"kind\":\"RuntimeReport\",\"backend\":\"{}\",\"artifact\":\"{}\",\
                 \"summary\":\"{}\"",
                json_escape(backend),
                json_escape(artifact),
                json_escape(summary),
            )
        },
        TraceOutcome::Declined {
            term,
            steps,
            label,
            operation,
            reason,
            detail,
            all,
        } => {
            let operation_field = match operation {
                Some(op) => format!("\"{}\"", json_escape(op)),
                None => "null".to_string(),
            };
            let all_field = all
                .iter()
                .map(|record| format!("\"{}\"", json_escape(record)))
                .collect::<Vec<_>>()
                .join(",");
            format!(
                "\"kind\":\"Declined\",\"term\":\"{}\",\"steps\":{},\"label\":\"{}\",\
                 \"operation\":{},\"reason\":\"{}\",\"detail\":\"{}\",\"all\":[{}]",
                json_escape(term),
                steps,
                json_escape(label),
                operation_field,
                json_escape(reason),
                json_escape(detail),
                all_field,
            )
        },
        TraceOutcome::StepLimitReached { final_term } => {
            format!("\"kind\":\"StepLimitReached\",\"final_term\":\"{}\"", json_escape(final_term),)
        },
        TraceOutcome::InvariantViolation { step, invariant, message } => {
            format!(
                "\"kind\":\"InvariantViolation\",\"step\":{},\"invariant\":\"{}\",\"message\":\"{}\"",
                step,
                json_escape(invariant),
                json_escape(message),
            )
        },
        TraceOutcome::LtlViolation { step, formula, message } => {
            format!(
                "\"kind\":\"LtlViolation\",\"step\":{},\"formula\":\"{}\",\"message\":\"{}\"",
                step,
                json_escape(formula),
                json_escape(message),
            )
        },
        TraceOutcome::Error { message } => {
            format!("\"kind\":\"Error\",\"message\":\"{}\"", json_escape(message),)
        },
    }
}

/// Format a `MorphologySummary` as a JSON object string.
fn morphology_to_json(m: &MorphologySummary) -> String {
    let alerts_json = if m.alerts.is_empty() {
        "[]".to_string()
    } else {
        let items: Vec<String> = m
            .alerts
            .iter()
            .map(
                |a| format!("{{\"step\":{},\"message\":\"{}\"}}", a.step, json_escape(&a.message),),
            )
            .collect();
        format!("[{}]", items.join(","))
    };

    format!(
        "\"total_steps\":{},\"min_nodes\":{},\"max_nodes\":{},\"mean_nodes\":{},\
         \"min_depth\":{},\"max_depth\":{},\"mean_depth\":{},\"distinct_shapes\":{},\
         \"alerts\":{}",
        m.total_steps,
        m.min_nodes,
        m.max_nodes,
        format_f64(m.mean_nodes),
        m.min_depth,
        m.max_depth,
        format_f64(m.mean_depth),
        m.distinct_shapes,
        alerts_json,
    )
}

/// Format an f64 for JSON: integers without a decimal point get `.0` appended
/// to keep them valid JSON numbers that parse back to f64 reliably.
fn format_f64(v: f64) -> String {
    if v.fract() == 0.0 && v.is_finite() {
        format!("{:.1}", v)
    } else {
        format!("{}", v)
    }
}

// ═══════════════════════════════════════════════════════════════════════════════
// JSONL writing (hand-formatted, no serde_json)
// ═══════════════════════════════════════════════════════════════════════════════

/// Write an `ExecutionTrace` to a JSONL file.
///
/// Format:
/// - Line 1: header object `{"type":"header","seed":...,"language":...}`
/// - Lines 2..N+1: one step object per line `{"type":"step",...}`
/// - Line N+2: outcome object `{"type":"outcome",...}`
/// - Line N+3 (optional): morphology object `{"type":"morphology",...}`
pub fn write_trace_jsonl(trace: &ExecutionTrace, path: &Path) -> std::io::Result<()> {
    let file = std::fs::File::create(path)?;
    let mut writer = BufWriter::new(file);

    // Header line.
    writeln!(
        writer,
        "{{\"type\":\"header\",\"seed\":\"{}\",\"language\":\"{}\",\"total_steps\":{}}}",
        json_escape(&trace.seed),
        json_escape(&trace.language),
        trace.steps.len(),
    )?;

    // Step lines.
    for entry in &trace.steps {
        writeln!(
            writer,
            "{{\"type\":\"step\",\"step_index\":{},\"term_display\":\"{}\",\"operation\":\"{}\",\"metrics\":{}}}",
            entry.step_index,
            json_escape(&entry.term_display),
            json_escape(&entry.operation),
            metrics_to_json(&entry.metrics),
        )?;
    }

    // Outcome line.
    writeln!(writer, "{{\"type\":\"outcome\",{}}}", outcome_to_json_fields(&trace.outcome),)?;

    // Morphology line (optional).
    if let Some(ref morphology) = trace.morphology {
        writeln!(writer, "{{\"type\":\"morphology\",{}}}", morphology_to_json(morphology),)?;
    }

    writer.flush()?;
    Ok(())
}

// ═══════════════════════════════════════════════════════════════════════════════
// JSONL reading (hand-parsed, no serde_json)
// ═══════════════════════════════════════════════════════════════════════════════

/// Read an `ExecutionTrace` back from a JSONL file.
///
/// Parses the structured JSONL format written by `write_trace_jsonl`.
pub fn read_trace_jsonl(path: &Path) -> Result<ExecutionTrace, String> {
    let contents = std::fs::read_to_string(path).map_err(|e| format!("IO error: {}", e))?;
    let mut lines = contents.lines();

    // Parse header.
    let header_line = lines
        .next()
        .ok_or_else(|| "JSONL file is empty".to_string())?;
    let seed = extract_json_string(header_line, "seed").unwrap_or_else(|| "unknown".to_string());
    let language =
        extract_json_string(header_line, "language").unwrap_or_else(|| "unknown".to_string());

    // Parse remaining lines: steps, outcome, morphology.
    let mut steps = Vec::new();
    let mut outcome: Option<TraceOutcome> = None;
    let mut morphology: Option<MorphologySummary> = None;

    for line in lines {
        if line.trim().is_empty() {
            continue;
        }

        let line_type = extract_json_string(line, "type");

        match line_type.as_deref() {
            Some("step") => {
                let step_index = extract_json_usize(line, "step_index").unwrap_or(0);
                let term_display = extract_json_string(line, "term_display").unwrap_or_default();
                let operation = extract_json_string(line, "operation").unwrap_or_default();
                let metrics = parse_metrics_from_line(line);
                steps.push(TraceEntry {
                    step_index,
                    term_display,
                    operation,
                    metrics,
                });
            },
            Some("outcome") => {
                outcome = Some(parse_outcome_from_line(line)?);
            },
            Some("morphology") => {
                morphology = Some(parse_morphology_from_line(line)?);
            },
            _ => {
                // Unknown line type, skip.
            },
        }
    }

    let outcome = outcome.ok_or_else(|| "No outcome line found in JSONL".to_string())?;

    Ok(ExecutionTrace {
        seed,
        language,
        steps,
        outcome,
        morphology,
    })
}

// ═══════════════════════════════════════════════════════════════════════════════
// Minimal JSON field extraction helpers (no serde_json)
// ═══════════════════════════════════════════════════════════════════════════════

/// Extract a JSON string value for the given key from a JSON object line.
/// Handles JSON escape sequences in the value.
fn extract_json_string(line: &str, key: &str) -> Option<String> {
    // Look for "key":"value" pattern.
    let needle = format!("\"{}\":\"", key);
    let start = line.find(&needle)? + needle.len();
    // Find the closing quote, respecting backslash escapes.
    let rest = &line[start..];
    let mut chars = rest.chars();
    let mut value = String::new();
    loop {
        match chars.next() {
            None => break,
            Some('\\') => {
                // Handle escape sequence.
                match chars.next() {
                    Some('"') => value.push('"'),
                    Some('\\') => value.push('\\'),
                    Some('n') => value.push('\n'),
                    Some('r') => value.push('\r'),
                    Some('t') => value.push('\t'),
                    Some('u') => {
                        // Parse \uXXXX.
                        let hex: String = chars.by_ref().take(4).collect();
                        if let Ok(code) = u16::from_str_radix(&hex, 16) {
                            if let Some(c) = char::from_u32(code as u32) {
                                value.push(c);
                            }
                        }
                    },
                    Some(c) => {
                        value.push('\\');
                        value.push(c);
                    },
                    None => break,
                }
            },
            Some('"') => break, // End of string value.
            Some(c) => value.push(c),
        }
    }
    Some(value)
}

/// Extract a JSON array-of-strings value for the given key from a JSON object line.
///
/// Mirrors [`extract_json_string`]'s escape handling element by element and stops at the closing
/// `]`. An absent key, or a key whose value is not an array, yields an empty `Vec` — the same
/// "absent means empty" convention the writer uses when a run declined nothing. Written by hand,
/// like every other reader here, because this module deliberately carries no `serde_json`
/// dependency (see the module header).
fn extract_json_string_array(line: &str, key: &str) -> Vec<String> {
    let needle = format!("\"{}\":[", key);
    let Some(open) = line.find(&needle) else {
        return Vec::new();
    };
    let rest = &line[open + needle.len()..];
    let mut out = Vec::new();
    let mut chars = rest.chars();
    loop {
        // Skip to the next element's opening quote, or stop at the array's end.
        let mut in_element = false;
        for c in chars.by_ref() {
            match c {
                '"' => {
                    in_element = true;
                    break;
                },
                ']' => return out,
                _ => {},
            }
        }
        if !in_element {
            return out;
        }
        let mut value = String::new();
        loop {
            match chars.next() {
                None => return out,
                Some('\\') => match chars.next() {
                    Some('"') => value.push('"'),
                    Some('\\') => value.push('\\'),
                    Some('n') => value.push('\n'),
                    Some('r') => value.push('\r'),
                    Some('t') => value.push('\t'),
                    Some('u') => {
                        let hex: String = chars.by_ref().take(4).collect();
                        if let Ok(code) = u16::from_str_radix(&hex, 16) {
                            if let Some(c) = char::from_u32(code as u32) {
                                value.push(c);
                            }
                        }
                    },
                    Some(c) => {
                        value.push('\\');
                        value.push(c);
                    },
                    None => return out,
                },
                Some('"') => break,
                Some(c) => value.push(c),
            }
        }
        out.push(value);
    }
}

/// Extract a JSON integer value for the given key from a JSON object line.
fn extract_json_usize(line: &str, key: &str) -> Option<usize> {
    // Look for "key":NUMBER pattern.
    let needle = format!("\"{}\":", key);
    let start = line.find(&needle)? + needle.len();
    let rest = &line[start..];
    let num_str: String = rest.chars().take_while(|c| c.is_ascii_digit()).collect();
    num_str.parse().ok()
}

/// Extract a JSON f64 value for the given key from a JSON object line.
fn extract_json_f64(line: &str, key: &str) -> Option<f64> {
    let needle = format!("\"{}\":", key);
    let start = line.find(&needle)? + needle.len();
    let rest = &line[start..];
    let num_str: String = rest
        .chars()
        .take_while(|c| {
            c.is_ascii_digit() || *c == '.' || *c == '-' || *c == 'e' || *c == 'E' || *c == '+'
        })
        .collect();
    num_str.parse().ok()
}

/// Extract a JSON u64 value for the given key from a JSON object line.
fn extract_json_u64(line: &str, key: &str) -> Option<u64> {
    let needle = format!("\"{}\":", key);
    let start = line.find(&needle)? + needle.len();
    let rest = &line[start..];
    let num_str: String = rest.chars().take_while(|c| c.is_ascii_digit()).collect();
    num_str.parse().ok()
}

/// Parse `TermMetrics` from the `"metrics":...` portion of a step line.
fn parse_metrics_from_line(line: &str) -> Option<TermMetrics> {
    // Check if metrics is null.
    if let Some(pos) = line.find("\"metrics\":") {
        let rest = &line[pos + "\"metrics\":".len()..];
        let trimmed = rest.trim_start();
        if trimmed.starts_with("null") {
            return None;
        }
    } else {
        return None;
    }

    // Extract fields from the metrics sub-object.
    // Since the metrics object is embedded in the line, we need to
    // find the sub-object and parse from it.
    let metrics_start = line.find("\"metrics\":")? + "\"metrics\":".len();
    let sub = &line[metrics_start..];

    // Find the closing brace of the metrics object.
    let obj_start = sub.find('{')?;
    let obj_sub = &sub[obj_start..];
    let mut depth = 0i32;
    let mut end = 0;
    for (i, ch) in obj_sub.char_indices() {
        match ch {
            '{' => depth += 1,
            '}' => {
                depth -= 1;
                if depth == 0 {
                    end = i + 1;
                    break;
                }
            },
            _ => {},
        }
    }
    let metrics_json = &obj_sub[..end];

    let node_count = extract_json_usize(metrics_json, "node_count")?;
    let depth = extract_json_usize(metrics_json, "depth")?;
    let structural_fingerprint = extract_json_u64(metrics_json, "structural_fingerprint")?;

    Some(TermMetrics {
        node_count,
        depth,
        structural_fingerprint,
    })
}

/// Parse a `TraceOutcome` from an outcome JSONL line.
fn parse_outcome_from_line(line: &str) -> Result<TraceOutcome, String> {
    let kind = extract_json_string(line, "kind")
        .ok_or_else(|| "Missing 'kind' in outcome line".to_string())?;

    match kind.as_str() {
        "NormalForm" => {
            let term = extract_json_string(line, "term")
                .ok_or_else(|| "Missing 'term' in NormalForm outcome".to_string())?;
            let steps = extract_json_usize(line, "steps")
                .ok_or_else(|| "Missing 'steps' in NormalForm outcome".to_string())?;
            Ok(TraceOutcome::NormalForm { term, steps })
        },
        "RuntimeObservations" => {
            let backend = extract_json_string(line, "backend")
                .ok_or_else(|| "Missing 'backend' in RuntimeObservations outcome".to_string())?;
            let artifact = extract_json_string(line, "artifact")
                .ok_or_else(|| "Missing 'artifact' in RuntimeObservations outcome".to_string())?;
            let channels = extract_json_usize(line, "channels")
                .ok_or_else(|| "Missing 'channels' in RuntimeObservations outcome".to_string())?;
            let values = extract_json_usize(line, "values")
                .ok_or_else(|| "Missing 'values' in RuntimeObservations outcome".to_string())?;
            let summary = extract_json_string(line, "summary")
                .ok_or_else(|| "Missing 'summary' in RuntimeObservations outcome".to_string())?;
            Ok(TraceOutcome::RuntimeObservations {
                backend,
                artifact,
                channels,
                values,
                summary,
            })
        },
        "RuntimeReport" => {
            let backend = extract_json_string(line, "backend")
                .ok_or_else(|| "Missing 'backend' in RuntimeReport outcome".to_string())?;
            let artifact = extract_json_string(line, "artifact")
                .ok_or_else(|| "Missing 'artifact' in RuntimeReport outcome".to_string())?;
            let summary = extract_json_string(line, "summary")
                .ok_or_else(|| "Missing 'summary' in RuntimeReport outcome".to_string())?;
            Ok(TraceOutcome::RuntimeReport { backend, artifact, summary })
        },
        "Declined" => {
            let term = extract_json_string(line, "term")
                .ok_or_else(|| "Missing 'term' in Declined outcome".to_string())?;
            let steps = extract_json_usize(line, "steps")
                .ok_or_else(|| "Missing 'steps' in Declined outcome".to_string())?;
            let label = extract_json_string(line, "label")
                .ok_or_else(|| "Missing 'label' in Declined outcome".to_string())?;
            // `operation` is nullable — a `.expect(msg)`-declared failure names no operation.
            let operation = extract_json_string(line, "operation");
            let reason = extract_json_string(line, "reason")
                .ok_or_else(|| "Missing 'reason' in Declined outcome".to_string())?;
            let detail = extract_json_string(line, "detail")
                .ok_or_else(|| "Missing 'detail' in Declined outcome".to_string())?;
            let all = extract_json_string_array(line, "all");
            Ok(TraceOutcome::Declined {
                term,
                steps,
                label,
                operation,
                reason,
                detail,
                all,
            })
        },
        "StepLimitReached" => {
            let final_term = extract_json_string(line, "final_term")
                .ok_or_else(|| "Missing 'final_term' in StepLimitReached outcome".to_string())?;
            Ok(TraceOutcome::StepLimitReached { final_term })
        },
        "InvariantViolation" => {
            let step = extract_json_usize(line, "step")
                .ok_or_else(|| "Missing 'step' in InvariantViolation outcome".to_string())?;
            let invariant = extract_json_string(line, "invariant")
                .ok_or_else(|| "Missing 'invariant' in InvariantViolation outcome".to_string())?;
            let message = extract_json_string(line, "message")
                .ok_or_else(|| "Missing 'message' in InvariantViolation outcome".to_string())?;
            Ok(TraceOutcome::InvariantViolation { step, invariant, message })
        },
        "LtlViolation" => {
            let step = extract_json_usize(line, "step")
                .ok_or_else(|| "Missing 'step' in LtlViolation outcome".to_string())?;
            let formula = extract_json_string(line, "formula")
                .ok_or_else(|| "Missing 'formula' in LtlViolation outcome".to_string())?;
            let message = extract_json_string(line, "message")
                .ok_or_else(|| "Missing 'message' in LtlViolation outcome".to_string())?;
            Ok(TraceOutcome::LtlViolation { step, formula, message })
        },
        "Error" => {
            let message = extract_json_string(line, "message")
                .ok_or_else(|| "Missing 'message' in Error outcome".to_string())?;
            Ok(TraceOutcome::Error { message })
        },
        other => Err(format!("Unknown outcome kind: {}", other)),
    }
}

/// Parse a `MorphologySummary` from a morphology JSONL line.
fn parse_morphology_from_line(line: &str) -> Result<MorphologySummary, String> {
    let total_steps = extract_json_usize(line, "total_steps")
        .ok_or_else(|| "Missing 'total_steps' in morphology".to_string())?;
    let min_nodes = extract_json_usize(line, "min_nodes")
        .ok_or_else(|| "Missing 'min_nodes' in morphology".to_string())?;
    let max_nodes = extract_json_usize(line, "max_nodes")
        .ok_or_else(|| "Missing 'max_nodes' in morphology".to_string())?;
    let mean_nodes = extract_json_f64(line, "mean_nodes")
        .ok_or_else(|| "Missing 'mean_nodes' in morphology".to_string())?;
    let min_depth = extract_json_usize(line, "min_depth")
        .ok_or_else(|| "Missing 'min_depth' in morphology".to_string())?;
    let max_depth = extract_json_usize(line, "max_depth")
        .ok_or_else(|| "Missing 'max_depth' in morphology".to_string())?;
    let mean_depth = extract_json_f64(line, "mean_depth")
        .ok_or_else(|| "Missing 'mean_depth' in morphology".to_string())?;
    let distinct_shapes = extract_json_usize(line, "distinct_shapes")
        .ok_or_else(|| "Missing 'distinct_shapes' in morphology".to_string())?;

    // Parse alerts array. For simplicity, we parse the alerts sub-array.
    let alerts = parse_alerts_from_line(line);

    Ok(MorphologySummary {
        total_steps,
        min_nodes,
        max_nodes,
        mean_nodes,
        min_depth,
        max_depth,
        mean_depth,
        distinct_shapes,
        alerts,
    })
}

/// Parse the `"alerts":[...]` array from a morphology line.
fn parse_alerts_from_line(line: &str) -> Vec<MorphologyAlert> {
    let needle = "\"alerts\":";
    let Some(start) = line.find(needle) else {
        return Vec::new();
    };
    let rest = &line[start + needle.len()..];
    let trimmed = rest.trim_start();
    if trimmed.starts_with("[]") {
        return Vec::new();
    }

    // Find the matching closing bracket.
    let arr_start = match trimmed.find('[') {
        Some(i) => i,
        None => return Vec::new(),
    };
    let arr_sub = &trimmed[arr_start..];
    let mut depth = 0i32;
    let mut end = 0;
    for (i, ch) in arr_sub.char_indices() {
        match ch {
            '[' => depth += 1,
            ']' => {
                depth -= 1;
                if depth == 0 {
                    end = i + 1;
                    break;
                }
            },
            _ => {},
        }
    }
    let arr_str = &arr_sub[..end];

    // Split on `},{` to separate alert objects.
    let mut alerts = Vec::new();
    // Remove outer brackets.
    let inner = &arr_str[1..arr_str.len() - 1];
    if inner.trim().is_empty() {
        return alerts;
    }

    // Split on "},{" while preserving braces for each object.
    let parts: Vec<&str> = inner.split("},{").collect();
    for (i, part) in parts.iter().enumerate() {
        let obj = if parts.len() == 1 {
            part.to_string()
        } else if i == 0 {
            format!("{}}}", part)
        } else if i == parts.len() - 1 {
            format!("{{{}", part)
        } else {
            format!("{{{}}}", part)
        };

        let step = extract_json_usize(&obj, "step").unwrap_or(0);
        let message = extract_json_string(&obj, "message").unwrap_or_default();
        alerts.push(MorphologyAlert { step, message });
    }

    alerts
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_execution_trace_construction() {
        let trace = ExecutionTrace {
            seed: "test-seed".to_string(),
            language: "Calculator".to_string(),
            steps: vec![
                TraceEntry {
                    step_index: 0,
                    term_display: "1 + 2".to_string(),
                    operation: "parse".to_string(),
                    metrics: Some(TermMetrics {
                        node_count: 3,
                        depth: 0,
                        structural_fingerprint: 12345,
                    }),
                },
                TraceEntry {
                    step_index: 1,
                    term_display: "3".to_string(),
                    operation: "rewrite".to_string(),
                    metrics: Some(TermMetrics {
                        node_count: 1,
                        depth: 0,
                        structural_fingerprint: 67890,
                    }),
                },
            ],
            outcome: TraceOutcome::NormalForm { term: "3".to_string(), steps: 2 },
            morphology: Some(MorphologySummary {
                total_steps: 2,
                min_nodes: 1,
                max_nodes: 3,
                mean_nodes: 2.0,
                min_depth: 0,
                max_depth: 0,
                mean_depth: 0.0,
                distinct_shapes: 2,
                alerts: vec![],
            }),
        };

        assert_eq!(trace.seed, "test-seed");
        assert_eq!(trace.language, "Calculator");
        assert_eq!(trace.steps.len(), 2);
        assert_eq!(trace.steps[0].step_index, 0);
        assert_eq!(trace.steps[0].term_display, "1 + 2");
        assert_eq!(trace.steps[0].operation, "parse");
        assert_eq!(trace.steps[1].step_index, 1);
        assert_eq!(trace.steps[1].term_display, "3");
        assert_eq!(trace.steps[1].operation, "rewrite");

        match &trace.outcome {
            TraceOutcome::NormalForm { term, steps } => {
                assert_eq!(term, "3");
                assert_eq!(*steps, 2);
            },
            other => panic!("Expected NormalForm, got: {:?}", other),
        }

        let morph = trace.morphology.as_ref().expect("morphology present");
        assert_eq!(morph.total_steps, 2);
        assert_eq!(morph.min_nodes, 1);
        assert_eq!(morph.max_nodes, 3);
        assert_eq!(morph.distinct_shapes, 2);
    }

    #[test]
    fn test_trace_outcome_variants() {
        let nf = TraceOutcome::NormalForm { term: "42".to_string(), steps: 5 };
        assert!(matches!(nf, TraceOutcome::NormalForm { .. }));

        let ro = TraceOutcome::RuntimeObservations {
            backend: "RhoMachine".to_string(),
            artifact: "RhoNormalizedAst".to_string(),
            channels: 1,
            values: 2,
            summary: "OUT=[1, 2]".to_string(),
        };
        assert!(matches!(ro, TraceOutcome::RuntimeObservations { .. }));

        let rr = TraceOutcome::RuntimeReport {
            backend: "Dovetail".to_string(),
            artifact: "DovetailRunReport".to_string(),
            summary: "DovetailRunReport(completeness=Complete, roots=[pair], terms=3, edges=2)"
                .to_string(),
        };
        assert!(matches!(rr, TraceOutcome::RuntimeReport { .. }));

        let sl = TraceOutcome::StepLimitReached { final_term: "stuck".to_string() };
        assert!(matches!(sl, TraceOutcome::StepLimitReached { .. }));

        let iv = TraceOutcome::InvariantViolation {
            step: 3,
            invariant: "BoundedSize".to_string(),
            message: "too big".to_string(),
        };
        assert!(matches!(iv, TraceOutcome::InvariantViolation { .. }));

        let err = TraceOutcome::Error { message: "parse error".to_string() };
        assert!(matches!(err, TraceOutcome::Error { .. }));
    }

    /// JSONL file I/O roundtrip test.
    ///
    /// Uses hand-formatted JSON (no serde_json) to avoid Cranelift aarch64
    /// NEON intrinsic issues on macOS nightly.
    #[test]
    fn test_trace_serialization_roundtrip() {
        let trace = ExecutionTrace {
            seed: "test-seed".to_string(),
            language: "Calculator".to_string(),
            steps: vec![
                TraceEntry {
                    step_index: 0,
                    term_display: "1 + 2".to_string(),
                    operation: "parse".to_string(),
                    metrics: Some(TermMetrics {
                        node_count: 3,
                        depth: 0,
                        structural_fingerprint: 12345,
                    }),
                },
                TraceEntry {
                    step_index: 1,
                    term_display: "3".to_string(),
                    operation: "rewrite".to_string(),
                    metrics: Some(TermMetrics {
                        node_count: 1,
                        depth: 0,
                        structural_fingerprint: 67890,
                    }),
                },
            ],
            outcome: TraceOutcome::NormalForm { term: "3".to_string(), steps: 2 },
            morphology: Some(MorphologySummary {
                total_steps: 2,
                min_nodes: 1,
                max_nodes: 3,
                mean_nodes: 2.0,
                min_depth: 0,
                max_depth: 0,
                mean_depth: 0.0,
                distinct_shapes: 2,
                alerts: vec![],
            }),
        };

        let dir = std::env::temp_dir().join("mettail_trace_test");
        let _ = std::fs::create_dir_all(&dir);
        let path = dir.join("test_trace.jsonl");

        write_trace_jsonl(&trace, &path).expect("write should succeed");

        // Read back and verify.
        let recovered = read_trace_jsonl(&path).expect("read should succeed");
        assert_eq!(recovered.seed, trace.seed);
        assert_eq!(recovered.language, trace.language);
        assert_eq!(recovered.steps.len(), trace.steps.len());
        assert_eq!(recovered.steps[0].term_display, "1 + 2");
        assert_eq!(recovered.steps[1].term_display, "3");

        match &recovered.outcome {
            TraceOutcome::NormalForm { term, steps } => {
                assert_eq!(term, "3");
                assert_eq!(*steps, 2);
            },
            other => panic!("Expected NormalForm, got: {:?}", other),
        }

        assert!(recovered.morphology.is_some());

        // Clean up.
        let _ = std::fs::remove_file(&path);
    }

    #[test]
    fn test_runtime_observations_serialization_roundtrip() {
        let trace = ExecutionTrace {
            seed: "test-seed".to_string(),
            language: "RhoDispatch".to_string(),
            steps: vec![TraceEntry {
                step_index: 0,
                term_display: "OUT=[5]".to_string(),
                operation: "runtime:RhoMachine:RhoNormalizedAst".to_string(),
                metrics: None,
            }],
            outcome: TraceOutcome::RuntimeObservations {
                backend: "RhoMachine".to_string(),
                artifact: "RhoNormalizedAst".to_string(),
                channels: 1,
                values: 1,
                summary: "OUT=[5]".to_string(),
            },
            morphology: None,
        };

        let dir = std::env::temp_dir().join("mettail_trace_test");
        let _ = std::fs::create_dir_all(&dir);
        let path = dir.join("runtime_observations.jsonl");

        write_trace_jsonl(&trace, &path).expect("write should succeed");
        let recovered = read_trace_jsonl(&path).expect("read should succeed");

        match recovered.outcome {
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
            other => panic!("Expected RuntimeObservations, got: {:?}", other),
        }

        let _ = std::fs::remove_file(&path);
    }

    #[test]
    fn test_runtime_report_serialization_roundtrip() {
        let trace = ExecutionTrace {
            seed: "test-seed".to_string(),
            language: "DovetailMock".to_string(),
            steps: vec![TraceEntry {
                step_index: 0,
                term_display:
                    "DovetailRunReport(completeness=Complete, roots=[x], terms=1, edges=0)"
                        .to_string(),
                operation: "runtime:Dovetail:DovetailRunReport".to_string(),
                metrics: None,
            }],
            outcome: TraceOutcome::RuntimeReport {
                backend: "Dovetail".to_string(),
                artifact: "DovetailRunReport".to_string(),
                summary: "DovetailRunReport(completeness=Complete, roots=[x], terms=1, edges=0)"
                    .to_string(),
            },
            morphology: None,
        };

        let dir = std::env::temp_dir().join("mettail_trace_test");
        let _ = std::fs::create_dir_all(&dir);
        let path = dir.join("runtime_report.jsonl");

        write_trace_jsonl(&trace, &path).expect("write should succeed");
        let recovered = read_trace_jsonl(&path).expect("read should succeed");

        match recovered.outcome {
            TraceOutcome::RuntimeReport { backend, artifact, summary } => {
                assert_eq!(backend, "Dovetail");
                assert_eq!(artifact, "DovetailRunReport");
                assert_eq!(
                    summary,
                    "DovetailRunReport(completeness=Complete, roots=[x], terms=1, edges=0)"
                );
            },
            other => panic!("Expected RuntimeReport, got: {:?}", other),
        }

        let _ = std::fs::remove_file(&path);
    }

    /// ★ The DECLINED outcome survives the JSONL round trip — including the nullable `operation`
    /// and the string array.
    ///
    /// The wire form is the artifact a downstream consumer reads, so a variant that renders but
    /// does not parse back is a variant that exists only inside this process. Both the
    /// operation-bearing shape (arithmetic) and the operation-less shape (an author's
    /// `.expect(msg)`) are exercised, because they take different branches of the reader.
    #[test]
    fn test_declined_serialization_roundtrip() {
        let dir = std::env::temp_dir().join("mettail_trace_test");
        let _ = std::fs::create_dir_all(&dir);

        // (a) An arithmetic decline: the operation and carrier are known.
        let arithmetic = ExecutionTrace {
            seed: "test-seed".to_string(),
            language: "Calculator".to_string(),
            steps: vec![TraceEntry {
                step_index: 0,
                term_display: "6 / 0".to_string(),
                operation: "runtime:Dovetail:DovetailRunReport".to_string(),
                metrics: None,
            }],
            outcome: TraceOutcome::Declined {
                term: "6 / 0".to_string(),
                steps: 1,
                label: "Calculator::fold::Int_DivInt".to_string(),
                operation: Some("div".to_string()),
                reason: "DivisionByZero".to_string(),
                detail: "`div` on `i32` is undefined here: division by zero".to_string(),
                all: vec![
                    "Calculator::fold::Int_DivInt declined: `div` on `i32` is undefined here: \
                     division by zero"
                        .to_string(),
                ],
            },
            morphology: None,
        };
        let path = dir.join("declined_arithmetic.jsonl");
        write_trace_jsonl(&arithmetic, &path).expect("write should succeed");
        match read_trace_jsonl(&path)
            .expect("read should succeed")
            .outcome
        {
            TraceOutcome::Declined {
                term,
                steps,
                label,
                operation,
                reason,
                detail,
                all,
            } => {
                assert_eq!(term, "6 / 0");
                assert_eq!(steps, 1);
                assert_eq!(label, "Calculator::fold::Int_DivInt");
                assert_eq!(operation.as_deref(), Some("div"));
                assert_eq!(reason, "DivisionByZero", "★ the DISCRIMINANT must survive verbatim");
                assert!(detail.contains("division by zero"), "detail was {detail:?}");
                assert_eq!(all.len(), 1, "the full record list must survive: {all:?}");
            },
            other => panic!("Expected Declined, got: {other:?}"),
        }
        let _ = std::fs::remove_file(&path);

        // (b) An author-declared decline: NO operation, and the message is the content. The
        // `"operation":null` field must read back as `None` rather than as the string "null".
        let declared = ExecutionTrace {
            seed: "test-seed".to_string(),
            language: "Calculator".to_string(),
            steps: Vec::new(),
            outcome: TraceOutcome::Declined {
                term: "at(list(1, 2), 5)".to_string(),
                steps: 0,
                label: "Calculator::fold::Proc_ElemList".to_string(),
                operation: None,
                reason: "Declared".to_string(),
                detail: "ElemList: invalid index".to_string(),
                all: vec![
                    "Calculator::fold::Proc_ElemList declined: ElemList: invalid index".to_string(),
                    "Calculator::fold::Proc_GetMap declined: get: key not found".to_string(),
                ],
            },
            morphology: None,
        };
        let path = dir.join("declined_declared.jsonl");
        write_trace_jsonl(&declared, &path).expect("write should succeed");
        match read_trace_jsonl(&path)
            .expect("read should succeed")
            .outcome
        {
            TraceOutcome::Declined { operation, reason, detail, all, .. } => {
                assert_eq!(
                    operation, None,
                    "★ a `.expect(msg)` decline names no operation, and `null` must read back as \
                     `None` — not as the four-character string",
                );
                assert_eq!(reason, "Declared");
                assert_eq!(
                    detail, "ElemList: invalid index",
                    "★★ the author's own message must survive to the wire",
                );
                assert_eq!(all.len(), 2, "a multi-element array must survive: {all:?}");
                assert!(all[1].contains("get: key not found"), "{all:?}");
            },
            other => panic!("Expected Declined, got: {other:?}"),
        }
        let _ = std::fs::remove_file(&path);
    }

    #[test]
    fn test_json_escape() {
        assert_eq!(json_escape("hello"), "hello");
        assert_eq!(json_escape("he\"llo"), "he\\\"llo");
        assert_eq!(json_escape("back\\slash"), "back\\\\slash");
        assert_eq!(json_escape("new\nline"), "new\\nline");
        assert_eq!(json_escape("tab\there"), "tab\\there");
    }

    #[test]
    fn test_extract_json_string() {
        let line = r#"{"type":"header","seed":"abc-123","language":"Calculator"}"#;
        assert_eq!(extract_json_string(line, "type"), Some("header".to_string()));
        assert_eq!(extract_json_string(line, "seed"), Some("abc-123".to_string()));
        assert_eq!(extract_json_string(line, "language"), Some("Calculator".to_string()));
        assert_eq!(extract_json_string(line, "missing"), None);
    }

    #[test]
    fn test_extract_json_usize() {
        let line = r#"{"type":"step","step_index":42,"term_display":"x"}"#;
        assert_eq!(extract_json_usize(line, "step_index"), Some(42));
    }

    /// Binary roundtrip test using postcard.
    ///
    /// Uses `postcard` (no SIMD float paths) to avoid Cranelift aarch64
    /// NEON intrinsic issues that `serde_json` triggers on macOS nightly.
    #[test]
    fn test_postcard_binary_roundtrip() {
        let trace = ExecutionTrace {
            seed: "binary-test".to_string(),
            language: "Calculator".to_string(),
            steps: vec![TraceEntry {
                step_index: 0,
                term_display: "1 + 2".to_string(),
                operation: "parse".to_string(),
                metrics: Some(TermMetrics {
                    node_count: 3,
                    depth: 0,
                    structural_fingerprint: 12345,
                }),
            }],
            outcome: TraceOutcome::NormalForm { term: "3".to_string(), steps: 1 },
            morphology: None,
        };

        let bytes = postcard::to_allocvec(&trace).expect("postcard serialize should succeed");
        let recovered: ExecutionTrace =
            postcard::from_bytes(&bytes).expect("postcard deserialize should succeed");

        assert_eq!(recovered.seed, trace.seed);
        assert_eq!(recovered.language, trace.language);
        assert_eq!(recovered.steps.len(), 1);
        assert_eq!(recovered.steps[0].term_display, "1 + 2");
        match &recovered.outcome {
            TraceOutcome::NormalForm { term, steps } => {
                assert_eq!(term, "3");
                assert_eq!(*steps, 1);
            },
            other => panic!("Expected NormalForm, got: {:?}", other),
        }
        assert!(recovered.morphology.is_none());
    }
}
