//! Simulation step types.
//!
//! Each step in a simulation trace records what operation was applied and
//! the resulting term state. These types are used by `ExecutionTrace` for
//! recording and by `SimulationRunner` for orchestration.

use serde::{Deserialize, Serialize};

/// The kind of operation applied at a simulation step.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum SimOperation {
    /// A rewrite rule fired (optionally named).
    Rewrite { rule_name: Option<String> },
    /// The input was parsed into a term.
    Parse { input: String },
    /// The term was normalized (beta-reduction, constant folding, etc.).
    Normalize,
    /// The term was directly evaluated (native type evaluation).
    DirectEval,
    /// An observation step (no transformation, just recording).
    Observe,
}

impl SimOperation {
    /// Return a short label for this operation suitable for trace output.
    pub fn label(&self) -> String {
        match self {
            SimOperation::Rewrite { rule_name: Some(name) } => format!("rewrite:{}", name),
            SimOperation::Rewrite { rule_name: None } => "rewrite".to_string(),
            SimOperation::Parse { .. } => "parse".to_string(),
            SimOperation::Normalize => "normalize".to_string(),
            SimOperation::DirectEval => "direct_eval".to_string(),
            SimOperation::Observe => "observe".to_string(),
        }
    }
}

/// A single step in a simulation execution.
#[derive(Debug, Clone)]
pub struct SimStep {
    /// Display string of the term at this step.
    pub term_display: String,
    /// Unique identifier for the term at this step.
    pub term_id: u64,
    /// The operation that was applied.
    pub operation: SimOperation,
    /// Zero-based index of this step within the trace.
    pub step_index: usize,
}
