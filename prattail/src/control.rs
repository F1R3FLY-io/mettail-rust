//! Shared parser/evaluator control directives.
//!
//! Hosts [`CekControl`] — formerly defined in `prattail/src/cek.rs`. The
//! evaluator (`cek_eval.rs`) uses this type for observer return values;
//! the parser-side CEK observer (in `cek.rs`) also uses it. Moving it to
//! a neutral location decouples evaluator from the parser-side CEK types
//! that get deleted during Stage 6 Phase E.4 (atomic-swap commit 2).
//!
//! Per the Stage 6 Phase 10 (F.0) plan, `CekControl` keeps its existing
//! variant names + API; only the import path changes for consumers.

/// Observer control response — returned by parser/evaluator observers
/// to direct the next step.
///
/// - `Continue`: proceed to the next transition (default / fast path).
/// - `Checkpoint`: record the current configuration and continue.
/// - `Abort`: halt evaluation immediately, returning partial results.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum CekControl {
    /// Proceed with the next transition.
    Continue,
    /// Record a checkpoint at the current configuration, then continue.
    Checkpoint,
    /// Abort the parse, returning partial results.
    Abort,
}

impl Default for CekControl {
    fn default() -> Self {
        Self::Continue
    }
}
