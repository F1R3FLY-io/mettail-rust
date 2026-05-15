//! WPDS incremental parsing session.
//!
//! Stage 5 of W7 plan v5.1. Provides [`WpdsIncrementalSession`], the
//! load-bearing affordance for LSP `textDocument/didChange` integration
//! per survey contracts (R8)–(R14):
//!
//! - On file open, the LSP server seeds the session with checkpoints
//!   recorded as the walker advances (use [`WpdsIncrementalSession::record_checkpoint`]).
//! - On edit at position `p`, the server calls
//!   [`WpdsIncrementalSession::invalidate_after`] then
//!   [`WpdsIncrementalSession::reparse`].
//! - The session locates the nearest checkpoint at-or-before `p`, resumes
//!   a fresh walker from that configuration, and drives until convergence
//!   (state + stack match) or the engine terminates.
//!
//! Closes survey gap class B (R8 specifically): the previous
//! `IncrementalSession` in `cek.rs` exposed checkpoint storage but no
//! `reparse` method.
//!
//! ## Memory budget
//!
//! Per the survey (R12), token-level checkpoints with copy-on-write stacks
//! cost ~200–400 KB per file. This session uses owned `Vec<StackSymbolV2>`
//! snapshots; CoW-stack optimization is a future enhancement (Stage 11
//! follow-up if needed).

use std::collections::BTreeMap;

use crate::automata::semiring::Semiring;
use crate::wpds_runtime::{WpdsConfiguration, WpdsState};
use crate::wpds_walker::{WpdsStepEngine, WpdsWalker};

// ══════════════════════════════════════════════════════════════════════════════
// WpdsIncrementalSession
// ══════════════════════════════════════════════════════════════════════════════

/// Per-buffer checkpoint cache supporting incremental reparse.
///
/// Generic over the weight semiring `W`. Typical instantiation:
/// `WpdsIncrementalSession<LexicographicWeight>`.
pub struct WpdsIncrementalSession<W: Semiring> {
    checkpoint_interval: usize,
    checkpoints: BTreeMap<usize, WpdsConfiguration<W>>,
}

/// Error returned by [`WpdsIncrementalSession::reparse`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ReparseError {
    /// No checkpoint exists at or before the requested position.
    NoCheckpoint,
    /// Walker terminated in an error state.
    EngineFailed(String),
}

impl<W: Semiring + crate::wpds_runtime::SnapshotWeight> WpdsIncrementalSession<W> {
    /// Create a new session with the given checkpoint interval.
    ///
    /// `checkpoint_interval = 1` means snapshot every token (sub-microsecond
    /// edits, ~400 KB/file). Higher intervals trade reparse speed for memory.
    pub fn new(checkpoint_interval: usize) -> Self {
        WpdsIncrementalSession {
            checkpoint_interval: checkpoint_interval.max(1),
            checkpoints: BTreeMap::new(),
        }
    }

    /// Current checkpoint interval.
    pub fn checkpoint_interval(&self) -> usize {
        self.checkpoint_interval
    }

    /// Set the checkpoint interval. Existing checkpoints are kept.
    pub fn set_checkpoint_interval(&mut self, n: usize) {
        self.checkpoint_interval = n.max(1);
    }

    /// Record a checkpoint at the given position.
    ///
    /// Existing checkpoint at `pos` is overwritten. Caller is responsible
    /// for honoring `checkpoint_interval` (the session does not gate).
    pub fn record_checkpoint(&mut self, pos: usize, config: WpdsConfiguration<W>) {
        self.checkpoints.insert(pos, config);
    }

    /// Locate the latest checkpoint at or before `pos`.
    ///
    /// Returns the position and the stored configuration. O(log N) via BTreeMap.
    pub fn checkpoint_at_or_before(
        &self,
        pos: usize,
    ) -> Option<(usize, &WpdsConfiguration<W>)> {
        self.checkpoints
            .range(..=pos)
            .next_back()
            .map(|(p, c)| (*p, c))
    }

    /// Drop all checkpoints strictly after `pos`.
    ///
    /// Called by LSP servers on `didChange` to invalidate stale snapshots
    /// downstream of an edit. Keeps the checkpoint at `pos` intact.
    pub fn invalidate_after(&mut self, pos: usize) {
        let to_remove: Vec<usize> = self
            .checkpoints
            .range((pos + 1)..)
            .map(|(p, _)| *p)
            .collect();
        for p in to_remove {
            self.checkpoints.remove(&p);
        }
    }

    /// Drop all checkpoints.
    pub fn clear(&mut self) {
        self.checkpoints.clear();
    }

    /// Number of stored checkpoints.
    pub fn checkpoint_count(&self) -> usize {
        self.checkpoints.len()
    }

    /// Whether the session has any checkpoints.
    pub fn is_empty(&self) -> bool {
        self.checkpoints.is_empty()
    }

    /// Iterator over all checkpoints in position order.
    pub fn iter(&self) -> impl Iterator<Item = (&usize, &WpdsConfiguration<W>)> {
        self.checkpoints.iter()
    }

    /// Convergence check: two configurations are convergent when their
    /// state, stack contents (bottom-to-top), and position all match.
    ///
    /// Per survey contract R10. Equivalent to `cek.rs::is_convergent` but
    /// for WPDS configurations.
    pub fn is_convergent(a: &WpdsConfiguration<W>, b: &WpdsConfiguration<W>) -> bool {
        a.state == b.state && a.stack == b.stack && a.pos == b.pos
    }

    /// Drive incremental reparse starting from the nearest checkpoint at or
    /// before `edit_pos`.
    ///
    /// The session locates the resumption point, constructs a fresh walker,
    /// re-seeds it from the stored configuration, and drives the walker
    /// (via `engine`) until it reaches a terminal state or `max_steps`
    /// is exhausted.
    ///
    /// Returns the walker's final state on success, or [`ReparseError`].
    ///
    /// Phase A.1: requires a `tokens: &dyn WpdsTokenSource` so the engine's
    /// `step()` can peek the input during the reparse.
    pub fn reparse<E: WpdsStepEngine<W>>(
        &self,
        edit_pos: usize,
        engine: E,
        max_steps: usize,
        tokens: &dyn crate::wpds_runtime::WpdsTokenSource,
    ) -> Result<WpdsState, ReparseError> {
        let (cp_pos, cp_config) = self
            .checkpoint_at_or_before(edit_pos)
            .ok_or(ReparseError::NoCheckpoint)?;
        let mut walker = WpdsWalker::seeded_from(engine, cp_config.clone());
        let _ = cp_pos;
        let final_state = walker.run_to_completion(max_steps, tokens);
        match final_state {
            WpdsState::Error { ref message } => {
                Err(ReparseError::EngineFailed(message.clone()))
            }
            other => Ok(other),
        }
    }
}

impl<W: Semiring + crate::wpds_runtime::SnapshotWeight> Default for WpdsIncrementalSession<W> {
    fn default() -> Self {
        Self::new(1)
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// Tests
// ══════════════════════════════════════════════════════════════════════════════

#[cfg(test)]
mod tests {
    use super::*;
    use crate::automata::lex_weight::LexicographicWeight;
    use crate::wpds_runtime::{SliceTokenSource, StackSymbolV2, WpdsState, WpdsTokenSource};
    use crate::wpds_walker::{IdleEngine, WpdsStepAction, WpdsStepEngine};
    use crate::gss::{WpdsGss, WpdsGssNode};
    use crate::automata::TokenKind;
    use std::cell::RefCell;

    /// Empty token source used by tests that don't inspect input.
    fn empty_tokens() -> SliceTokenSource<'static> {
        static EMPTY: [TokenKind; 0] = [];
        SliceTokenSource::new(&EMPTY)
    }

    fn lex(c: f64, s: u16, r: u16) -> LexicographicWeight {
        LexicographicWeight::from_cost(c, s, r)
    }

    fn cfg(pos: usize, state: WpdsState, stack_depth: usize) -> WpdsConfiguration<LexicographicWeight> {
        WpdsConfiguration {
            pos,
            state,
            stack: (0..stack_depth as u16)
                .map(|i| StackSymbolV2::category_entry(i))
                .collect(),
            weight: lex(1.0 + pos as f64, 0, 0),
        }
    }

    #[test]
    fn new_session_is_empty() {
        let s: WpdsIncrementalSession<LexicographicWeight> = WpdsIncrementalSession::new(1);
        assert_eq!(s.checkpoint_interval(), 1);
        assert!(s.is_empty());
        assert_eq!(s.checkpoint_count(), 0);
    }

    #[test]
    fn checkpoint_interval_min_one() {
        // Zero interval is clamped to 1.
        let s: WpdsIncrementalSession<LexicographicWeight> = WpdsIncrementalSession::new(0);
        assert_eq!(s.checkpoint_interval(), 1);
    }

    #[test]
    fn record_checkpoint_increases_count() {
        let mut s: WpdsIncrementalSession<LexicographicWeight> = WpdsIncrementalSession::new(1);
        s.record_checkpoint(0, cfg(0, WpdsState::Ready { min_bp: 0 }, 1));
        s.record_checkpoint(5, cfg(5, WpdsState::PrefixDispatch { pos: 5, cur_bp: 0 }, 2));
        assert_eq!(s.checkpoint_count(), 2);
    }

    #[test]
    fn checkpoint_at_or_before_finds_latest() {
        let mut s: WpdsIncrementalSession<LexicographicWeight> = WpdsIncrementalSession::new(1);
        s.record_checkpoint(0, cfg(0, WpdsState::Ready { min_bp: 0 }, 1));
        s.record_checkpoint(5, cfg(5, WpdsState::PrefixDispatch { pos: 5, cur_bp: 0 }, 2));
        s.record_checkpoint(10, cfg(10, WpdsState::InfixLoop { cur_bp: 7 }, 3));

        let (p, c) = s.checkpoint_at_or_before(10).expect("found at exact match");
        assert_eq!(p, 10);
        assert_eq!(c.pos, 10);

        let (p, _) = s.checkpoint_at_or_before(7).expect("found at 5");
        assert_eq!(p, 5);

        let (p, _) = s.checkpoint_at_or_before(0).expect("found at 0");
        assert_eq!(p, 0);
    }

    #[test]
    fn checkpoint_at_or_before_none_for_low_position() {
        let mut s: WpdsIncrementalSession<LexicographicWeight> = WpdsIncrementalSession::new(1);
        s.record_checkpoint(5, cfg(5, WpdsState::Ready { min_bp: 0 }, 1));
        assert!(s.checkpoint_at_or_before(0).is_none());
        assert!(s.checkpoint_at_or_before(4).is_none());
    }

    #[test]
    fn invalidate_after_drops_downstream_only() {
        let mut s: WpdsIncrementalSession<LexicographicWeight> = WpdsIncrementalSession::new(1);
        for p in [0, 5, 10, 15, 20] {
            s.record_checkpoint(p, cfg(p, WpdsState::Ready { min_bp: 0 }, 1));
        }
        s.invalidate_after(10);
        // Checkpoints at 0, 5, 10 should remain; 15, 20 dropped.
        assert!(s.checkpoint_at_or_before(0).is_some());
        assert!(s.checkpoint_at_or_before(5).is_some());
        assert!(s.checkpoint_at_or_before(10).is_some());
        assert_eq!(s.checkpoint_at_or_before(20).map(|(p, _)| p), Some(10));
        assert_eq!(s.checkpoint_count(), 3);
    }

    #[test]
    fn invalidate_after_zero_keeps_checkpoint_at_zero() {
        let mut s: WpdsIncrementalSession<LexicographicWeight> = WpdsIncrementalSession::new(1);
        s.record_checkpoint(0, cfg(0, WpdsState::Ready { min_bp: 0 }, 1));
        s.record_checkpoint(5, cfg(5, WpdsState::Ready { min_bp: 0 }, 1));
        s.invalidate_after(0);
        assert!(s.checkpoint_at_or_before(0).is_some());
        assert_eq!(s.checkpoint_count(), 1);
    }

    #[test]
    fn clear_drops_all() {
        let mut s: WpdsIncrementalSession<LexicographicWeight> = WpdsIncrementalSession::new(1);
        for p in 0..10 {
            s.record_checkpoint(p, cfg(p, WpdsState::Ready { min_bp: 0 }, 1));
        }
        s.clear();
        assert!(s.is_empty());
        assert_eq!(s.checkpoint_count(), 0);
    }

    #[test]
    fn is_convergent_matches_identical_configs() {
        let a: WpdsConfiguration<LexicographicWeight> = cfg(5, WpdsState::Ready { min_bp: 0 }, 2);
        let b = a.clone();
        assert!(WpdsIncrementalSession::is_convergent(&a, &b));
    }

    #[test]
    fn is_convergent_rejects_different_state() {
        let a: WpdsConfiguration<LexicographicWeight> = cfg(5, WpdsState::Ready { min_bp: 0 }, 2);
        let b: WpdsConfiguration<LexicographicWeight> =
            cfg(5, WpdsState::PrefixDispatch { pos: 5, cur_bp: 0 }, 2);
        assert!(!WpdsIncrementalSession::is_convergent(&a, &b));
    }

    #[test]
    fn is_convergent_rejects_different_stack() {
        let a: WpdsConfiguration<LexicographicWeight> = cfg(5, WpdsState::Ready { min_bp: 0 }, 2);
        let b: WpdsConfiguration<LexicographicWeight> = cfg(5, WpdsState::Ready { min_bp: 0 }, 3);
        assert!(!WpdsIncrementalSession::is_convergent(&a, &b));
    }

    #[test]
    fn is_convergent_rejects_different_position() {
        let a: WpdsConfiguration<LexicographicWeight> = cfg(5, WpdsState::Ready { min_bp: 0 }, 2);
        let b: WpdsConfiguration<LexicographicWeight> = cfg(7, WpdsState::Ready { min_bp: 0 }, 2);
        assert!(!WpdsIncrementalSession::is_convergent(&a, &b));
    }

    #[test]
    fn reparse_with_no_checkpoints_returns_no_checkpoint() {
        let s: WpdsIncrementalSession<LexicographicWeight> = WpdsIncrementalSession::new(1);
        let r = s.reparse(10, IdleEngine, 100, &empty_tokens());
        assert_eq!(r, Err(ReparseError::NoCheckpoint));
    }

    #[test]
    fn reparse_resumes_from_checkpoint() {
        // Engine that immediately accepts.
        struct AcceptEngine;
        impl WpdsStepEngine<LexicographicWeight> for AcceptEngine {
            fn step(
                &self,
                _state: &WpdsState,
                _gss: &WpdsGss<LexicographicWeight>,
                _frontier_top: Option<&WpdsGssNode>,
                _pos: usize,
                _tokens: &dyn WpdsTokenSource,
            ) -> WpdsStepAction<LexicographicWeight> {
                WpdsStepAction::Accept
            }
        }
        let mut s: WpdsIncrementalSession<LexicographicWeight> = WpdsIncrementalSession::new(1);
        s.record_checkpoint(5, cfg(5, WpdsState::Ready { min_bp: 0 }, 0));
        let r = s.reparse(8, AcceptEngine, 100, &empty_tokens());
        assert_eq!(r, Ok(WpdsState::Accepted));
    }

    #[test]
    fn reparse_propagates_engine_error() {
        struct ErrorEngine;
        impl WpdsStepEngine<LexicographicWeight> for ErrorEngine {
            fn step(
                &self,
                _state: &WpdsState,
                _gss: &WpdsGss<LexicographicWeight>,
                _frontier_top: Option<&WpdsGssNode>,
                _pos: usize,
                _tokens: &dyn WpdsTokenSource,
            ) -> WpdsStepAction<LexicographicWeight> {
                WpdsStepAction::Error("simulated".to_string())
            }
        }
        let mut s: WpdsIncrementalSession<LexicographicWeight> = WpdsIncrementalSession::new(1);
        s.record_checkpoint(0, cfg(0, WpdsState::Ready { min_bp: 0 }, 0));
        let r = s.reparse(0, ErrorEngine, 100, &empty_tokens());
        match r {
            Err(ReparseError::EngineFailed(msg)) => assert_eq!(msg, "simulated"),
            other => panic!("expected EngineFailed, got {:?}", other),
        }
    }

    #[test]
    fn iter_returns_checkpoints_in_order() {
        let mut s: WpdsIncrementalSession<LexicographicWeight> = WpdsIncrementalSession::new(1);
        for p in [10, 0, 5, 3, 7] {
            s.record_checkpoint(p, cfg(p, WpdsState::Ready { min_bp: 0 }, 1));
        }
        let positions: Vec<usize> = s.iter().map(|(p, _)| *p).collect();
        assert_eq!(positions, vec![0, 3, 5, 7, 10]);
    }

    /// Engine that performs `n` advances then accepts (driven via shared counter).
    struct AdvanceThenAccept {
        counter: RefCell<usize>,
        n: usize,
    }
    impl WpdsStepEngine<LexicographicWeight> for AdvanceThenAccept {
        fn step(
            &self,
            _state: &WpdsState,
            _gss: &WpdsGss<LexicographicWeight>,
            _frontier_top: Option<&WpdsGssNode>,
            _pos: usize,
            _tokens: &dyn WpdsTokenSource,
        ) -> WpdsStepAction<LexicographicWeight> {
            let mut c = self.counter.borrow_mut();
            if *c >= self.n {
                WpdsStepAction::Accept
            } else {
                *c += 1;
                WpdsStepAction::Advance(WpdsState::PrefixDispatch { pos: 0, cur_bp: 0 })
            }
        }
    }

    #[test]
    fn reparse_runs_engine_to_acceptance() {
        let engine = AdvanceThenAccept {
            counter: RefCell::new(0),
            n: 3,
        };
        let mut s: WpdsIncrementalSession<LexicographicWeight> = WpdsIncrementalSession::new(1);
        s.record_checkpoint(0, cfg(0, WpdsState::Ready { min_bp: 0 }, 0));
        let r = s.reparse(0, engine, 100, &empty_tokens());
        assert_eq!(r, Ok(WpdsState::Accepted));
    }

    #[test]
    fn typical_lsp_flow() {
        // Simulate: open file → record 10 checkpoints → user edits at pos 5 →
        // invalidate_after(5) → reparse from nearest checkpoint.
        let mut s: WpdsIncrementalSession<LexicographicWeight> = WpdsIncrementalSession::new(1);
        for p in 0..10 {
            s.record_checkpoint(p, cfg(p, WpdsState::Ready { min_bp: 0 }, 1));
        }
        assert_eq!(s.checkpoint_count(), 10);

        // User edits at position 5.
        s.invalidate_after(5);
        assert_eq!(s.checkpoint_count(), 6); // 0..=5 retained
        assert_eq!(s.checkpoint_at_or_before(5).map(|(p, _)| p), Some(5));

        // Reparse from checkpoint at 5.
        struct AcceptOnce;
        impl WpdsStepEngine<LexicographicWeight> for AcceptOnce {
            fn step(
                &self,
                _state: &WpdsState,
                _gss: &WpdsGss<LexicographicWeight>,
                _frontier_top: Option<&WpdsGssNode>,
                _pos: usize,
                _tokens: &dyn WpdsTokenSource,
            ) -> WpdsStepAction<LexicographicWeight> {
                WpdsStepAction::Accept
            }
        }
        let r = s.reparse(8, AcceptOnce, 100, &empty_tokens());
        assert_eq!(r, Ok(WpdsState::Accepted));
    }
}
