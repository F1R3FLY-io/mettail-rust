//! Phase F.13 Task #117 (2026-05-23) — Recovery-Dispatch Cohort Sharing
//!
//! Analogue of H12 ([[dispatch_cohort.rs]]) for the recovery-dispatch
//! path. When N cursors land on the same PrefixDispatch dead-end at
//! the same `(pos, state_cat_src_idx, cur_bp)` triple within one
//! parse, the per-cursor baseline re-runs the full
//! `emit_recovery_fork` work (WFST `find_best_recovery_contextual` +
//! `viterbi_multi_step` + branch synthesis + forward-progress filter).
//! This cache shares the resulting `Vec<ForkBranch<W>>` across cohort
//! members so the WFST search runs once per dispatch site instead of
//! once per cohort cursor.
//!
//! ## Why a separate cache (vs reusing `DispatchCohortCache`)
//!
//! H12's `DispatchCohortCache` is multi-state (`InFlight` / `Resolved`
//! / `Failed`) with worker snapshots, multi-packing fanout, and end-
//! of-step revive drain — all geared to the cross-cat sub-parse
//! semantics where the cohort's "answer" arrives asynchronously via
//! sibling-worker pops. Recovery dispatch is **synchronous**:
//! `emit_recovery_fork` returns a finished `Vec<ForkBranch<W>>` in one
//! call. There is no pause / resume / snapshot bookkeeping. The cache
//! collapses to a simple memoization table.
//!
//! ## Soundness
//!
//! The recovery work depends ONLY on inputs that are walker-global
//! (not per-cursor) at the dispatch site:
//!
//! | Input | Source | Cursor-specific? |
//! |-------|--------|-------------------|
//! | `pos` | dispatch key | NO (cache key) |
//! | `state_cat_src_idx` | dispatch key | NO (cache key) |
//! | `cur_bp` | dispatch key | NO (cache key) |
//! | `tokens` | walker's shared `WpdaTokenSource` | NO (walker-global) |
//! | `infra` | `LazyLock<RecoveryInfra>` per-category | NO (binary-global) |
//! | `runtime_view.gss.frontier_size()` | walker's GSS | NO (walker-global) |
//! | `runtime_view.frontier_top` | walker's GSS frontier | NO (walker-global) |
//!
//! Per-cursor state (`cursor.recovery_depth`, `cursor.visited_recovery`)
//! is gated on the **consumer side** in `apply_action_to_cursor`'s Fork
//! arm AFTER the cohort returns the shared branches. That gate is
//! identical with-or-without this cache.
//!
//! ## Memory bound
//!
//! At most ONE entry per `(pos, state_cat_src_idx, cur_bp)` triple per
//! parse. For Calculator (4 categories × ~50 token positions × ~4
//! binding powers = ~800 max entries); typical workload <20 entries.
//! Each entry holds a `Vec<ForkBranch<W>>` of length ≤
//! `RECOVERY_FORK_MAX_BRANCHES` (recovery_dispatch.rs:36).

use crate::automata::semiring::SemiringRef;
use crate::wpda_walker::ForkBranch;

/// Cache key for a recovery dispatch site.
///
/// Mirrors EVERY input to `WalkerRuntimeView::build_recovery_context`
/// that affects the synthesized `Vec<ForkBranch<W>>`:
///
/// - `pos`, `state_cat_src_idx`, `cur_bp`: dispatch-site identity (same
///   triple as H12's `DispatchKey` modulo terminology).
/// - `frame_kind_disc`: discriminant byte of `derive_frame_kind(frontier_top)`.
///   In `step_fanout` (`wpda_walker.rs:6990`) `frontier_top` is per-cursor
///   (derived from `cursor.node`), NOT walker-global — two cursors at the
///   same `(pos, cat, bp)` with different GSS-frame symbols produce
///   different `RecoveryContext.frame_kind` and therefore distinct WFST
///   recovery candidates.
/// - `frontier_size`: `gss.frontier_size()` — feeds `RecoveryContext.depth`.
///   Walker-global within a step but varies across steps; including it
///   ensures cross-step cache safety for the same `(pos, cat, bp)`.
///
/// All five fields together form the equivalence class under which
/// `emit_recovery_fork` is a pure function (modulo `tokens` and `infra`,
/// both walker-global and parse-stable; cleared at `walker.reset`).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct RecoveryDispatchKey {
    pub pos: u32,
    pub state_cat_src_idx: u16,
    pub cur_bp: u8,
    pub frame_kind_disc: u8,
    pub frontier_size: u32,
}

impl RecoveryDispatchKey {
    #[inline(always)]
    pub fn new(
        pos: usize,
        state_cat_src_idx: u16,
        cur_bp: u8,
        frame_kind_disc: u8,
        frontier_size: usize,
    ) -> Self {
        Self {
            pos: pos as u32,
            state_cat_src_idx,
            cur_bp,
            frame_kind_disc,
            frontier_size: frontier_size as u32,
        }
    }
}

/// Cached result of an `emit_recovery_fork` call. Either a finished
/// `Vec<ForkBranch<W>>` (the successful synthesis path) or a tombstone
/// containing the error message that `emit_recovery_fork` would have
/// surfaced (the no-recovery-available path).
pub struct RecoveryCacheEntry<W: SemiringRef> {
    pub branches: Vec<ForkBranch<W>>,
    pub error_msg: Option<String>,
}

impl<W: SemiringRef + Clone> Clone for RecoveryCacheEntry<W> {
    fn clone(&self) -> Self {
        Self {
            branches: self.branches.clone(),
            error_msg: self.error_msg.clone(),
        }
    }
}

/// Result of `RecoveryCohortCache::lookup`.
pub enum RecoveryCacheLookup<W: SemiringRef> {
    /// Cache hit with recovery branches — branches cloned for the caller.
    Hit { branches: Vec<ForkBranch<W>> },
    /// Cache hit with a no-recovery-available tombstone.
    ErrorHit { msg: String },
    /// First cohort member at this key — caller must compute and insert.
    Miss,
}

/// Per-parse cache shared across cohort members at the same recovery
/// dispatch site. Owned by `WpdaWalker`; cleared in `reset`.
pub struct RecoveryCohortCache<W: SemiringRef> {
    pub entries: rustc_hash::FxHashMap<RecoveryDispatchKey, RecoveryCacheEntry<W>>,
    /// Cumulative count of `insert` calls — one per cohort first member.
    pub registrations_total: u64,
    /// Cumulative count of `lookup` returning `Hit` — one per cohort follower.
    pub cache_hits_total: u64,
    /// Cumulative count of `lookup` returning `ErrorHit` — short-circuited
    /// no-recovery-available cohort follower.
    pub error_hits_total: u64,
}

impl<W: SemiringRef + Clone> RecoveryCohortCache<W> {
    #[inline(always)]
    pub fn new() -> Self {
        Self {
            entries: rustc_hash::FxHashMap::default(),
            registrations_total: 0,
            cache_hits_total: 0,
            error_hits_total: 0,
        }
    }

    /// Reset between parses. Counter values are preserved (they're
    /// cumulative across the walker's lifetime, useful for diagnostics);
    /// the entry table is cleared.
    #[inline(always)]
    pub fn clear(&mut self) {
        self.entries.clear();
    }

    /// Look up an existing entry. Returns `Hit` / `ErrorHit` with a
    /// cloned payload on cache hit, or `Miss` if the caller must
    /// compute and insert.
    pub fn lookup(&mut self, key: &RecoveryDispatchKey) -> RecoveryCacheLookup<W> {
        match self.entries.get(key) {
            Some(entry) => match &entry.error_msg {
                Some(msg) => {
                    self.error_hits_total += 1;
                    RecoveryCacheLookup::ErrorHit { msg: msg.clone() }
                }
                None => {
                    self.cache_hits_total += 1;
                    RecoveryCacheLookup::Hit {
                        branches: entry.branches.clone(),
                    }
                }
            },
            None => RecoveryCacheLookup::Miss,
        }
    }

    /// Insert a freshly-computed result. Should be called exactly once
    /// per key per parse, by the cohort's first member.
    pub fn insert(
        &mut self,
        key: RecoveryDispatchKey,
        branches: Vec<ForkBranch<W>>,
        error_msg: Option<String>,
    ) {
        self.entries.insert(
            key,
            RecoveryCacheEntry {
                branches,
                error_msg,
            },
        );
        self.registrations_total += 1;
    }

    /// Human-readable summary of cache statistics. Mirrors
    /// `dispatch_cohort.rs`'s `write_summary`.
    pub fn write_summary(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let total_lookups = self.cache_hits_total + self.error_hits_total + self.registrations_total;
        writeln!(f, "RecoveryCohortCache stats:")?;
        writeln!(f, "  active entries:   {}", self.entries.len())?;
        writeln!(f, "  registrations:    {}", self.registrations_total)?;
        writeln!(f, "  branch hits:      {}", self.cache_hits_total)?;
        writeln!(f, "  tombstone hits:   {}", self.error_hits_total)?;
        if total_lookups > 0 {
            let hit_rate =
                (self.cache_hits_total + self.error_hits_total) as f64 / total_lookups as f64;
            writeln!(f, "  hit rate:         {:.2}%", hit_rate * 100.0)?;
        }
        Ok(())
    }
}

impl<W: SemiringRef + Clone> Default for RecoveryCohortCache<W> {
    fn default() -> Self {
        Self::new()
    }
}

// ─── Thread-local cache pointer (codegen ↔ walker handshake) ──────────────
//
// The recovery dispatch is invoked from within `engine.step`
// (codegen-emitted at `engine_impl.rs:385-405`). The engine trait's
// `step` signature is fixed and shared by every generated parser, so
// adding a `&mut RecoveryCohortCache<W>` parameter would require a
// wide ABI change. Instead, the walker stashes a raw pointer to its
// own cache in a thread-local before each `engine.step` call; the
// codegen-emitted `emit_recovery_fork_cached` reads the pointer back.
//
// Safety contract:
// - Only the walker writes (via `with_active_cache`).
// - Only `emit_recovery_fork_cached` reads (via `with_active_cache_typed`).
// - The pointer is valid only for the duration of `with_active_cache`'s
//   inner closure; readers must not hold the reference beyond their
//   own scope.
// - `W` is generic; the walker and the reader must agree on `W` at
//   the type level — guaranteed because both are codegen-emitted from
//   the same language definition.

use std::cell::Cell;

thread_local! {
    static RECOVERY_CACHE_PTR: Cell<*mut ()> = const { Cell::new(std::ptr::null_mut()) };
}

/// Walker-side: pin the recovery cache pointer for the duration of
/// `f`, restoring the prior pointer afterward (nestable). Returns
/// `f`'s result.
///
/// The walker MUST call this around each `engine.step` invocation that
/// can trigger recovery dispatch (i.e., every step in the parse loop).
#[inline]
pub fn with_active_cache<W, F, R>(cache: &mut RecoveryCohortCache<W>, f: F) -> R
where
    W: SemiringRef + Clone,
    F: FnOnce() -> R,
{
    let raw = cache as *mut RecoveryCohortCache<W> as *mut ();
    let _guard = RecoveryCachePinGuard::pin(raw);
    f()
}

/// RAII guard equivalent to `with_active_cache` for use in code that
/// can't be wrapped in a closure (e.g. functions with early returns
/// across many branches). Caller passes a `*mut ()` pointer cast from
/// `&mut RecoveryCohortCache<W>`. The guard restores the prior
/// thread-local pointer on `Drop`.
///
/// # Safety
/// `raw` must either be null OR be a valid `&mut RecoveryCohortCache<W>`
/// cast as `*mut ()`, and must outlive the guard.
pub struct RecoveryCachePinGuard {
    prev: *mut (),
}

impl RecoveryCachePinGuard {
    #[inline]
    pub fn pin(raw: *mut ()) -> Self {
        let prev = RECOVERY_CACHE_PTR.with(|cell| {
            let p = cell.get();
            cell.set(raw);
            p
        });
        Self { prev }
    }
}

impl Drop for RecoveryCachePinGuard {
    fn drop(&mut self) {
        RECOVERY_CACHE_PTR.with(|cell| cell.set(self.prev));
    }
}

/// Codegen-side: read the currently-active cache pointer and call
/// `f` with a typed `&mut RecoveryCohortCache<W>`. Returns `None` if
/// no cache is active (recovery is invoked outside a
/// `with_active_cache` scope) — the caller should fall back to the
/// uncached `emit_recovery_fork`.
///
/// # Safety
/// The caller asserts that the active cache's element type matches
/// `W`. This is upheld at codegen by emitting both the walker's
/// `with_active_cache::<W>` and `with_active_cache_typed::<W>` with
/// the same `W` derived from the language definition.
#[inline]
pub fn with_active_cache_typed<W, F, R>(f: F) -> Option<R>
where
    W: SemiringRef + Clone,
    F: FnOnce(&mut RecoveryCohortCache<W>) -> R,
{
    RECOVERY_CACHE_PTR.with(|cell| {
        let raw = cell.get();
        if raw.is_null() {
            None
        } else {
            // Safety: the walker holds `&mut Self`, which owns the
            // cache; the raw pointer is a stable address valid for
            // the duration of `with_active_cache`'s scope. Readers
            // only borrow during their own closure, which is nested
            // inside that scope.
            let cache: &mut RecoveryCohortCache<W> = unsafe { &mut *(raw as *mut RecoveryCohortCache<W>) };
            Some(f(cache))
        }
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn key_construction() {
        let k = RecoveryDispatchKey::new(42, 3, 7, 0, 5);
        assert_eq!(k.pos, 42);
        assert_eq!(k.state_cat_src_idx, 3);
        assert_eq!(k.cur_bp, 7);
        assert_eq!(k.frame_kind_disc, 0);
        assert_eq!(k.frontier_size, 5);
    }

    #[test]
    fn empty_cache_returns_miss() {
        let mut cache: RecoveryCohortCache<crate::automata::lex_weight::LexicographicWeight> =
            RecoveryCohortCache::new();
        let k = RecoveryDispatchKey::new(0, 0, 0, 0, 0);
        match cache.lookup(&k) {
            RecoveryCacheLookup::Miss => {}
            _ => panic!("expected Miss on empty cache"),
        }
        assert_eq!(cache.cache_hits_total, 0);
        assert_eq!(cache.registrations_total, 0);
    }

    #[test]
    fn insert_then_lookup_hit_for_branches() {
        let mut cache: RecoveryCohortCache<crate::automata::lex_weight::LexicographicWeight> =
            RecoveryCohortCache::new();
        let k = RecoveryDispatchKey::new(10, 1, 2, 0, 0);
        cache.insert(k, Vec::new(), None);
        assert_eq!(cache.registrations_total, 1);
        match cache.lookup(&k) {
            RecoveryCacheLookup::Hit { branches } => {
                assert!(branches.is_empty());
            }
            other => panic!("expected Hit, got {:?}", std::mem::discriminant(&other)),
        }
        assert_eq!(cache.cache_hits_total, 1);
    }

    #[test]
    fn insert_then_lookup_error_hit_for_tombstone() {
        let mut cache: RecoveryCohortCache<crate::automata::lex_weight::LexicographicWeight> =
            RecoveryCohortCache::new();
        let k = RecoveryDispatchKey::new(20, 4, 5, 0, 0);
        cache.insert(k, Vec::new(), Some("no recovery available at pos 20".to_string()));
        match cache.lookup(&k) {
            RecoveryCacheLookup::ErrorHit { msg } => {
                assert!(msg.contains("pos 20"));
            }
            other => panic!("expected ErrorHit, got {:?}", std::mem::discriminant(&other)),
        }
        assert_eq!(cache.error_hits_total, 1);
        assert_eq!(cache.cache_hits_total, 0);
    }

    #[test]
    fn clear_resets_entries_not_counters() {
        let mut cache: RecoveryCohortCache<crate::automata::lex_weight::LexicographicWeight> =
            RecoveryCohortCache::new();
        let k = RecoveryDispatchKey::new(0, 0, 0, 0, 0);
        cache.insert(k, Vec::new(), None);
        let _ = cache.lookup(&k);
        cache.clear();
        assert_eq!(cache.entries.len(), 0);
        // Counters are cumulative across the walker's lifetime, intentionally.
        assert_eq!(cache.registrations_total, 1);
        assert_eq!(cache.cache_hits_total, 1);
        // After clear, subsequent lookup is Miss.
        match cache.lookup(&k) {
            RecoveryCacheLookup::Miss => {}
            _ => panic!("expected Miss after clear"),
        }
    }
}
