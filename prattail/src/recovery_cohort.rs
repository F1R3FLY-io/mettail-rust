//! Phase F.13 Task #117 (2026-05-23) — Recovery-Dispatch Cohort Sharing
//!
//! Analogue of H12 ([[dispatch_cohort.rs]]) for the recovery-dispatch
//! path. When N cursors land on the same PrefixDispatch dead-end at
//! the same `(pos, state_cat_src_idx, cur_bp)` triple within one
//! parse, the per-cursor baseline re-runs the full
//! `emit_recovery_fork` work (WFST
//! `find_best_recovery_contextual_with_config` + `viterbi_multi_step` +
//! branch synthesis + forward-progress filter).
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
//! The recovery work depends only on inputs represented by the key or on
//! parse-stable global inputs:
//!
//! | Input | Source | Cursor-specific? |
//! |-------|--------|-------------------|
//! | `pos` | dispatch key | NO (cache key) |
//! | `state_cat_src_idx` | dispatch key | NO (cache key) |
//! | `cur_bp` | dispatch key | NO (cache key) |
//! | `tokens` | walker's shared `WpdaTokenSource` | NO (walker-global) |
//! | `infra` + active recovery config | `LazyLock<RecoveryInfra>` + walker config | NO, via `infra_signature` |
//! | configured recovery depth class | walker's GSS + `RecoveryConfig` | NO (walker-global) |
//! | `runtime_view.frontier_top` | cursor GSS tip | YES, via `frame_kind_class` |
//!
//! Per-cursor state (`cursor.recovery_depth`, `cursor.visited_recovery`)
//! is still gated on the **consumer side** in `apply_action_to_cursor`'s
//! Fork arm AFTER the cohort returns the shared branches. The walker-global
//! `RecoveryConfig` is also observed during branch synthesis; in particular
//! `max_recovery_depth = 0` disables recovery before WFST/Viterbi work.
//!
//! ## Memory bound
//!
//! At most ONE entry per full `RecoveryDispatchKey`
//! `(pos, state_cat_src_idx, cur_bp, frame_kind_class, depth_class,
//! infra_signature)` per parse. The frame-kind, configured depth-class,
//! and infra-identity axes are deliberately part of the key because they
//! affect `RecoveryContext`, WFST costs, token projection, sync sets, and
//! therefore repair selection. Each entry holds a `Vec<ForkBranch<W>>` of
//! length ≤ `RECOVERY_FORK_MAX_BRANCHES` (recovery_dispatch.rs:36).

use crate::automata::semiring::SemiringRef;
use crate::recovery::{FrameKind, RecoveryConfig};
use crate::token_id::TokenId;
use crate::wpda_walker::ForkBranch;

/// Depth exceeds `RecoveryConfig::deep_nesting_threshold`.
pub const RECOVERY_DEPTH_CLASS_DEEP: u8 = 0b0001;
/// Depth is below `RecoveryConfig::shallow_depth_threshold`.
pub const RECOVERY_DEPTH_CLASS_SHALLOW: u8 = 0b0010;
/// Depth exceeds `RecoveryConfig::vpa_nesting_ceiling` when present.
pub const RECOVERY_DEPTH_CLASS_VPA_OVER: u8 = 0b0100;

/// Recovery-context frame class whose cost multipliers are neutral.
pub const RECOVERY_FRAME_CLASS_OTHER: u8 = 0;
/// Frame class that applies the infix-RHS skip multiplier.
pub const RECOVERY_FRAME_CLASS_INFIX_RHS: u8 = 1;
/// Frame class that applies the collection insert multiplier.
pub const RECOVERY_FRAME_CLASS_COLLECTION: u8 = 2;
/// Frame class that applies the group insert multiplier.
pub const RECOVERY_FRAME_CLASS_GROUP: u8 = 3;
/// Frame class that applies the mixfix substitute multiplier.
pub const RECOVERY_FRAME_CLASS_MIXFIX: u8 = 4;

/// Finite abstraction of `RecoveryContext.frame_kind` observed by recovery
/// cost multipliers. Variants outside these four special cases are
/// cache-equivalent: they do not affect branch synthesis, and emitted branches
/// do not carry the original frame kind.
#[inline(always)]
pub fn recovery_frame_kind_class(frame_kind: FrameKind) -> u8 {
    match frame_kind {
        FrameKind::InfixRHS => RECOVERY_FRAME_CLASS_INFIX_RHS,
        FrameKind::Collection => RECOVERY_FRAME_CLASS_COLLECTION,
        FrameKind::Group => RECOVERY_FRAME_CLASS_GROUP,
        FrameKind::Mixfix => RECOVERY_FRAME_CLASS_MIXFIX,
        FrameKind::Prefix
        | FrameKind::Postfix
        | FrameKind::Lambda
        | FrameKind::Dollar
        | FrameKind::CastWrap
        | FrameKind::Other => RECOVERY_FRAME_CLASS_OTHER,
    }
}

/// Finite abstraction of the exact GSS frontier size used by contextual
/// recovery. The WFST cost model only observes depth through these threshold
/// predicates, so exact depths in the same class are cache-equivalent.
#[inline(always)]
pub fn recovery_depth_class(depth: usize, config: &RecoveryConfig) -> u8 {
    let mut class = 0;
    if depth > config.deep_nesting_threshold {
        class |= RECOVERY_DEPTH_CLASS_DEEP;
    }
    if depth < config.shallow_depth_threshold {
        class |= RECOVERY_DEPTH_CLASS_SHALLOW;
    }
    if config
        .vpa_nesting_ceiling
        .is_some_and(|ceiling| depth > ceiling)
    {
        class |= RECOVERY_DEPTH_CLASS_VPA_OVER;
    }
    class
}

/// Exact finite observation of normalized `RecoveryConfig` fields that
/// influence recovery branch synthesis. Floating-point values are stored by
/// raw bits so equality and hashing are total and deterministic.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct RecoveryConfigSignature {
    pub skip_per_token_bits: u64,
    pub delete_cost_bits: u64,
    pub substitute_cost_bits: u64,
    pub insert_cost_bits: u64,
    pub swap_cost_bits: u64,
    pub max_skip_lookahead: usize,
    pub deep_nesting_threshold: usize,
    pub deep_nesting_skip_mult_bits: u64,
    pub shallow_depth_threshold: usize,
    pub shallow_depth_skip_mult_bits: u64,
    pub low_bp_threshold: u8,
    pub low_bp_skip_mult_bits: u64,
    pub collection_insert_mult_bits: u64,
    pub group_insert_mult_bits: u64,
    pub bracket_insert_mult_bits: u64,
    pub mixfix_substitute_mult_bits: u64,
    pub beam_width_bits: Option<u64>,
    pub vpa_nesting_ceiling: Option<usize>,
    pub max_recovery_depth: u8,
}

impl RecoveryConfigSignature {
    pub fn from_config(config: &RecoveryConfig) -> Self {
        let normalized_config = config.normalized_for_recovery_search();
        let config = &normalized_config;
        Self {
            skip_per_token_bits: config.skip_per_token.to_bits(),
            delete_cost_bits: config.delete_cost.to_bits(),
            substitute_cost_bits: config.substitute_cost.to_bits(),
            insert_cost_bits: config.insert_cost.to_bits(),
            swap_cost_bits: config.swap_cost.to_bits(),
            max_skip_lookahead: config.max_skip_lookahead,
            deep_nesting_threshold: config.deep_nesting_threshold,
            deep_nesting_skip_mult_bits: config.deep_nesting_skip_mult.to_bits(),
            shallow_depth_threshold: config.shallow_depth_threshold,
            shallow_depth_skip_mult_bits: config.shallow_depth_skip_mult.to_bits(),
            low_bp_threshold: config.low_bp_threshold,
            low_bp_skip_mult_bits: config.low_bp_skip_mult.to_bits(),
            collection_insert_mult_bits: config.collection_insert_mult.to_bits(),
            group_insert_mult_bits: config.group_insert_mult.to_bits(),
            bracket_insert_mult_bits: config.bracket_insert_mult.to_bits(),
            mixfix_substitute_mult_bits: config.mixfix_substitute_mult.to_bits(),
            beam_width_bits: config.beam_width.map(f64::to_bits),
            vpa_nesting_ceiling: config.vpa_nesting_ceiling,
            max_recovery_depth: config.max_recovery_depth,
        }
    }
}

/// Exact finite observation of the mutable `RecoveryWfst` fields that
/// influence recovery branch synthesis.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct RecoveryWfstSignature {
    pub token_ids: Vec<(String, TokenId)>,
    pub sync_tokens: Vec<TokenId>,
    pub prediction_discounts: Vec<(TokenId, u64)>,
    pub bracket_mismatch_ids: Vec<TokenId>,
    pub recursive_category: bool,
}

/// Exact finite observation of `RecoveryInfra` fields that influence recovery
/// branch synthesis and token projection.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct RecoveryInfraSignature {
    pub token_ids: Vec<(String, TokenId)>,
    pub sync_tokens: Vec<TokenId>,
    pub config: RecoveryConfigSignature,
    pub wfst: RecoveryWfstSignature,
}

/// Cache key for a recovery dispatch site.
///
/// Mirrors every recovery-context input observed by the synthesized
/// `Vec<ForkBranch<W>>`:
///
/// - `pos`, `state_cat_src_idx`, `cur_bp`: dispatch-site identity (same
///   triple as H12's `DispatchKey` modulo terminology).
/// - `frame_kind_class`: finite cost observation of
///   `derive_frame_kind(frontier_top)`. In `step_fanout`
///   (`wpda_walker.rs:6990`) `frontier_top` is per-cursor (derived from
///   `cursor.node`), NOT walker-global. The key separates only frame kinds
///   that can change recovery multipliers; neutral variants share a class.
/// - `depth_class`: finite threshold observation of `gss.frontier_size()`
///   under the active `RecoveryConfig`. Exact depth feeds
///   `RecoveryContext.depth`, but the configured multiplier logic only
///   observes these threshold predicates.
/// - `infra_signature`: finite observation of the `RecoveryInfra` inputs
///   used by branch synthesis (outer token projection map, Viterbi sync set,
///   recovery config fields observed by branch synthesis, and the nested
///   mutable `RecoveryWfst` observation). The generated path keeps
///   `dispatch_context` absent, so WFST follow contexts are deliberately
///   omitted until that input is wired into `WalkerRuntimeView`. Category
///   source index is already a top-level key component and is validated before
///   lookup; category names are diagnostic-only while no simulator is supplied.
///
/// All six fields together form the equivalence class under which
/// `emit_recovery_fork` is a pure function (modulo `tokens`, which is
/// walker-global and whose mutation clears this cache).
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct RecoveryDispatchKey {
    pub pos: usize,
    pub state_cat_src_idx: u16,
    pub cur_bp: u8,
    pub frame_kind_class: u8,
    pub depth_class: u8,
    pub infra_signature: RecoveryInfraSignature,
}

impl RecoveryDispatchKey {
    #[inline(always)]
    pub fn new(
        pos: usize,
        state_cat_src_idx: u16,
        cur_bp: u8,
        frame_kind_class: u8,
        depth_class: u8,
        infra_signature: RecoveryInfraSignature,
    ) -> Self {
        Self {
            pos,
            state_cat_src_idx,
            cur_bp,
            frame_kind_class,
            depth_class,
            infra_signature,
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
                },
                None => {
                    self.cache_hits_total += 1;
                    RecoveryCacheLookup::Hit { branches: entry.branches.clone() }
                },
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
        self.entries
            .insert(key, RecoveryCacheEntry { branches, error_msg });
        self.registrations_total += 1;
    }

    /// Human-readable summary of cache statistics. Mirrors
    /// `dispatch_cohort.rs`'s `write_summary`.
    pub fn write_summary(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let total_lookups =
            self.cache_hits_total + self.error_hits_total + self.registrations_total;
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
// adding `&mut RecoveryCohortCache<W>` / `&RecoveryConfig` parameters
// would require a wide ABI change. Instead, the walker stashes raw
// pointers to its own cache and active recovery config in thread-locals
// before each `engine.step` call; the codegen-emitted recovery path reads
// them back.
//
// Safety contract:
// - Only the walker writes (via the pin guards).
// - Only the generated recovery path reads (via the `with_active_*`
//   accessors below).
// - The pointers are valid only for the duration of their pin-guard
//   scopes; readers must not hold references beyond their own closures.
// - `W` is generic; the walker and the reader must agree on `W` at
//   the type level — guaranteed because both are codegen-emitted from
//   the same language definition.

use std::cell::Cell;

thread_local! {
    static RECOVERY_CACHE_PTR: Cell<*mut ()> = const { Cell::new(std::ptr::null_mut()) };
    static RECOVERY_CONFIG_PTR: Cell<*const RecoveryConfig> =
        const { Cell::new(std::ptr::null()) };
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

/// RAII guard for the active walker recovery config. Nestable; restores the
/// previous pointer on drop.
pub struct RecoveryConfigPinGuard {
    prev: *const RecoveryConfig,
}

impl RecoveryConfigPinGuard {
    #[inline]
    pub fn pin(config: &RecoveryConfig) -> Self {
        let raw = config as *const RecoveryConfig;
        let prev = RECOVERY_CONFIG_PTR.with(|cell| {
            let p = cell.get();
            cell.set(raw);
            p
        });
        Self { prev }
    }
}

impl Drop for RecoveryConfigPinGuard {
    fn drop(&mut self) {
        RECOVERY_CONFIG_PTR.with(|cell| cell.set(self.prev));
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
            let cache: &mut RecoveryCohortCache<W> =
                unsafe { &mut *(raw as *mut RecoveryCohortCache<W>) };
            Some(f(cache))
        }
    })
}

/// Codegen-side: borrow the currently-active walker recovery config. Returns
/// `None` outside a walker-pinned step, in which case generated recovery uses
/// the category-local infra default.
#[inline]
pub fn with_active_recovery_config<F, R>(f: F) -> Option<R>
where
    F: FnOnce(&RecoveryConfig) -> R,
{
    RECOVERY_CONFIG_PTR.with(|cell| {
        let raw = cell.get();
        if raw.is_null() {
            None
        } else {
            // Safety: the walker owns `recovery_config`; the raw pointer is
            // pinned only while the walker is synchronously inside a step
            // driver. Readers borrow only for this closure.
            let config: &RecoveryConfig = unsafe { &*raw };
            Some(f(config))
        }
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    fn test_infra_signature(_name: &str) -> RecoveryInfraSignature {
        RecoveryInfraSignature {
            token_ids: Vec::new(),
            sync_tokens: Vec::new(),
            config: RecoveryConfigSignature::from_config(&RecoveryConfig::default()),
            wfst: RecoveryWfstSignature {
                token_ids: Vec::new(),
                sync_tokens: Vec::new(),
                prediction_discounts: Vec::new(),
                bracket_mismatch_ids: Vec::new(),
                recursive_category: true,
            },
        }
    }

    #[test]
    fn key_construction() {
        let signature = test_infra_signature("Expr");
        let k = RecoveryDispatchKey::new(42, 3, 7, 0, 5, signature.clone());
        assert_eq!(k.pos, 42);
        assert_eq!(k.state_cat_src_idx, 3);
        assert_eq!(k.cur_bp, 7);
        assert_eq!(k.frame_kind_class, 0);
        assert_eq!(k.depth_class, 5);
        assert_eq!(k.infra_signature, signature);
    }

    #[test]
    fn frame_kind_class_collapses_neutral_variants() {
        assert_eq!(
            recovery_frame_kind_class(FrameKind::Prefix),
            recovery_frame_kind_class(FrameKind::Other),
            "Prefix and Other do not affect contextual recovery multipliers",
        );
        assert_eq!(recovery_frame_kind_class(FrameKind::Postfix), RECOVERY_FRAME_CLASS_OTHER);
        assert_eq!(recovery_frame_kind_class(FrameKind::Lambda), RECOVERY_FRAME_CLASS_OTHER);
        assert_eq!(recovery_frame_kind_class(FrameKind::Dollar), RECOVERY_FRAME_CLASS_OTHER);
        assert_eq!(recovery_frame_kind_class(FrameKind::CastWrap), RECOVERY_FRAME_CLASS_OTHER);
    }

    #[test]
    fn frame_kind_class_separates_multiplier_bearing_variants() {
        assert_ne!(
            recovery_frame_kind_class(FrameKind::InfixRHS),
            RECOVERY_FRAME_CLASS_OTHER,
            "InfixRHS applies a skip multiplier and must be keyed separately",
        );
        assert_ne!(
            recovery_frame_kind_class(FrameKind::Collection),
            RECOVERY_FRAME_CLASS_OTHER,
            "Collection applies an insert multiplier and must be keyed separately",
        );
        assert_ne!(
            recovery_frame_kind_class(FrameKind::Group),
            RECOVERY_FRAME_CLASS_OTHER,
            "Group applies an insert multiplier and must be keyed separately",
        );
        assert_ne!(
            recovery_frame_kind_class(FrameKind::Mixfix),
            RECOVERY_FRAME_CLASS_OTHER,
            "Mixfix applies a substitute multiplier and must be keyed separately",
        );
    }

    #[test]
    #[cfg(target_pointer_width = "64")]
    fn key_construction_preserves_positions_above_u32() {
        let signature = test_infra_signature("Expr");
        let low = RecoveryDispatchKey::new(0, 3, 7, 0, 5, signature.clone());
        let high = RecoveryDispatchKey::new((u32::MAX as usize) + 1, 3, 7, 0, 5, signature);

        assert_ne!(low, high, "recovery cohort cache keys must not truncate token positions",);
        assert_eq!(high.pos, (u32::MAX as usize) + 1);
    }

    #[test]
    fn depth_class_collapses_midrange_depths() {
        let config = RecoveryConfig::default();

        assert_eq!(
            recovery_depth_class(10, &config),
            recovery_depth_class(999, &config),
            "depths with the same configured threshold observations share a cache class",
        );
        assert_ne!(
            recovery_depth_class(9, &config),
            recovery_depth_class(10, &config),
            "the shallow-depth predicate is part of the cache class",
        );
        assert_ne!(
            recovery_depth_class(1001, &config),
            recovery_depth_class(999, &config),
            "the deep-depth predicate is part of the cache class",
        );
    }

    #[test]
    fn depth_class_observes_vpa_ceiling() {
        let config = RecoveryConfig {
            vpa_nesting_ceiling: Some(20),
            ..RecoveryConfig::default()
        };

        assert_eq!(
            recovery_depth_class(21, &config) & RECOVERY_DEPTH_CLASS_VPA_OVER,
            RECOVERY_DEPTH_CLASS_VPA_OVER,
        );
        assert_eq!(recovery_depth_class(20, &config) & RECOVERY_DEPTH_CLASS_VPA_OVER, 0);
    }

    #[test]
    fn empty_cache_returns_miss() {
        let mut cache: RecoveryCohortCache<crate::automata::lex_weight::LexicographicWeight> =
            RecoveryCohortCache::new();
        let k = RecoveryDispatchKey::new(0, 0, 0, 0, 0, test_infra_signature("Expr"));
        match cache.lookup(&k) {
            RecoveryCacheLookup::Miss => {},
            _ => panic!("expected Miss on empty cache"),
        }
        assert_eq!(cache.cache_hits_total, 0);
        assert_eq!(cache.registrations_total, 0);
    }

    #[test]
    fn insert_then_lookup_hit_for_branches() {
        let mut cache: RecoveryCohortCache<crate::automata::lex_weight::LexicographicWeight> =
            RecoveryCohortCache::new();
        let k = RecoveryDispatchKey::new(10, 1, 2, 0, 0, test_infra_signature("Expr"));
        cache.insert(k.clone(), Vec::new(), None);
        assert_eq!(cache.registrations_total, 1);
        match cache.lookup(&k) {
            RecoveryCacheLookup::Hit { branches } => {
                assert!(branches.is_empty());
            },
            other => panic!("expected Hit, got {:?}", std::mem::discriminant(&other)),
        }
        assert_eq!(cache.cache_hits_total, 1);
    }

    #[test]
    fn insert_then_lookup_error_hit_for_tombstone() {
        let mut cache: RecoveryCohortCache<crate::automata::lex_weight::LexicographicWeight> =
            RecoveryCohortCache::new();
        let k = RecoveryDispatchKey::new(20, 4, 5, 0, 0, test_infra_signature("Expr"));
        cache.insert(k.clone(), Vec::new(), Some("no recovery available at pos 20".to_string()));
        match cache.lookup(&k) {
            RecoveryCacheLookup::ErrorHit { msg } => {
                assert!(msg.contains("pos 20"));
            },
            other => panic!("expected ErrorHit, got {:?}", std::mem::discriminant(&other)),
        }
        assert_eq!(cache.error_hits_total, 1);
        assert_eq!(cache.cache_hits_total, 0);
    }

    #[test]
    fn clear_resets_entries_not_counters() {
        let mut cache: RecoveryCohortCache<crate::automata::lex_weight::LexicographicWeight> =
            RecoveryCohortCache::new();
        let k = RecoveryDispatchKey::new(0, 0, 0, 0, 0, test_infra_signature("Expr"));
        cache.insert(k.clone(), Vec::new(), None);
        let _ = cache.lookup(&k);
        cache.clear();
        assert_eq!(cache.entries.len(), 0);
        // Counters are cumulative across the walker's lifetime, intentionally.
        assert_eq!(cache.registrations_total, 1);
        assert_eq!(cache.cache_hits_total, 1);
        // After clear, subsequent lookup is Miss.
        match cache.lookup(&k) {
            RecoveryCacheLookup::Miss => {},
            _ => panic!("expected Miss after clear"),
        }
    }
}
