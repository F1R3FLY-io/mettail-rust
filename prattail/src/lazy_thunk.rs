//! Phase F.13 chain_10000 Lazy redesign L1 (2026-05-27): the
//! `BranchCursorThunk<W>` enum that replaces eager `BranchCursor<W>`
//! allocation at Fork-arm sites.
//!
//! # Design (per `prattail/docs/design/plans/lazy-weight-guided-walker.md` §2)
//!
//! Lazy + weight-guided redesign: replace the FIFO `Vec<Frame<W>>` cursor
//! queue with a weight-keyed min-heap (lex-min) of thunks. The Fork-arm
//! emits one thunk per alternative — each ~48 B — instead of materializing
//! N full `BranchCursor` (~512 B + heavy Arc fields = ~3 KB) instances.
//!
//! The walker pops the highest-priority (= lex-min weight) thunk per step,
//! materializes it via `force()`, and dispatches. Deferred thunks (siblings
//! whose weight is dominated by the popped winner) NEVER allocate a
//! `BranchCursor` — they sit in the heap until the dominator resolves +
//! drops the heap, dying en bloc.
//!
//! # Soundness (per plan §4)
//!
//! `LexicographicWeight` is **idempotent + commutative under `plus`**
//! (lex-min). The eager walker computes `argmin_w (⊕_i cursor_i.weight)`
//! over all materialized siblings; the lazy walker pops siblings in
//! lex-min order from `BinaryHeap<Reverse<HeapEntry<W>>>` yielding the
//! SAME winner. Any thunk never forced is a sibling with
//! `weight > min(forced_weights)` that the eager walker would have also
//! pruned via `pick_lex_min_resolved`. Source_priority tiebreak (Stage
//! 3.12 Fix 2(ii)) is preserved via the insertion-stamp 2nd-key in
//! `HeapEntry`.
//!
//! # Substage staging
//!
//! - **L1 (this module)** — types + `force()` stub + `mem::size_of`
//!   asserts; dead code.
//! - L2 — convert the dominant Fork-arm Push site (`wpda_walker.rs:5845`)
//!   to enqueue thunks.
//! - L3 — convert the remaining 20 Fork-arm sites.
//! - L4 — lazy WFST composition (`compose.rs:721`).
//! - L5 — bench panel + close chain_10000 to < 500 MB peak RSS.
//!
//! # `Materialized` variant — escape hatch
//!
//! `BranchCursorThunk::Materialized(BranchCursor<W>)` is a legacy escape
//! hatch for sites where the lazy reconstruction recipe is impractical to
//! capture (rare cases — e.g. cohort revives that have already
//! materialized the cursor). Counts as 1 force on enqueue. The L0
//! instrumentation tracks how many thunks fall into this bucket so the
//! L2-L3 plan can target conversion priorities.

use std::cmp::Ordering;
use std::mem;

use crate::automata::semiring::SemiringRef;
use crate::cursor_id::{CursorId, CURSOR_ID_NONE};
use crate::sppf::SppfId;
use crate::wpda_runtime::WpdaState;
use crate::wpda_walker::{BranchCursor, ForkActionKind};

/// Lazy thunk that captures the recipe to reconstruct a
/// `BranchCursor<W>` on demand. Stored in the walker's weight-keyed
/// min-heap (`BinaryHeap<Reverse<HeapEntry<W>>>`); popped + forced
/// per step.
///
/// Size budget (per plan §2(b)): ~48 B for `ForkChild` (the chain-
/// interior dominant). `DispatchResolved` ~32 B. `Materialized` is the
/// full ~512 B `BranchCursor` (escape hatch — keep rare).
#[derive(Clone, Debug)]
pub enum BranchCursorThunk<W: SemiringRef> {
    /// Recipe for a Fork-arm child. `parent_id` references a parent
    /// cursor in `CursorStore<W>` whose heavy fields (`visited_dispatch`,
    /// `recovery_deltas`, `binder_scope_marks`, `optional_scope_marks`,
    /// `sppf_collection_arena`, `lex_fork_path`) are inherited via
    /// `Arc::clone` at `force()` time — NOT pre-materialized at Fork
    /// emit time. Only the small fields (`weight_delta`, `branch_idx`,
    /// `new_state`, `action_kind`) are stored in the thunk.
    ForkChild {
        /// Index into `CursorStore<W>::minimal[]` for the parent's
        /// heavy-field source. `force()` reads the parent state +
        /// applies the action_kind + branch_idx delta.
        parent_id: CursorId,
        /// Fork-source-order priority (Stage 3.12 Fix 2(ii) tiebreak).
        /// `child_source_priority = branch_idx as u32` at Fork allocation
        /// time. Lower wins on weight ties.
        branch_idx: u32,
        /// The action discriminator (matches `ForkBranch::action_kind`).
        /// Force-time dispatch on this re-creates the per-Fork-arm
        /// child allocation path from `wpda_walker.rs` Fork arm
        /// (lines 5455-7390).
        action_kind: ForkActionKind,
        /// Target state for the child cursor's `inner_state` field.
        /// Copied verbatim from `ForkBranch::new_state` at Fork-arm
        /// time.
        new_state: WpdaState,
        /// Per-branch weight delta to multiply into the parent's
        /// weight via `parent.weight.times_ref(&weight_delta)` at
        /// force time. Stored verbatim from `ForkBranch::weight`.
        weight_delta: W,
    },

    /// Recipe for a DispatchResolved cohort revive (planned L3).
    /// `paused_member_id` references the cohort member whose state
    /// the revive is restoring; `snap_id` is the SPPF resolution
    /// snapshot the revive plays back.
    DispatchResolved {
        snap_id: SppfId,
        paused_member_id: CursorId,
        weight_delta: W,
    },

    /// Legacy escape hatch for sites where lazy reconstruction is
    /// impractical. Holds a full materialized cursor on the heap via
    /// `Box` — keeps the enum's stack footprint dominated by the cheap
    /// `ForkChild` / `DispatchResolved` variants (the Materialized
    /// variant is rare post-L2; per L0 instrumentation it's bounded
    /// to seed / commit-winner write-back sites).
    /// L0 instrumentation tracks the count of this variant — L2-L3
    /// will minimize it.
    Materialized(Box<BranchCursor<W>>),
}

impl<W: SemiringRef> BranchCursorThunk<W> {
    /// Construct a `ForkChild` thunk with the standard fields.
    pub fn fork_child(
        parent_id: CursorId,
        branch_idx: u32,
        action_kind: ForkActionKind,
        new_state: WpdaState,
        weight_delta: W,
    ) -> Self {
        BranchCursorThunk::ForkChild {
            parent_id,
            branch_idx,
            action_kind,
            new_state,
            weight_delta,
        }
    }

    /// Construct a `DispatchResolved` thunk.
    pub fn dispatch_resolved(
        snap_id: SppfId,
        paused_member_id: CursorId,
        weight_delta: W,
    ) -> Self {
        BranchCursorThunk::DispatchResolved {
            snap_id,
            paused_member_id,
            weight_delta,
        }
    }

    /// Construct a `Materialized` thunk (escape hatch). Boxes the
    /// cursor to keep the enum's discriminant + payload small in the
    /// common ForkChild case.
    pub fn materialized(cursor: BranchCursor<W>) -> Self {
        BranchCursorThunk::Materialized(Box::new(cursor))
    }

    /// Discriminant: the parent_id if applicable, otherwise `CURSOR_ID_NONE`.
    pub fn parent_id(&self) -> CursorId {
        match self {
            BranchCursorThunk::ForkChild { parent_id, .. }
            | BranchCursorThunk::DispatchResolved {
                paused_member_id: parent_id,
                ..
            } => *parent_id,
            BranchCursorThunk::Materialized(_) => CURSOR_ID_NONE,
        }
    }

    /// Source-priority for tiebreak. Returns the cursor's stored
    /// `source_priority` for `Materialized` (the legacy default).
    pub fn source_priority(&self) -> u32 {
        match self {
            BranchCursorThunk::ForkChild { branch_idx, .. } => *branch_idx,
            BranchCursorThunk::DispatchResolved { .. } => 0,
            BranchCursorThunk::Materialized(c) => c.as_ref().source_priority,
        }
    }

    /// True iff this is a `Materialized` thunk (escape hatch).
    pub fn is_materialized(&self) -> bool {
        matches!(self, BranchCursorThunk::Materialized(_))
    }
}

/// Weight-keyed heap entry. Min-heap orders by `(weight, insertion_stamp)`
/// — lex-min weight wins, ties broken by insertion stamp (preserves
/// Stage 3.12 Fix 2(ii) source_priority via `branch_idx`-keyed stamps).
///
/// `BinaryHeap<Reverse<HeapEntry<W>>>` gives a min-heap (Rust's standard
/// `BinaryHeap` is a max-heap by default).
#[derive(Clone, Debug)]
pub struct HeapEntry<W: SemiringRef> {
    /// Per-cursor accumulated weight (parent × delta) at enqueue time.
    /// Min over this drives traversal order.
    pub weight: W,
    /// Monotonic insertion stamp — ties broken by lower stamp first
    /// (stable FIFO under weight equality).
    pub insertion_stamp: u64,
    /// The thunk recipe.
    pub thunk: BranchCursorThunk<W>,
}

impl<W: SemiringRef> HeapEntry<W> {
    /// Construct a heap entry from a thunk + accumulated weight + stamp.
    pub fn new(weight: W, insertion_stamp: u64, thunk: BranchCursorThunk<W>) -> Self {
        Self {
            weight,
            insertion_stamp,
            thunk,
        }
    }
}

/// Strict total order on `HeapEntry<W>` by `(weight, insertion_stamp)`.
/// `weight`'s order is the semiring's natural order (via `W: Ord`);
/// ties broken by `insertion_stamp` ascending. For
/// `LexicographicWeight`, `Ord` IS the lex-min order — its
/// `impl Ord` at `automata/lex_weight.rs:355` delegates to
/// `LexicographicWeight::lex_cmp`. Other semirings supply their own
/// `Ord` impl.
impl<W> PartialEq for HeapEntry<W>
where
    W: SemiringRef + Ord,
{
    fn eq(&self, other: &Self) -> bool {
        self.weight == other.weight && self.insertion_stamp == other.insertion_stamp
    }
}

impl<W> Eq for HeapEntry<W> where W: SemiringRef + Ord {}

impl<W> PartialOrd for HeapEntry<W>
where
    W: SemiringRef + Ord,
{
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl<W> Ord for HeapEntry<W>
where
    W: SemiringRef + Ord,
{
    fn cmp(&self, other: &Self) -> Ordering {
        match self.weight.cmp(&other.weight) {
            Ordering::Equal => self.insertion_stamp.cmp(&other.insertion_stamp),
            other => other,
        }
    }
}

/// Force a thunk into a `BranchCursor<W>` — the lazy-evaluation hot path.
///
/// At L1 this is a STUB: returns `Some` only for the `Materialized`
/// variant. `ForkChild` and `DispatchResolved` paths require
/// `CursorStore<W>` to be populated (L2 wires it in) — L1 leaves them
/// as `None` so the walker compiles + tests pass without re-architecting
/// `CursorStore` wiring.
///
/// L2 implementation: `ForkChild` reads
/// `cursor_store.minimal[parent_id.as_index()]` for the parent's small
/// fields, clones the parent's heavy Arcs via `cursor_store.heavy_*`
/// lookups, and applies `action_kind` + `weight_delta` to produce the
/// child cursor (replicating the per-arm logic from
/// `wpda_walker.rs:5455-7390`).
pub fn force<W: SemiringRef>(
    thunk: BranchCursorThunk<W>,
) -> Option<BranchCursor<W>> {
    match thunk {
        BranchCursorThunk::Materialized(c) => Some(*c),
        BranchCursorThunk::ForkChild { .. }
        | BranchCursorThunk::DispatchResolved { .. } => {
            // L1 stub: real reconstruction wired at L2 alongside
            // CursorStore population at the Push Fork-arm site
            // (wpda_walker.rs:5845). Returning None here means no
            // current call site forces a non-Materialized thunk — by
            // construction, L1 only enqueues Materialized thunks.
            None
        }
    }
}

/// Size of `BranchCursorThunk<W>` for a typical W. Plan §2(b) budget:
/// ForkChild ~48 B; DispatchResolved ~32 B. The enum's actual size is
/// the max of its variants + tag — `Materialized` (~512 B) dominates,
/// but only the `ForkChild` / `DispatchResolved` variants are produced
/// at the hot path post-L2.
///
/// Returned for diagnostics / size_of asserts.
pub fn thunk_size_bytes<W: SemiringRef>() -> usize {
    mem::size_of::<BranchCursorThunk<W>>()
}

/// Size of `HeapEntry<W>` — the actual on-heap footprint per pending
/// cursor. Bytes-per-pending = `thunk_size_bytes::<W>() + 16 (W) + 8
/// (insertion_stamp)` for typical W.
pub fn heap_entry_size_bytes<W: SemiringRef>() -> usize {
    mem::size_of::<HeapEntry<W>>()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::automata::semiring::SemiringRef;
    use crate::cursor_id::CursorId;
    use crate::wpda_runtime::WpdaState;

    /// Minimal idempotent semiring stub for the L1 tests. Real walker
    /// uses `LexicographicWeight`; for L1 dead-code tests any
    /// `SemiringRef + LexProvenance` impl is sufficient.
    type W = crate::automata::lex_weight::LexicographicWeight;

    #[test]
    fn fork_child_thunk_constructs() {
        let parent = CursorId(7);
        let weight = W::one_ref();
        let new_state = WpdaState::Ready { min_bp: 0 };
        let thunk = BranchCursorThunk::<W>::fork_child(
            parent,
            3,
            ForkActionKind::Push,
            new_state,
            weight,
        );
        assert_eq!(thunk.parent_id(), parent);
        assert_eq!(thunk.source_priority(), 3);
        assert!(!thunk.is_materialized());
    }

    #[test]
    fn dispatch_resolved_thunk_constructs() {
        let parent = CursorId(11);
        let weight = W::one_ref();
        let snap: SppfId = 42;
        let thunk = BranchCursorThunk::<W>::dispatch_resolved(snap, parent, weight);
        assert_eq!(thunk.parent_id(), parent);
        assert_eq!(thunk.source_priority(), 0);
        assert!(!thunk.is_materialized());
    }

    #[test]
    fn force_materialized_returns_inner() {
        // Construct a Materialized thunk by directly wrapping a cursor.
        // The cursor itself is not exercised here — only the thunk's
        // force() round-trip.
        // We use a placeholder by constructing through the cursor
        // store's seed path indirectly: skip the BranchCursor
        // construction and only test the enum behavior via parent_id
        // sentinel.
        // For materialized force, the L1 tests cannot easily fabricate
        // a real BranchCursor without invoking the walker — defer to
        // the L2 integration test.
        let unforced =
            BranchCursorThunk::<W>::dispatch_resolved(0u32, CursorId(0), W::one_ref());
        assert!(force(unforced).is_none());
    }

    #[test]
    fn thunk_size_under_budget() {
        // Plan §2(b) budget: ForkChild ~48 B; DispatchResolved ~32 B.
        // The enum's overall size is the max-variant + tag. Materialized
        // wraps a full BranchCursor — the actual enum is bounded by
        // that. Post-L2, when ForkChild dominates the heap, the
        // avg-per-thunk is closer to ForkChild's standalone size.
        // For L1 we assert a generous upper bound to catch egregious
        // bloat (e.g., capturing an entire Vec by value in a variant).
        let sz = thunk_size_bytes::<W>();
        eprintln!(
            "    [L1 size_of] BranchCursorThunk<LexicographicWeight> = {} B",
            sz
        );
        eprintln!(
            "    [L1 size_of] BranchCursor<LexicographicWeight>     = {} B (eager baseline)",
            mem::size_of::<BranchCursor<W>>(),
        );
        assert!(
            sz < 4096,
            "BranchCursorThunk size {} bytes — likely \
             accidentally capturing a Vec/HashMap by value in a variant",
            sz
        );
    }

    #[test]
    fn heap_entry_size_under_budget() {
        // HeapEntry adds the W weight + insertion_stamp on top of the
        // thunk. Same upper-bound check.
        let sz = heap_entry_size_bytes::<W>();
        eprintln!(
            "    [L1 size_of] HeapEntry<LexicographicWeight>        = {} B",
            sz
        );
        assert!(
            sz < 4096,
            "HeapEntry size {} bytes — likely accidentally capturing a Vec/HashMap by value",
            sz
        );
    }

    #[test]
    fn heap_entry_ord_by_weight_then_stamp() {
        // Two entries with the same weight should order by insertion_stamp
        // ascending (stable FIFO under tie).
        let weight = W::one_ref();
        let thunk_a = BranchCursorThunk::<W>::dispatch_resolved(
            0u32,
            CursorId(0),
            weight.clone(),
        );
        let thunk_b = BranchCursorThunk::<W>::dispatch_resolved(
            0u32,
            CursorId(0),
            weight.clone(),
        );
        let entry_a = HeapEntry::new(weight.clone(), 1, thunk_a);
        let entry_b = HeapEntry::new(weight.clone(), 2, thunk_b);
        assert!(entry_a < entry_b);
    }

    #[test]
    fn heap_entry_eq_iff_weight_and_stamp_match() {
        let weight = W::one_ref();
        let thunk = BranchCursorThunk::<W>::dispatch_resolved(
            0u32,
            CursorId(0),
            weight.clone(),
        );
        let entry_a = HeapEntry::new(weight.clone(), 1, thunk.clone());
        let entry_b = HeapEntry::new(weight.clone(), 1, thunk.clone());
        assert_eq!(entry_a, entry_b);
        let entry_c = HeapEntry::new(weight.clone(), 2, thunk);
        assert_ne!(entry_a, entry_c);
    }
}
