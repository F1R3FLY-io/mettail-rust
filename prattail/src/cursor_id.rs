//! Phase F.13 chain_10000 Exp 15 Substage 1 (2026-05-27): CursorId
//! newtype for the CPS walker rewrite.
//!
//! Per `prattail/docs/design/plans/exp15-cps-trampolined-walker.md` §3.2:
//! the planned CPS rewrite replaces the per-cursor BranchCursor (~512 B
//! with 30+ fields including `Arc<FxHashSet<PackedDispatchConfig>>`
//! visited sets) with a walker-global `CursorStore` keyed by `CursorId`
//! (a recycled u32 handle). Cursors become small index handles; the
//! continuation queue carries `CursorId` references rather than full
//! cursor state.
//!
//! Substage 1 ships ONLY the type + recycle helpers as dead code; no
//! integration with the existing walker. Substage 2 introduces the
//! mirror-write feature gate that allocates a parallel CursorId at
//! each BranchCursor allocation.

use std::fmt;

/// Stable u32 handle for a per-parse cursor. Allocated via
/// `CursorIdAllocator::alloc`; recycled via the allocator's free-list
/// upon `retire`.
///
/// The sentinel `CURSOR_ID_NONE = u32::MAX` is used by reset / drained
/// initial state to denote "no cursor here". Live cursor ids are
/// `0..CursorIdAllocator::next_id` minus the free-list.
#[derive(Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub struct CursorId(pub u32);

impl CursorId {
    /// Read the underlying u32.
    #[inline(always)]
    pub fn as_u32(self) -> u32 {
        self.0
    }

    /// Read as `usize` for Vec indexing.
    #[inline(always)]
    pub fn as_index(self) -> usize {
        self.0 as usize
    }

    /// True iff this id is the sentinel.
    #[inline(always)]
    pub fn is_none(self) -> bool {
        self == CURSOR_ID_NONE
    }
}

impl fmt::Debug for CursorId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.is_none() {
            write!(f, "CursorId(NONE)")
        } else {
            write!(f, "CursorId({})", self.0)
        }
    }
}

impl fmt::Display for CursorId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.is_none() {
            write!(f, "c_none")
        } else {
            write!(f, "c{}", self.0)
        }
    }
}

/// Sentinel for "no cursor". `u32::MAX` matches the same convention as
/// `gss::GSS_NODE_NONE` and `path_tree_arena::STACK_ID_ROOT`.
pub const CURSOR_ID_NONE: CursorId = CursorId(u32::MAX);

/// Recycling allocator for `CursorId`s. Per the Exp 15 plan §3.2,
/// retired ids go into the free-list so Vec storage in
/// `CursorStore::minimal` does not grow without bound.
///
/// Invariant: allocated ids never exceed `u32::MAX - 1` (since
/// `u32::MAX` is the sentinel).
pub struct CursorIdAllocator {
    /// Next never-before-allocated id (monotonic counter).
    next_id: u32,
    /// Retired ids available for reuse.
    free_list: Vec<CursorId>,
    /// Cumulative count of `alloc` calls (stats).
    alloc_count: u64,
    /// Cumulative count of `retire` calls (stats).
    retire_count: u64,
    /// Peak live cursor count (= max of allocated minus retired at any
    /// instant — stats).
    peak_live: u32,
    /// Current live cursor count (allocated minus retired).
    live: u32,
}

impl Default for CursorIdAllocator {
    fn default() -> Self {
        Self::new()
    }
}

impl CursorIdAllocator {
    /// Construct an empty allocator.
    pub fn new() -> Self {
        Self {
            next_id: 0,
            free_list: Vec::new(),
            alloc_count: 0,
            retire_count: 0,
            peak_live: 0,
            live: 0,
        }
    }

    /// Reset to empty state (called from walker reset).
    pub fn clear(&mut self) {
        self.next_id = 0;
        self.free_list.clear();
        self.alloc_count = 0;
        self.retire_count = 0;
        self.peak_live = 0;
        self.live = 0;
    }

    /// Allocate a fresh cursor id. Reuses a free-list id if available;
    /// otherwise issues `next_id` and increments.
    ///
    /// Panics if `next_id` would reach `u32::MAX` (reserved sentinel).
    pub fn alloc(&mut self) -> CursorId {
        self.alloc_count = self.alloc_count.saturating_add(1);
        self.live = self.live.saturating_add(1);
        if self.live > self.peak_live {
            self.peak_live = self.live;
        }
        if let Some(id) = self.free_list.pop() {
            return id;
        }
        let id = CursorId(self.next_id);
        if self.next_id == u32::MAX - 1 {
            panic!(
                "CursorIdAllocator: id space exhausted at u32::MAX - 1; \
                 cannot allocate without colliding with CURSOR_ID_NONE sentinel"
            );
        }
        self.next_id = self.next_id.saturating_add(1);
        id
    }

    /// Retire an id so it goes back to the free-list. Idempotent: a
    /// double-retire is silently ignored (the free-list already
    /// contains the id; counting it twice would corrupt `live`).
    pub fn retire(&mut self, id: CursorId) {
        if id.is_none() {
            return;
        }
        // Cheap O(1) defense: refuse to push if obviously stale (live=0).
        if self.live == 0 {
            return;
        }
        self.free_list.push(id);
        self.retire_count = self.retire_count.saturating_add(1);
        self.live = self.live.saturating_sub(1);
    }

    /// Number of currently-live cursor ids (= allocated - retired).
    pub fn live_count(&self) -> u32 {
        self.live
    }

    /// Peak `live_count` observed since construction or last clear.
    pub fn peak_live(&self) -> u32 {
        self.peak_live
    }

    /// Total `alloc` calls.
    pub fn alloc_count(&self) -> u64 {
        self.alloc_count
    }

    /// Total `retire` calls.
    pub fn retire_count(&self) -> u64 {
        self.retire_count
    }

    /// Size of the free-list.
    pub fn free_list_len(&self) -> usize {
        self.free_list.len()
    }

    /// Maximum id ever assigned (= `next_id - 1`, or `u32::MAX` if no
    /// alloc has happened yet — caller should check `next_id == 0`).
    pub fn next_id(&self) -> u32 {
        self.next_id
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn cursor_id_sentinel_is_none() {
        assert!(CURSOR_ID_NONE.is_none());
        assert!(!CursorId(0).is_none());
        assert!(!CursorId(1).is_none());
    }

    #[test]
    fn cursor_id_display_format() {
        assert_eq!(format!("{}", CursorId(7)), "c7");
        assert_eq!(format!("{}", CURSOR_ID_NONE), "c_none");
        assert_eq!(format!("{:?}", CursorId(42)), "CursorId(42)");
        assert_eq!(format!("{:?}", CURSOR_ID_NONE), "CursorId(NONE)");
    }

    #[test]
    fn allocator_starts_empty() {
        let a = CursorIdAllocator::new();
        assert_eq!(a.live_count(), 0);
        assert_eq!(a.peak_live(), 0);
        assert_eq!(a.alloc_count(), 0);
        assert_eq!(a.retire_count(), 0);
        assert_eq!(a.free_list_len(), 0);
        assert_eq!(a.next_id(), 0);
    }

    #[test]
    fn alloc_returns_consecutive_ids() {
        let mut a = CursorIdAllocator::new();
        assert_eq!(a.alloc(), CursorId(0));
        assert_eq!(a.alloc(), CursorId(1));
        assert_eq!(a.alloc(), CursorId(2));
        assert_eq!(a.live_count(), 3);
        assert_eq!(a.peak_live(), 3);
        assert_eq!(a.alloc_count(), 3);
    }

    #[test]
    fn retire_returns_id_to_free_list() {
        let mut a = CursorIdAllocator::new();
        let id = a.alloc();
        assert_eq!(a.live_count(), 1);
        a.retire(id);
        assert_eq!(a.live_count(), 0);
        assert_eq!(a.free_list_len(), 1);
        assert_eq!(a.retire_count(), 1);
    }

    #[test]
    fn retire_then_alloc_reuses_id() {
        let mut a = CursorIdAllocator::new();
        let first = a.alloc();
        a.retire(first);
        let second = a.alloc();
        assert_eq!(first, second, "free-list reuse should reissue the same id");
    }

    #[test]
    fn retire_none_is_noop() {
        let mut a = CursorIdAllocator::new();
        let _ = a.alloc();
        a.retire(CURSOR_ID_NONE);
        assert_eq!(a.retire_count(), 0);
        assert_eq!(a.live_count(), 1);
    }

    #[test]
    fn retire_when_live_zero_is_noop() {
        let mut a = CursorIdAllocator::new();
        a.retire(CursorId(0));
        assert_eq!(a.retire_count(), 0);
    }

    #[test]
    fn peak_live_is_high_water_mark() {
        let mut a = CursorIdAllocator::new();
        let _ = a.alloc();
        let _ = a.alloc();
        let id = a.alloc();
        assert_eq!(a.peak_live(), 3);
        a.retire(id);
        assert_eq!(a.live_count(), 2);
        assert_eq!(a.peak_live(), 3, "peak should not regress on retire");
    }

    #[test]
    fn clear_resets_state() {
        let mut a = CursorIdAllocator::new();
        let _ = a.alloc();
        let _ = a.alloc();
        a.clear();
        assert_eq!(a.live_count(), 0);
        assert_eq!(a.peak_live(), 0);
        assert_eq!(a.alloc_count(), 0);
        assert_eq!(a.next_id(), 0);
        assert_eq!(a.alloc(), CursorId(0));
    }

    #[test]
    fn cursor_id_orderable() {
        assert!(CursorId(0) < CursorId(1));
        assert!(CursorId(5) < CURSOR_ID_NONE);
    }
}
