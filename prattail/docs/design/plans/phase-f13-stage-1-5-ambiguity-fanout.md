# Phase F.13 H12 Stage 1.5 — Ambiguity Fanout in DispatchCacheEntry

**Status:** Plan agent design (2026-05-21). Successor to Stage 1.3.1.

**Mission:** Safely enable cohort sharing for multi-packing Symbols (e.g., `-3!` → `Symbol(Int, 0, 3) = {Fact(-3), Neg(Fact(3))}`), unblocking the 13 failures gated off by Stage 1.3.1's conservative fallthrough.

## 1. Diagnosis

Stage 1.3.1 captures a single worker snapshot at the moment of the worker's pop. For single-packing sub-parses this is per-cursor-equivalent (verified across 6 `float_cast_*` tests). For multi-packing sub-parses, the per-cursor baseline path produces N cursors at end-of-sub-parse — one per Packing — each with its own `pending_packing_weight` and `weight`. Stage 1.3.1 squashes the divergence to a single cohort cursor; observably distinct from per-cursor baseline.

The cache currently no-ops on the SECOND worker's pop (because the entry is already Resolved). Stage 1.5 makes resolve APPEND snapshots across sibling workers, and end-of-step drain produces ONE revived cohort cursor per snapshot.

## 2. Design choice

- **A1 (chosen):** `Vec<WorkerSnapshot>` per Resolved entry.
- **B2 (chosen):** Deferred revival at end-of-step (after all sibling workers within the same step have appended snapshots).
- Per-packing weight: use `worker_pending_packing_weight` directly (not SPPF symbol_weight_sum) — it's the per-packing residual the Stage 1.3.1 schema already captures.

## 3. Schema diff

```rust
pub struct WorkerSnapshot<W: SemiringRef> {
    pub worker_inner_state: WpdaState,
    pub worker_last_action_output_cat: Option<u16>,
    pub worker_pending_packing_weight: W,
    pub worker_weight: W,
}

pub enum DispatchCacheEntry<W: SemiringRef> {
    InFlight {
        cohort_size: u32,
        pending_cohort: Vec<CohortMember<W>>,
        worker_snapshots: Vec<WorkerSnapshot<W>>,
        opened_at_step: u64,
    },
    Resolved {
        symbol_id: SppfId,
        hi_pos: u32,
        pos_at_dispatch: u32,
        worker_snapshots: Vec<WorkerSnapshot<W>>,
        resolution_step: u64,
        pending_cohort: Vec<CohortMember<W>>,
    },
    Failed,
}
```

## 4. Algorithm

- **register**: same as Stage 1.3.1; ResolvedHit returns the snapshots Vec; defensive bypass when `resolution_step != current_step`.
- **resolve**: extended to append snapshots from sibling workers; signals `FirstResolve` (schedule drain) vs `SnapshotAppended` (no-op) vs `NoOp`.
- **revive_cohort_member_with_snapshot**: takes one `WorkerSnapshot` + member; weight = `member.weight_at_dispatch.times_ref(&snap.worker_pending_packing_weight)`.
- **cursor_gss_pop_via_edge**: construct `WorkerSnapshot` at resolve site, no inline revive (deferred to end-of-step).
- **step_fanout**: at end-of-step (BEFORE merge_equivalent_cursors), iterate `pending_cohort_drain_keys` and emit `paused × snapshots` revived cursors.
- **allocate_fork_push_child**: returns `CohortAllocResult<W>` = `One`/`Many`/`None`; ResolvedHit emits `Many` with multi-snapshot fanout; InflightCollision emits `None` and pauses cohort.

## 5. Soundness

Per-cursor baseline `B(M)` = the multiset of cursors a cohort member `M` would produce by running the per-cursor (no-cohort) path. By Tomita-GLR / Symbol-dedup, `|B(M)| = |packings_of(SppfId)|`. Stage 1.5 produces the same multiset by capturing all worker snapshots and emitting one revived cursor per snapshot. Downstream merge collapses the cohort's revived multiset to the same shape as `B(M)` because `ConfigKey` equivalence ignores `pending_packing_weight` and `weight`.

## 6. Edge cases

- N ≥ 3 packings: fanout × paused; bounded by `merge_equivalent_cursors` collapse.
- Late workers (different step): defensive bypass via `late_worker_bypass_total` counter.
- Failed sub-parse: terminal `worker_inner_state` filtered out at drain time.
- Recursive cross-cat: nested keys handled independently.
- Zero-fire sub-parse: `witness_packing_id = None`, fallback to `symbol_weight_sum`.

## 7. Implementation staging (4 commits)

1. **Stage 1.5.0** — schema-only refactor. Behavior identical.
2. **Stage 1.5.1** — end-of-step drain, single-snapshot. Multi-packing tests still broken; architecture shifted.
3. **Stage 1.5.2** — multi-snapshot fanout. 13 broken tests pass; ResolvedHit enabled.
4. **Stage 1.5.3** — InflightCollision pause enabled. Full H12 active.

## 8. Risk register

1. **Per-packing weight aliasing.** Use `worker_pending_packing_weight` (captured at resolve time, before any subsequent `intern_packing` `⊕`-aggregation).
2. **Worker terminal state divergence.** Filter terminal snapshots at drain time.
3. **Drain timing.** Place drain at exactly the same point as Stage 1.3.1's `pending_cohort_revives` flush (BEFORE `merge_equivalent_cursors`).

## 9. Test plan

- Smallest falsification: `postfix_binds_tighter_than_unary` (-3!).
- 12 broken calculator multi-packing tests.
- chain_50 Welch's t-test for H12 speedup (p < 0.05).
- chain_10000 sanity.
- Stage 1.6 default-on with feature gate removed.
