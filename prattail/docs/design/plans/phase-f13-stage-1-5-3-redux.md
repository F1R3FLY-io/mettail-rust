# Phase F.13 H12 Stage 1.5.3-Redux — Cohort Cursor Tagging + ConfigKey Bucketing

**Status:** Plan agent design (2026-05-21). Successor to falsified tropical-delta design (Stage 1.5.3 original).

**Tip:** `7395b30` (working-tree partial revert).

## Mandate

Close `-3!` AND keep all 228 baseline tests passing. Preserve H12 chain_50/100/200 speedup. No env vars, no feature gates.

## Root cause (refined)

The dispatch cohort cache key `(pos, source_src_idx, inner_cur_bp)` is **under-specified** for what counts as "same sub-parse." Two cursors at the same key can have different RETURN CONTINUATIONS — different outer rules to fire afterwards (e.g., Branch A wants to fire `Fact`, Branch B wants to fire `Neg`).

Stage 1.5.2's cohort revive inherits `snap.worker_inner_state` from the worker, which encodes the worker's outer-rule continuation. The cohort member's distinct outer continuation is LOST — it inherits the worker's fire.

When the cohort revive cursor and Branch B's per-cursor cursor reach the same ConfigKey at later steps, `merge_equivalent_cursors` collapses them via lex-min. The winner's `sppf_stack.last() = S03` is the same SppfId (Symbol-dedup) but the LOSER's intent to fire its distinct outer rule is dropped — Branch B's distinct outer Packing never gets `intern_packing`'d.

## Approach N (recommended)

Tag every cohort-revived cursor with `cohort_origin: Option<DispatchKey>`. Extend `ConfigKey` to include `cohort_origin`. Cohort revives and per-cursor cursors bucket SEPARATELY in merge. Each survives to end-of-parse and gets realized independently.

**Graduation rule G2:** Cursor's `cohort_origin` clears when the cursor pops past the depth at which it was revived (`cursor.incoming_edge_stack.len() < cohort_revive_depth`).

## Schema changes

```rust
pub struct BranchCursor<W: SemiringRef> {
    // ... existing fields ...
    pub cohort_origin: Option<crate::dispatch_cohort::DispatchKey>,
    pub cohort_revive_depth: u32,
}

struct ConfigKey {
    state: WpdaState,
    node: GssNodeId,
    pos: usize,
    incoming_edge: Option<GssEdgeId>,
    collection_depth: usize,
    cohort_origin: Option<crate::dispatch_cohort::DispatchKey>,  // NEW
}
```

## Soundness

- Cohort revives with same origin still merge → H12 preserved.
- Cohort revives vs per-cursor → distinct buckets → both survive.
- Both reach Accepted → realize fanout over packings_of(S03) → both packings yield normal forms.

## Staging (4 commits)

1. **1.5.3R-a:** schema + propagation, no behavior change.
2. **1.5.3R-b:** revival sets tag + G2 graduation.
3. **1.5.3R-c:** ConfigKey integration — expected 6161/0.
4. **1.5.3R-d:** defensive hardening + stat counters.

## Effort: 3-4 days (HONEST)

- 1.5.3R-a: 4-6 hours.
- 1.5.3R-b: 3-4 hours.
- 1.5.3R-c: 1-2 hours + 0-4 hour perf-debug buffer.
- 1.5.3R-d + testing: 4-6 hours.
- Risk: 1-2 extra days if multi-cohort lineage requires `Vec<DispatchKey>` instead of `Option`.

## Fallback: Approach R

If N fails Gate-4 stress: 4-hour fallback to "bail out cohort sharing on multi-packing keys" (lose ~5% chain_50 speedup; keep `-3!` correct).

## Critical files

- `prattail/src/wpda_walker.rs` (BranchCursor, ConfigKey, merge_equivalent_cursors, revive_cohort_member_with_snapshot, allocate_fork_push_child, cursor_gss_pop_via_edge)
- `prattail/src/dispatch_cohort.rs`
- `prattail/src/automata/lex_weight.rs` (optional: revert TropicalDeltaWeight if Option B per §10 chosen)
- `prattail/src/wpda_session.rs` (optional: revert bound)
- `languages/tests/edge_case_tests.rs:1490`

## Test gates

- Gate 0: `-3!` PASS, `int_of_float_add` PASS.
- Gate 1: edge_case_tests 229/0.
- Gate 2: full languages crate ≥ 6161/0.
- Gate 3: chain_50/100/200 Welch t-test p<0.05 (preserved speedup).
- Gate 4: 100x isolated stress runs.
- Gate 5: rholang + proptest gauntlet.
