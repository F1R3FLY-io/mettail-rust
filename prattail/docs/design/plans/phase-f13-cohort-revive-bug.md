# Phase F.13 H12 Stage 1.3.1 — Cohort Revive Bug Analysis and Design

**Status:** Plan agent analysis (2026-05-21). Implementation deferred to Stage 1.3.1 (Task #138).

## Executive summary

The current `revive_cohort_member` (`prattail/src/wpda_walker.rs:~9183`) builds a resumed cursor by:
1. Starting from `member.return_frame` (cohort member's pre-dispatch snapshot).
2. Overwriting `weight = member.weight_at_dispatch`, `pending_packing_weight = W::one_ref()`, `pos = hi_pos`, `inner_state = worker_inner_state`.
3. Pushing the cached `symbol_id` onto `sppf_stack` and pushing `CategoryEntry(S)` onto GSS.

This is **structurally incorrect for at least 5 fields**. The correct semantics is "what would the per-cursor sub-parse have produced in THIS cursor?" — which for most state is "the same delta that the worker observed, applied to THIS cursor's pre-dispatch state."

The dominant transformation is identical for worker and cohort member because the sub-parse is dispatch-key-deterministic (Tomita-GLR's foundational identity). What differs are the *initial conditions* (cohort member's pre-dispatch state) and the *path-traversal artifacts* (cohort member's incoming_edge_stack identity, visited_dispatch entries this cursor accumulated).

The fix requires capturing **two new pieces** in `DispatchCacheEntry::Resolved`:
1. `worker_last_action_output_cat: Option<u16>` — the F.3b load-bearing field read by `apply_pop_body_to_cursor` at the `GroupingClosePreservingInner` resolution site.
2. `ppw_delta: PpwDelta<W>` — encodes whether the sub-parse fired ≥1 action (post = `W::one_ref() × residual`) or zero actions (post = `pre × branch_product`).

For Calculator's grammar (no cohort sub-parse leaves residual GSS frames; all crossed cats fire at least one action — IntLit, FloatLit, etc.), this collapses to simpler invariants. The `last_action_output_cat` field is the prime suspect for the float_cast_* failure.

**Bottom line recommendation: ship Stage 1.3 as infrastructure-only with the conservative fallthrough. Pursue Stage 1.3.1 as a separate research-grade fix** (~3-5 days of focused work) backed by an empirical capture-and-diff harness that compares worker vs would-be cohort cursor field-by-field across the full gauntlet. Do NOT enable ResolvedHit synthesis blind — the field-inheritance partition below is the correct skeleton but the LexicographicWeight algebra for `pending_packing_weight` requires symbolic verification.

---

## 1. Field-by-field partition

Notation:
- **W** = inherit from worker (the worker's post-sub-parse value).
- **C** = preserve from cohort member's pre-dispatch state (`member.return_frame`).
- **D** = set to a known default.
- **Δ** = apply the worker's *delta* (transformation) to the cohort member's pre-dispatch value.

| # | Field | Decision | Justification |
|---|---|---|---|
| 1 | `node: GssNodeId` | C + push | Cohort member retains its own GSS top. Revive pushes CategoryEntry(S). |
| 2 | `pos: usize` | W (= hi_pos) | Sub-parse advances pos from `pos_at_dispatch` to `hi_pos`. Dispatch-key-deterministic. |
| 3 | `weight: W` | **Δ** | `cohort_post = cohort.weight_at_dispatch ⊗ sub_weight`. Current code missing `× sub_weight`. Task #132. |
| 4 | `inner_state: WpdaState` | W (= `worker_inner_state`) | Cohort member must inherit identically so next walker step emits same Pop. Current code correct. |
| 5 | `recovery_deltas: Vec<BuilderDelta>` | C ⊕ Δ_w | Sub-parse may append entries on recovery. Float_cast_* doesn't exercise recovery. Decision: C. Add debug assert. Task #136. |
| 6 | `source_priority: u32` | C | Fork-arm tiebreak identity — must NOT be worker's. Current code correct. |
| 7 | `incoming_edge_stack: Vec<GssEdgeId>` | C + push | Cohort member's stack-suffix identity. MUST be its own. Revive adds new CategoryEntry edge. Current code correct. |
| 8 | `recovery_depth: u8` | C | Per-cursor recovery counter. Current code correct. |
| 9 | `visited_recovery: OrdSet` | C | Per-cursor recovery memoization. Current code correct. Task #134. |
| 10 | `visited_dispatch: OrdSet` | C (or Δ for nested) | Per-cursor cycle defense. CRITICAL EDGE CASE for nested cross-cat — float_cast_* doesn't hit this. Tasks #134, #133. |
| 11 | `sppf_stack: Arc<Vec<SppfId>>` | C + push(symbol_id) | Net effect of sub-parse on sppf_stack = +1 entry (the symbol_id). Current code correct. |
| 12 | `optional_scope_marks: Vec<usize>` | C | Sub-parse's start/finalize pair up. Net effect zero. Current code correct. |
| 13 | `binder_scope_marks: Vec<(u16, Vec<String>)>` | C | Net effect zero for non-binder sub-parses. Current code correct for float_cast_*. |
| 14 | `pending_packing_weight: W` | **Δ_ppw** | Tricky — see Capture Strategy §4. Current code uses W::one_ref() — correct for fire-paths, unsound for no-fire. |
| 15 | `collection_stack_depth: u8` | C ⊕ Δ_w | Sub-parse opens and closes collections pair-wise. Net effect zero for float_cast_*. |
| 16 | `sppf_collection_arena: Arc<Vec<Vec<SppfId>>>` | C | Per-cursor collection accumulator. Net effect on this Arc: zero (collections close before sub-parse ends). Current code correct. |
| 17 | `last_action_output_cat: Option<u16>` | **W (load-bearing)** | **PRIME SUSPECT** for float_cast_* failure. F.3b reads it at `wpda_walker.rs:9651`. Cohort member's pre-dispatch value differs from worker's post-fire value. Current code WRONG. Task #135. |

### Summary of changes from current to correct

| Field | Current revive | Correct revive |
|---|---|---|
| `weight` | `member.weight_at_dispatch` | `member.weight_at_dispatch.times_ref(&sub_weight)` |
| `pending_packing_weight` | `W::one_ref()` | `apply_ppw_delta(member.weight_at_dispatch_ppw, &ppw_delta)` |
| `last_action_output_cat` | inherited via `member.return_frame` | `worker_last_action_output_cat` — **NEW required cache field** |
| (others) | various | unchanged from current |

---

## 2. Correct `revive_cohort_member` design (Rust pseudo-code)

```rust
#[cfg(feature = "dispatch-cohort")]
fn revive_cohort_member(
    &mut self,
    member: crate::dispatch_cohort::CohortMember<W>,
    cached: &ResolvedSnapshot<W>,
    source_src_idx: u16,
    inner_cur_bp: u8,
) -> BranchCursor<W> {
    let mut cursor = member.return_frame;

    // Field 3: weight = pre-dispatch weight × sub_weight delta.
    cursor.weight = member.weight_at_dispatch.times_ref(&cached.sub_weight);

    // Field 14: ppw_delta application.
    cursor.pending_packing_weight = apply_ppw_delta(
        &member.weight_at_dispatch_ppw,
        &cached.ppw_delta,
    );

    // Field 11: push cached Symbol id.
    Arc::make_mut(&mut cursor.sppf_stack).push(cached.symbol_id);

    // Field 2: pos = hi_pos.
    cursor.pos = cached.hi_pos as usize;

    // Field 17 (CRITICAL): inherit worker's last_action_output_cat.
    cursor.last_action_output_cat = cached.worker_last_action_output_cat;

    // Field 1 + 7: push CategoryEntry(S) onto cohort member's own GSS.
    let cat_sym = StackSymbolV2::category_entry(source_src_idx);
    let kind = crate::gss::EdgeKind::CrossCatProjection {
        source_src_idx,
        inner_cur_bp,
    };
    let _ = self.cursor_gss_push_with_kind(
        &mut cursor,
        cat_sym,
        cached.pos_at_dispatch as usize,
        W::one_ref(),
        kind,
    );

    // Field 4: restore inner_state.
    cursor.inner_state = cached.worker_inner_state.clone();

    cursor
}

struct ResolvedSnapshot<W: SemiringRef> {
    symbol_id: SppfId,
    hi_pos: u32,
    pos_at_dispatch: u32,                       // NEW
    sub_weight: W,
    worker_inner_state: WpdaState,
    worker_last_action_output_cat: Option<u16>, // NEW (load-bearing)
    ppw_delta: PpwDelta<W>,                     // NEW
    #[cfg(debug_assertions)]
    worker_sub_parse_field_witness: SubParseWitness,
}

enum PpwDelta<W: SemiringRef> {
    Fired { residual: W },
    NoFire { multiplier: W },
}

fn apply_ppw_delta<W: SemiringRef>(pre: &W, delta: &PpwDelta<W>) -> W {
    match delta {
        PpwDelta::Fired { residual } => residual.clone(),
        PpwDelta::NoFire { multiplier } => pre.times_ref(multiplier),
    }
}
```

---

## 3. Invariant (formal)

For any cohort member `M` paused at `DispatchKey K = (P, S, B)` while worker `W` was running:

```
Let σ : BranchCursor → BranchCursor be the (state-monad) operation
"run the sub-parse for K starting from a cursor whose state-at-K
equals the input".

σ is functorial over the fields the cache claims are shared:
  σ(M_pre_dispatch) ≡_obs σ(W_pre_dispatch)
where ≡_obs identifies cursors whose subsequent observable behavior
(parse outcome, final SPPF, lex-min weight) is identical.

The cohort-revive operation R must satisfy:
  R(M, cache_of(σ(W_pre_dispatch))) ≡_obs σ(M_pre_dispatch)

That is: applying the cached worker delta to the cohort member's
pre-dispatch state must be observation-equivalent to running the
sub-parse on the cohort member directly.
```

Operationally: for every CrossCatProjection edge popped, before recording Resolved, compute the field-by-field diff between worker's pre-dispatch and worker's post-pop snapshots. The diff MUST be confined to the fields above. If any "preserve" field changed, BAIL on cohort sharing for that key (fall through). Debug-assertion guard.

---

## 4. Capture strategy

### New `DispatchCacheEntry::Resolved` fields

| New field | Captured at | Used by |
|---|---|---|
| `worker_last_action_output_cat: Option<u16>` | resolve() in cursor_gss_pop_via_edge | revive (field 17) |
| `ppw_delta: PpwDelta<W>` | resolve() — requires worker fires counter | revive (field 14) |
| `pos_at_dispatch: u32` | resolve() — node.pos at pop site | revive (field 1 GSS push pos) |

### Already captured (current Stage 1.3 schema)

- `symbol_id: SppfId`
- `hi_pos: u32`
- `sub_weight: W` (currently W::one_ref(); Task #132)
- `worker_inner_state: WpdaState`

### Walker-global side-effect fields (already shared)

- `self.sppf` (SPPF arena) — Symbol-dedup, idempotent.
- `self.gss` — disjoint cursor stacks.
- `self.sppf_symbol_terms` — Arc memo, idempotent.
- `self.sppf_predicate_arena` — append-only.

### Fires detection

Snapshot `self.sppf.packings_count()` at register; diff at resolve. If count increased, sub-parse fired ≥1.

---

## 5. Test plan

| Field | Test |
|---|---|
| `weight` (Δ) | A grammar where sub-parse Forks contribute non-one weights AND lex-min selects the survivor. |
| `last_action_output_cat` (W) | `comparison_after_cast_results::float_cast_eq`. Add unit test snapshotting field through "float(3) == 3.0". |
| `pending_packing_weight` (Δ) | Test with zero-fire sub-parse path (rare). Most float_cast_* paths fire at least the inner action. |
| `incoming_edge_stack` (C+push) | Recursive cross-cat: `int(float(3.0))`. |
| `visited_dispatch` (C or Δ) | `(int(3.14) + int(3.14)) == 6` — same key from two paths. |
| `sppf_stack` (C + push) | Any cross-cat-cast. |

### Regression gauntlet

1. Full 6166/0 with `--features dispatch-cohort` AND `RESOLVED_HIT_SYNTHESIS=1`.
2. 100× isolated runs of the 6 float_cast_* tests.
3. chain_50/100/200/1000 stats: ~90.7% resolved_hits captured by synthesis.
4. Welch's t-test on chain_50 walltime: p < 0.05.

### Debug-assertion guard

Behind `#[cfg(debug_assertions)]` in `cursor_gss_pop_via_edge` at resolve site: compare worker pre-dispatch to post-pop snapshots field-by-field. On any "preserve" field change, BAIL (mark entry Failed; paused members fall through to per-cursor).

---

## 6. Recommendation

**Ship Stage 1.3 as infrastructure-only (current state — `af2b434`).** Pursue Stage 1.3.1 as a separate research-grade fix (~3-5 days).

### What Stage 1.3.1 needs (concrete)

1. **Field-diff harness**: `WorkerSubParseSnapshot` capturing all 17 cursor fields; print histogram of mutations across the gauntlet under `--features dispatch-cohort,snapshot-diff`.
2. **LexicographicWeight algebra** (Task #132): proof or counterexample that `sub_weight = W::one_ref()` for cross-cat sub-parses.
3. **Per-cursor `fires_during_subparse`** counter: snapshot `sppf.packings_count()` at register and diff at resolve.
4. **`last_action_output_cat` propagation** (Task #135): direct test verification via `dbg!` in `apply_pop_body_to_cursor`'s GroupingClose resolution at `wpda_walker.rs:9651`.
5. **Stage 1.4 compose**: approach 4a (ghost-edge pop) may simplify revive substantially.

---

## 7. Critical files

- `prattail/src/dispatch_cohort.rs` — extend Resolved with `worker_last_action_output_cat`, `ppw_delta`, `pos_at_dispatch`.
- `prattail/src/wpda_walker.rs` — modify `cursor_gss_pop_via_edge` to capture new fields; modify `revive_cohort_member` per design; thread `ResolvedSnapshot` into `allocate_fork_push_child`; add debug-assertion bail guard.
- `languages/tests/edge_case_tests.rs` — float_cast_* tests are the smallest-falsification gauntlet.
- `prattail/src/sppf.rs` — Symbol-dedup at `intern_symbol:511-525`, Packing-dedup at `intern_packing:536-559` underpin Tomita-GLR sharing.
- `prattail/docs/design/plans/phase-f13-algorithmic-cross-cat-cohort.md` — update with Stage 1.3.1 spec.
