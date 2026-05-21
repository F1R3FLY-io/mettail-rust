# Phase F.13 H12 Stage 1.3.1 — Corrected Cohort Revive (Implementable)

**Status:** Plan agent design (2026-05-21). Supersedes `phase-f13-cohort-revive-bug.md` recommendation to defer.

## Executive summary

Two implementable bugs identified that together explain the 6 `comparison_after_cast_results::float_cast_*` failures:

- **Bug A — GSS push position mismatch.** Current revive pushes `CategoryEntry(S)` at `hi_pos`. Worker pushed at `pos_at_dispatch`. Mismatch breaks `merge_equivalent_cursors::ConfigKey` and the engine's `Unwinding-CategoryEntry` pred_kind read at `engine_impl.rs:449-451`.
- **Bug B — Weight delta forfeit.** Current revive sets `cursor.weight = member.weight_at_dispatch` (no sub-parse multiplication). The correct value is `member.weight_at_dispatch × sppf.symbol_weight_sum(symbol_id)` — the SPPF Symbol's aggregate weight is the LexicographicWeight-canonical sub-parse contribution.

Fallback hypothesis if A+B don't close failures: **H4 — engine's `_gss.edges_from(id).first()` GSS pred read is non-deterministic.** Requires engine.step signature change to pass cursor's own incoming edge.

## 1. The corrected `revive_cohort_member`

```rust
#[cfg(feature = "dispatch-cohort")]
fn revive_cohort_member(
    &mut self,
    member: crate::dispatch_cohort::CohortMember<W>,
    symbol_id: crate::sppf::SppfId,
    pos_at_dispatch: u32,
    hi_pos: u32,
    source_src_idx: u16,
    inner_cur_bp: u8,
    worker_inner_state: WpdaState,
    worker_last_action_output_cat: Option<u16>,
    worker_pending_packing_weight: W,
) -> BranchCursor<W> {
    let mut cursor = member.return_frame;

    // Bug B fix: weight = pre_dispatch × sub_parse_weight_delta.
    let symbol_weight_sum = self.sppf.symbol_weight_sum(symbol_id);
    cursor.weight = member.weight_at_dispatch.times_ref(&symbol_weight_sum);

    cursor.pending_packing_weight = worker_pending_packing_weight;
    cursor.last_action_output_cat = worker_last_action_output_cat;

    Arc::make_mut(&mut cursor.sppf_stack).push(symbol_id);
    cursor.pos = hi_pos as usize;

    // Bug A fix: push CategoryEntry at pos_at_dispatch (not hi_pos).
    let cat_sym = StackSymbolV2::category_entry(source_src_idx);
    let kind = crate::gss::EdgeKind::CrossCatProjection {
        source_src_idx,
        inner_cur_bp,
    };
    let _ = self.cursor_gss_push_with_kind(
        &mut cursor, cat_sym, pos_at_dispatch as usize, W::one_ref(), kind,
    );

    cursor.inner_state = worker_inner_state;
    cursor
}
```

## 2. SPPF helper

```rust
impl<W: SemiringRef> Sppf<W> {
    pub fn symbol_weight_sum(&self, id: SppfId) -> W {
        match self.node(id) {
            Some(SppfNode::Symbol { packings, .. }) => {
                let mut acc: Option<W> = None;
                for &p in packings.iter() {
                    if let Some(SppfNode::Packing { weight, .. }) = self.node(p) {
                        acc = Some(match acc {
                            None => weight.clone(),
                            Some(a) => a.plus_ref(weight),
                        });
                    }
                }
                acc.unwrap_or_else(W::one_ref)
            }
            _ => W::one_ref(),
        }
    }
}
```

## 3. Schema update — DispatchCacheEntry::Resolved

Add `pos_at_dispatch: u32`. Remove `worker_weight: W` (replaced by SPPF-derived `symbol_weight_sum`).

## 4. Test plan progression

1. Smallest falsification: `float_cast_eq`.
2. All 6 float_cast_*.
3. edge_case_tests (229).
4. Full languages (2110).
5. Full workspace (6166).
6. chain_50 Welch t-test, p<0.05.
7. Enable InflightCollision pause.
8. Remove `dispatch-cohort` feature gate (Stage 1.6 default-on).

## 5. Fallback hypotheses if Step 1 fails

- **H4** — engine's `.first()` GSS pred read at `engine_impl.rs:449-451`. Cohort's structural sharing with worker's CategoryEntry node exposes a latent non-determinism. Fix: pass cursor's own incoming_edge_stack.last() into engine.step.
- **H5** — SPPF Symbol weight_sum over-aggregation (failed Packings included).
- **H6** — `visited_dispatch` propagation for recursive cross-cat.
- **H7** — F.3b interaction (cohort's last_action_output_cat read by outer rule).

## 6. Critical files

- `prattail/src/wpda_walker.rs:9176-9227` — replace revive_cohort_member.
- `prattail/src/wpda_walker.rs:9691-9776` — update resolve call.
- `prattail/src/wpda_walker.rs:9030-9152` — enable ResolvedHit + InflightCollision.
- `prattail/src/dispatch_cohort.rs` — schema update.
- `prattail/src/sppf.rs` — add symbol_weight_sum.
- `macros/src/gen/runtime/wpda_codegen/engine_impl.rs:436-505` — H4 fallback.
