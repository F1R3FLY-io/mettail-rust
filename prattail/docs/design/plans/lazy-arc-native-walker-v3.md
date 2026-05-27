# Lazy Tomita Frontier Walker v3 — Fork-Arc-Emit Plan

**Date**: 2026-05-27
**Branch tip**: `7b2c11f`
**Supersedes**: `lazy-arc-native-walker.md` (v2) and `lazy-weight-guided-walker.md` (v1).
**Driver**: empirical apply_action_variant_histogram falsified v2's L2 target.

---

## 1. Diagnosis

`chain_50` apply_action histogram (walker-stats, 2026-05-27):
```
Fork                   = 450,198  (42.1%)  ← DOMINANT
Push                   = 391,509  (36.6%)  ← RESIDUAL after Substage 5 (broadcasts InfixCont/PrefixRule/LexAlt)
Pop                    = 153,907  (14.4%)
Advance                =  44,139  ( 4.1%)
ConsumeAndPush         =  17,981  ( 1.7%)
IterativeChainAbsorb   =  11,130  ( 1.0%)
```

**Fork + Push = 78.7% of apply_action volume.**

The real waste is per-arc materialization (`materialize_branch_cursor_from_arc` at `wpda_walker.rs:8088-8093`) — every arc becomes a full BranchCursor regardless of action class.

**Cohort cache: `inflight_collisions = 95.7%`** — already saturated; additional cohort caching cannot help. Remaining 4.3% spawns 413,147 cohort cursors → 1.07M apply_action calls (~2.6 per emitted cursor).

**The 21 `children.push(child)` sites at `wpda_walker.rs:5828-7390`** are the per-cohort-cursor amplifier.

**Single highest-impact lever**: eliminate per-arc materialization in the Fork arm by emitting `FrontierArc<W>` directly into the next `TomitaFrontierMap`. Sibling arcs at the same `TomitaKey` merge immediately via `register_arc_with_aggregation`'s lex-min ⊕.

**Projected**: 450K Fork calls × ~3 children avg = 1.35M arc emissions, Tomita-merge factor ~3× collapses to ~450K distinct arcs. Combined with L2a's extended Push broadcast: total apply_action volume drops from 1.07M → effectively 0 for chain-interior.

---

## 2. Redesign: Angle C (A first, then B)

### Angle A first — extend Substage 5 Push broadcast

Lower-risk extension (~300 LOC). Substage 5 already broadcasts Push for `InfixContinuation`, `PrefixRuleEntry`, `LexAltLiteral`. Add: `CategoryEntryRoot`, `CrossCatProjection`, `OptionalGroupAt`. Each needs side-effect handling moved per-arc:
- CategoryEntryRoot's sentinel synthesis — already shell-broadcastable (S5 line 8008 handles it).
- CrossCatProjection's `visited_dispatch` insert — per-arc Arc::make_mut on FrontierArc.visited_dispatch (already an im::OrdSet).
- OptionalGroupAt's `optional_scope_marks` push — per-arc Arc::make_mut on FrontierArc.optional_scope_marks.

### Angle B second — Fork-arm arc-emit (the dominant lift)

Higher-risk structural surgery (~700 LOC). Convert the 21 `children.push(child: BranchCursor)` sites to `next_frontier.register_arc_with_aggregation(key, shell, arc)`. The `allocate_fork_push_child` helper returns `(TomitaKey, FrontierArc<W>)` instead of `BranchCursor<W>`.

Critical insight: 95.7% inflight-collision rate means cohort dedup already happens at registration time. Converting Fork to arc-emit lets that same dedup absorb the 21 children siblings. Each Fork emitting N children where all share the same TomitaKey (common at chain workloads — siblings differ only in `weight` / `source_priority`) collapses to **one frontier node with N arcs**; `register_arc_with_aggregation` immediately ⊕-merges weight-equivalent siblings.

### step_fanout_v3 shape

```
ingest pre-step cursors → frontier (existing)
drain_current_generation → for each (key, node):
  engine.step(shell) → ONE action per shell (existing)
  classify_for_tomita_v3(action, edge_kind) →
    ObsInvariantOverArcs:
      - Push convergent EdgeKinds (5+3 = 6 kinds total): shell-broadcast (existing S5 + new L2a)
      - Pop with single-pred convergent kind: NEW (deferred to L3b if dominant)
      - Advance/Accept/Error/Idle: existing S6
    ObsDivergentOverArcs (Fork): NEW B path — synthesize FrontierArc per branch,
      register_arc_with_aggregation into next_frontier directly;
      DO NOT call apply_action_to_cursor at all.
    Other ObsDivergentOverArcs: existing per-arc materialize fallback.
```

---

## 3. Substage roadmap

| # | Title | LOC | Pre-gate (instrument BEFORE shipping) | Falsifier (Welch p<0.05 at chain_50/100/200) |
|---|-------|-----|---------------------------------------|----------------------------------------------|
| **L2a** | Extend S5 Push broadcast: CategoryEntryRoot + CrossCatProjection + OptionalGroupAt | ~300 | `push_kind_histogram` (NEW — mirror `pop_kind_histogram`) confirms ≥ 80% of 391K residual Push calls are in these 3 kinds. If <50% → re-target. | apply_action_calls drops ≥ 25% (1.07M → ≤ 800K); chain_500 RSS ≤ baseline; gauntlet 4206/0 |
| **L2b** | Extend `apply_obs_invariant_to_frontier` for OptGroupAbsent — conditional on residual after L2a | ~150 | post-L2a `apply_action_variant_histogram` shows OptGroupAbsent ≥ 5% of residual | apply_action_calls drops additional ≥ 10% |
| **L3** | Fork-arm arc-emit: convert `allocate_fork_push_child` to return `(TomitaKey, FrontierArc<W>)`; 21 sites switch from `children.push(child)` to `next_frontier.register_arc_with_aggregation(key, shell, arc)` | ~700 | `fork_arm_target_tomita_key_collision_histogram` (NEW): project destination TomitaKey of each child, measure dedup ratio. If projected merge factor < 2.0× → reconsider | apply_action_calls drops to ≤ 150K (-85% from baseline); chain_500 LEFT peak RSS ≤ 8 GB (-44%); gauntlet 4206/0 |
| **L4** | chain_10000 close: tune `evict_stale`, frontier eviction at step boundary, drain-vec capacity sizing; instrument `frontier_arc_peak_count` | ~200 | post-L3 `frontier_arc_peak_count` < 50K (~5 MB working set). If > 200K → arc explosion blocked. | **chain_10000 LEFT peak RSS < 500 MB**; chain_500 wins preserved (-30% wall, -33% RSS); gauntlet 4206/0 |

**Every substage**: ship ONLY if pre-gate confirms target volume. **No plan-defined-skip exits** — falsified gates trigger redesign, not exit.

---

## 4. Soundness argument

Each substage is a structural refactor of an existing path; the per-arc materialize fallback REMAINS as the residual handler.

- **L2a** mirrors Substage 5's pattern exactly (shell-level GSS push + per-arc weight broadcast + `cursor_resolution_check`). The three added EdgeKinds have side effects (root-sentinel synthesis, visited_dispatch insert, optional-scope mark) that need to be moved per-arc OR proven shell-shareable. CategoryEntryRoot's sentinel synthesis is already shell-broadcastable (S5 line 8008 handles it). CrossCatProjection's visited_dispatch insert moves to per-arc Arc::make_mut. OptionalGroupAt's optional_scope_marks push moves to per-arc Arc::make_mut.
- **L3 Fork arc-emit**: `allocate_fork_push_child`'s existing soundness already preserves per-arc state via the BranchCursor's heavy fields; emitting a FrontierArc instead of a BranchCursor is type-preserving — `materialize_branch_cursor_from_arc` is the inverse. Cohort cache paths (InflightCollision, ResolvedHit, FailedHit) remain in `allocate_fork_push_child` BEFORE the arc-emit, preserving 95.7% inflight-collision dedup.

Chain_500 wins preserved because L3 EXTENDS S5's broadcast surface — never narrows it.

---

## 5. Memory estimate at completion

- Per-arc: ~100 B measured (Substage 1.5+2.5 baseline). 11 small Copy fields + 6 Arc pointers @ 8 B each.
- Per-shell: ~64 B (Arc-shared across all arcs at the same TomitaKey).
- chain_10000 working-set: ~5000 active TomitaKeys × ~3 arcs × 100 B = **1.5 MB per step**.
- Cumulative arc allocations ~30M (10K chain × ~3000 arcs/step), freed at end-of-step `evict_stale`.
- GSS + SPPF + arena overhead: ~150-200 MB (linear in chain length, baseline at chain_500 = 8-10 MB × 20 = 160-200 MB).

**Projected chain_10000 peak RSS: 200-350 MB. Comfortably under 500 MB target.**

---

## 6. First-30-minutes concrete actions

1. Read `prattail/src/wpda_walker.rs:7949-8094` (existing S5 Push broadcast — exact template for L2a).
2. Read `prattail/src/wpda_walker.rs:11689-11744` (`allocate_fork_push_child` non-cohort tail — the BranchCursor allocation to convert to FrontierArc emit at L3).
3. Read `prattail/src/tomita_frontier.rs:540-600` (`register_arc_with_aggregation` — the merge contract L3 must satisfy).
4. Add `push_kind_histogram: [u64; 11]` walker stat mirroring `pop_kind_histogram` AND run chain_50 with walker-stats BEFORE writing L2a code — confirm CategoryEntryRoot + CrossCatProjection + OptionalGroupAt sum ≥ 80% of 391K residual Push.

---

## 7. Risk register

- **L2a CrossCatProjection risk**: `visited_dispatch` insert is per-cursor — shell-broadcast collapses cycle-defense distinctness. **Falsifier**: post-L2a gauntlet 4206/0; if cross-cat tests fail, per-arc the insert via Arc::make_mut on FrontierArc.visited_dispatch.
- **L2a OptionalGroupAt risk**: `optional_scope_marks` push is per-cursor. **Falsifier**: optional_group_smoke tests; broadcast must use per-arc Arc::make_mut on FrontierArc.optional_scope_marks.
- **L3 Fork arc-emit risk**: 21 sites each have subtly different child construction (recovery-fork prologue, lex-fork stamp, cohort_origin tagging). **Falsifier**: `fork_arm_arc_emissions_by_action_kind` exhaustive coverage check; ship one site at a time, gauntlet between each.
- **L3 cohort interaction risk**: `RegisterOutcome::ResolvedHit` returns N revived cursors (multi-packing). Arc-emit must register each as separate arc. **Falsifier**: phase-f13-cohort-ambiguity tests.
- **L4 risk**: arc count grows superlinearly at chain_10000 from poor TomitaKey merge factor. **Falsifier**: `frontier_arc_peak_count`; if > 200K at chain_500, blocked — redesign merge_disambiguator predicate.

---

## 8. Integration with prior work

- **L0 instrumentation** (shipped, uncommitted): residual-divergence diagnostic. Re-purpose to measure `apply_action_calls / arc_count` (the L4 gate).
- **L1 `BranchCursorThunk` module** (shipped, uncommitted): dead code; fallback substrate if arc-emit hits an unsolvable soundness obstruction.
- **L2 prep histograms** (shipped, uncommitted): `pop_kind_histogram` + `apply_action_variant_histogram` — both reusable.
- **Substage 5 Push broadcast**: L2a extends it (drop-in compatible).
- **Exp 14 Tomita per-arc** (shipped): infrastructure L3 builds on.
- **Exp 15 CPS scaffold**: `cursor_store.rs`, `cursor_id.rs` could be the parent-id-by-CursorId mechanism if needed at L3.
- **chain_10000 un-ignore from `7b2c11f`**: stays in tree; the "Protocol amendment 2026-05-27" gets superseded by L4 closure.
