# Cohort Origin Quotient (COQ) — chain_10000 architectural fix

**Date**: 2026-05-27
**Branch tip**: `c0a78f9`
**Supersedes**: prior lazy-redesign plans for the chain_10000 close. L2a (CategoryEntryRoot Push broadcast) shipped a 36% constant-factor win; COQ addresses the **exponent** (N^2.16 apply_action scaling).
**Driver**: Plan agent v4 super-linear scaling root-cause diagnosis after empirical chain_500 measurement at commit `c0a78f9`.

---

## 1. Root cause of super-linear scaling

**The culprit**: `cohort_origin: Option<DispatchKey>` is a per-cursor `ConfigKey` discriminator. The `DispatchKey` includes `pos: u32`. Every chain element creates a fresh DispatchKey at a fresh `pos`, so post-revive cursors at chain step N have unique `cohort_origin` vs N-1, N-2, etc. `merge_equivalent_cursors` cannot collapse cohort-revived cursors across chain depths.

**Cite-by-line evidence:**

- `prattail/src/wpda_walker.rs:1976-1987` — `ConfigKey.cohort_origin` is load-bearing: "Two cursors at the same `(state, node, pos, edge, depth)` bucket SEPARATELY when their cohort_origin differs."
- `prattail/src/dispatch_cohort.rs:49-54` — `DispatchKey { pos: u32, source_src_idx, inner_cur_bp }`. **The `pos: u32` axis makes every chain element generate a fresh key**.
- `prattail/src/wpda_walker.rs:11689-11745` — `RegisterOutcome::ResolvedHit` re-pauses synthetic members AND revives N×snapshot cursors. Revives carry `cohort_origin: Some(DispatchKey {pos: N, ...})` — differs at every chain depth N.
- `prattail/src/wpda_walker.rs:8345-8440` — end-of-step cohort drain emits one revival per (paused_member × snapshot) pair. `pending_members` cap per-key=16, but the **number of KEYS grows linearly in chain depth**, so global pending population grows O(N).

**Math** (chain_50 → chain_500):
- chain_50: 433K cohort_cursors_emitted ÷ 691 steps = ~627 per step; ~50 distinct cohort_origin buckets surviving merge
- chain_500: 26.4M cohort_cursors_emitted ÷ 6,912 steps = ~3,820 per step; ~500 distinct buckets

Per-step cohort grows linearly in N because the discriminator set grows linearly in N. Combined with avg_merge_factor 2.97× (constant), cumulative apply_action = O(N) per step × N steps = **O(N²)** → matches the observed 146× factor (close to N² = 100×; extra from visited_dispatch HAMT depth growing as O(log N)).

---

## 2. The single architectural fix: COQ (Cohort Origin Quotient)

**Make cohort_origin's equivalence relation drop the `pos` axis.** Keep the cache keyed on `pos` for in-flight bookkeeping; make `ConfigKey` equality use only `(source_src_idx, inner_cur_bp)` via a new `EquivKey` quotient. Plus aggressive G2 graduation: clear `cohort_origin` once SPPF packing observation occurs (not when GSS frame exits — current `wpda_walker.rs:11898` is too late).

**Cohort math**: at chain_500, registrations=110M with 98.5% inflight_collisions reduces to 1.6M resolved_hits. The 26.4M `cohort_cursors_emitted` = resolved_hits × snapshots × paused_members. If `cohort_origin` quotients to a single equivalence class per `(source_src_idx, inner_cur_bp)` pair (Calculator chain has ONE such pair: `(0, 0)`), then **all 26.4M cohort cursors collapse to ONE merge bucket per step** modulo lex/sppf divergence. Post-merge frontier becomes O(grammar size) per step = **O(1)** for chain workloads.

**Why this addresses the EXPONENT, not the constant:** the cohort cache's 95.7-98.5% inflight_collisions stat hides that the CACHE has linearly-growing distinct keys. After COQ, the *equivalence relation* for ConfigKey merge collapses across keys at all `pos` values — post-merge frontier at every step is bounded by `|EquivKey| × |grammar slot| × |GSS-tip| × |SPPF-stack-baseline|`, all O(1) in chain length. Cumulative apply_action falls from O(N²) to **O(N)**.

LOC budget: ~600-800 LOC across 5 substages.

---

## 3. Substage roadmap

| # | Title | LOC | Pre-gate | Falsifier |
|---|-------|-----|----------|-----------|
| **COQ-S0** | Instrumentation: `cohort_origin_distinct_per_step_histogram` + `cohort_origin_equivkey_collision_rate` walker stats | ~120 | n/a — feature-gated | Gate FIRES iff chain_50 has `distinct_cohort_origin_per_step` median ≥ 5 AND `equivkey_collision_rate` ≥ 95%. If equivkey collision < 90%, COQ blocked; re-target. |
| **COQ-S1** | Split DispatchKey → `CacheKey` + `EquivKey` types; `ConfigKey` reads `cohort_origin.equiv()` | ~280 | S0 confirms equivkey collision ≥ 95% | apply_action_calls drops ≥ 50% chain_50 AND ≥ 80% chain_500; gauntlet 4213/0; chain_500 RSS ≤ 8 GB |
| **COQ-S2** | Aggressive G2 graduation: clear `cohort_origin` at first `emit_fire_action` consumption of cohort revive's SPPF packing | ~150 | S1 confirms `cohort_cursors_graduated / cohort_cursors_emitted ≤ 0.05` | per-step `branch_cursors_peak_pre_merge` drops ≥ 80%; chain_500 wall ≤ 4 min |
| **COQ-S3** | `TomitaShell.cohort_origin → EquivKey`; `merge_disambiguator` at `tomita_frontier.rs:295-305` reads EquivKey | ~100 | S2 confirms per-step Tomita merge factor ≥ 30× at chain_500 (current: 2.97×) | chain_10000 LEFT-assoc < 2 GB peak RSS, runs to completion in < 30 min wall; gauntlet 4213/0 |
| **COQ-S4** | Close chain_10000: tune `evict_stale` (TomitaFrontierMap) + `pending_members` cap (now O(1) per EquivKey) + `sppf_reclaim_gate` (36.1% of windows have ≥12.5% reclaimable but the gate refuses to fire) | ~150 | S3 confirms `frontier_arc_peak_count < 5K` | **chain_10000 LEFT-assoc < 500 MB peak RSS**; chain_500 wall ≤ 3 min; gauntlet 4213/0 |

Every substage ships ONLY if the empirical pre-gate confirms the target. **No plan-defined skips.**

---

## 4. Soundness argument

**COQ-S1**: Exp 11 S0 measured 100% of chain Forks dispatch a single `(source_src_idx=0, inner_cur_bp=0)` pair. The `pos` axis of `DispatchKey` distinguishes **dispatch sites**, not **observational equivalence**. Two cursors with the same `(state, node, pos, edge, depth, sppf_top)` but different `cohort_origin.pos` are produced by structurally equivalent paths through the same grammar slot — engine's `step` function is pure of cursor state at every dispatch site (`tomita_frontier.rs:60-65`), so they receive the same action.

Their SPPF packing distinctions (the `-3!` rationale at line 1999-2005) are carried by `sppf_top`, which COQ does **NOT** touch. The cohort-revive `worker_pending_packing_weight` per-packing distinction (`dispatch_cohort.rs:80-97`) is carried by `WorkerSnapshot`, which COQ does **NOT** touch.

**COQ-S2**: graduation is sound because SPPF Symbol-dedup at `(nt, lo, hi)` already aggregates per-packing weights via `link_packing_to_symbol`. Once a cohort revive's fire is observed by `emit_fire_action`, downstream merges can safely ignore the dispatch origin — algebraic distinction has been recorded in the SPPF.

Gauntlet 4213/0 must hold at every substage; falsifier is one regression.

---

## 5. Memory + time estimate at completion

- COQ-S1: per-step cohort O(N) → O(grammar_size) ≈ 5-20 buckets for Calculator chain. apply_action_calls drops 50-80× at chain_500.
- COQ-S2: aggressive graduation eliminates O(N) accumulation of cohort_origin-tagged cursors across steps. Cumulative cursors_created_via_fork drops 10×.
- COQ-S3: TomitaFrontierMap merge factor jumps from 2.97× → 30-100× because previously-distinct cohort-tagged cursors share TomitaKey.
- **COQ-S4 projection**: chain_10000 working set ≈ 5,000 active EquivKey × ~3 arcs × 100 B/arc = **1.5 MB per step**. GSS+SPPF arena 100-200 MB linear in chain length. **Peak RSS: 250-450 MB. Wall: ~5-15 min** (vs current projected 6.7 days under super-linearity).

---

## 6. First-30-minutes actions

1. Read `prattail/src/dispatch_cohort.rs:49-65` (DispatchKey + EquivKey split design surface).
2. Read `prattail/src/wpda_walker.rs:1976-2006` (ConfigKey.cohort_origin + sppf_top discriminator).
3. Read `prattail/src/wpda_walker.rs:11842-11920` (revive_cohort_member_with_snapshot + G2 graduation).
4. Add `cohort_origin_distinct_per_step_histogram` + `cohort_origin_equivkey_collision_rate` walker stats. Run chain_50 and chain_500 LEFT-assoc with walker-stats. Confirm distinct cohort_origin per step grows linearly with N AND equivkey collision rate ≥ 95%.

---

## 7. What NOT to do

- **Do not add more cohort caching** — cache at 98.5% inflight_collisions; the cohort cache is NOT the bottleneck, the **post-revive ConfigKey discriminator** is.
- **Do not propose Earley/CYK/LR/PEG substitution** (user mandate).
- **Do not propose more L2a-style Push-broadcast extensions** (L2a + Substage 5 + 6 already captured the constant-factor gains; the exponent is unmoved).
- **Do not propose `MAX_PENDING_COHORT_PER_KEY` raises** (cap=256 was tried in Stage L6 ledger entry, blew up to 22 GB at chain_10000 in 2:54).
- **Do not propose dropping `incoming_edge` or `sppf_top` from ConfigKey** (Exp 10 S1 REJECT: chain_1000 +7.4% LOSS).
- **Do not propose streaming SPPF / GSS reclamation** as the primary fix (Exp D-E4 S1.a DATA-CONCLUDED: chain_1000 cache_pinned=99.8%, cohort-cache pins SPPF positions, streaming futile until cohort layer fixed; COQ unblocks streaming as future complement).
- **Do not propose CursorId-keyed walker-global maps** (Exp 8 S2 REJECT: HashMap-probe overhead exceeds memory savings).

---

## 8. Empirical baseline (anchor for substage Welch tests)

### chain_50 LEFT-assoc (post-L2a, 2.23s wall)

```
step_fanout_calls         = 691
apply_action_calls        = 684,581
  Fork                    = 454,290  (66.4%)
  Pop                     = 155,388  (22.7%)
per_step_apply_action     = 991
cursors_created_via_fork  = 1,370,763
mem_attr_total            = 57 MB
cohort: registrations=646K inflight_collisions=618K (95.7%)
       resolved_hits=27K cohort_cursors_emitted=433K
tomita_key: cumulative_cursors=684,580 distinct_keys=260,980 avg_merge=2.62×
```

### chain_500 LEFT-assoc (post-L2a, 835.10s wall, 16 GB systemd cap held)

```
step_fanout_calls         = 6,912    (10×)
apply_action_calls        = 99,777,311  (146×!)
  Fork                    = 78,338,464  (78.5%)
  Pop                     = 12,351,815  (12.4%)
per_step_apply_action     = 14,420
cursors_created_via_fork  = 197,731,702
cohort: registrations=110M inflight_collisions=108M (98.5%)
       resolved_hits=1.6M cohort_cursors_emitted=26.4M
tomita_key: cumulative=99.7M distinct=33.5M avg_merge=2.97×
```

Scaling exponents (chain_50→chain_500, 10× input):
- apply_action_calls: **N^2.16**
- Wall time: **N^2.58**
- Per-step apply_action: **N^1.16**
- Fork apply_action: **N^2.24**
- TomitaKey distinct: **N^2.11**

For chain_10000 (200× chain_50): projected 38B apply_action_calls / 6.7 days wall / 90+ GB peak.

**COQ target**: bring per-step apply_action from O(N^1.16) to O(1), cumulative from O(N^2.16) to O(N), peak RSS at chain_10000 from 90+ GB to < 500 MB.
