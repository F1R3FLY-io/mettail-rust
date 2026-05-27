# Chain-Interior Cohort Bypass (Plan v5) — exponent fix

**Date**: 2026-05-27
**Branch tip**: `f309d58` (post-COQ-S0)
**Supersedes**: COQ plan (v4), which was empirically falsified at both chain_50 and chain_500 (0.006% reduction in apply_action; cohort_origin was never the dominant merge blocker).
**Honesty caveat**: this plan will NOT pre-commit to chain_10000 < 500 MB. The fix attacks the largest empirically-attributed driver (cohort cursor emission rate), and the plan agent commits to falsifying-at-each-pre-gate + reporting truthfully. If after E5 chain_10000 > 500 MB, the honest verdict is that the 500 MB target requires algorithmic substitution (which the user has forbidden), and the gauntlet target should move to 32-48 GB.

---

## 1. Why prior plans failed

**Common analytical error: confusing cohort cache hit-rate with downstream cursor merge.** All 4 prior plans treated `inflight_collisions = 98.2%` as evidence of saturated dedup. It is not. That stat measures the cache's *registration-time* short-circuit; it doesn't bound how many *post-revive cursors* the cache then *emits*. Empirical: `registrations_total=100.7M, inflight_collisions=98.2M, cohort_cursors_emitted=28.9M` at chain_500 — the cache emits 29M cursors after collapsing 100M registrations. **Cursor-count is the load-bearing axis, not registration-count.**

Per-plan failures:
- v1 (lazy-weight-guided): targeted weight-heap pruning; misread dominant cost.
- v2/v3 (lazy-arc-native): projected L3 Fork arc-emit would Tomita-merge siblings 3×. But sibling arcs have distinct `sppf_stack_id`s (each iteration pushes a new RHS operand). Empirical: `merge_miss (edge, sppf_top) = 96.3%`. Even full L3 wouldn't collapse arcs.
- v4 (COQ): picked `cohort_origin` for collapse. Empirical: `merge_miss cohort_origin = 8.7%`. Dominant blockers: sppf_top (96.3%) + node (93.9%) + edge (100%).

---

## 2. True root cause

**Grammar structure**: Calculator's `AddInt . a:Int, b:Int |- a "+" b : Int` is left-recursive infix. The parser handles `1 + 1 + ... + 1` as N nested `AddInt` applications. Each `+` triggers:

1. `WpdaStepAction::IterativeChainAbsorb` (Exp 6b+7 codegen IS emitting at 1.37M call count). Chain-extension elision shares ONE Return RuleAt across all N iterations.
2. `emit_fire_action` per iteration folds RHS into `Packing` Symbol — bounds SPPF chain growth.
3. **Per-iteration RHS sub-parse** via `InfixChainIterative → PrefixDispatch{rhs_bp}`. The RHS is Int, which Calculator gives multiple categorical interpretations — the cohort cache dispatches each `(pos, Int, rhs_bp)` independently.

**Why per-step cohort grows O(N)**: at chain depth N, cohort cache has N distinct `DispatchKey` entries (one per `(pos, source, bp)` triple). Each entry's `Resolved.symbol_id` is **pinned for the rest of the parse** because the corresponding GSS Return frame stays live (we elided per-iteration Pop). Every subsequent chain step's PrefixDispatch *re-dispatches* against the cache; `ResolvedHit` fans out one revived cursor per worker_snapshot. Snapshots accumulate per (paused_member × snapshot) pair across all past chain depths. `snapshot_appends=42,737` and `pending_members=47,546` — both unbounded in N.

**The cursors at depth N are GENUINELY different**: distinct sppf_stack_id (each iteration pushed an additional RHS operand), distinct node (GSS Return chain index varies), distinct incoming_edge_stack_id (edge prefix encodes the chain), distinct cohort_origin (revive came from different pos). Tomita `merge_disambiguator` correctly preserves all four. **The only way to bound per-step cursor count to O(1) is to PREVENT the divergence at source** — stop the cohort cache from emitting one revived cursor per (snapshot × paused_member × chain_depth) triple. Cohort emission rate (28.9M for chain_500) is the cursor-count multiplier = `O(N²) apply_action`.

---

## 3. The architectural fix: chain-interior cohort cache BYPASS

Honest evaluation of all 5 candidates:

- **(a) Complete IterativeChainAbsorb codegen** — FALSIFIED. Commit `969f3d5` (Exp 6b) shipped codegen; commit `6da30a5` (Exp 7) added per-iteration `emit_fire_action`. The 1.37M apply_action confirms it fires. Docstring at `wpda_runtime.rs:355-367` is stale; update only.

- **(b) Grammar-aware single-Push chain elision** — already the effect of Exp 6/7.

- **(c) Cohort cache GC** — partial. Saves cache memory, NOT cursor emissions. Estimated 5-15%.

- **(d) Lazy SPPF realization** — infeasible without redesigning the SPPF arena's id allocator.

- **(e) Chain-interior cohort cache BYPASS** — **the only structural fix that PREVENTS cursor creation at source.**

**Mechanism**: Inside `IterativeChainAbsorb`, when `already_chained=true`, the walker currently calls `emit_fire_action` once. Extension: suppress ALL cohort-cache registration for the RHS sub-parse on chain-interior iterations. Concretely:

`WpdaState::InfixChainIterative` becomes the exclusive state for chain-interior RHS parsing. `PrefixDispatch` from this state runs in a **non-cohort-cached fast path** that:
1. Eagerly invokes the prefix rule for the single allowed prefix category (Int, plus categorically-determined alternatives per codegen-detectable Plan A invariant I1).
2. Skips `dispatch_cohort_cache.register()` entirely; never emits a revive cursor.
3. Re-enters `InfixLoop` with the freshly-folded SPPF Packing.

Tomita frontier sees ONE cursor per chain step instead of 58K. Projected per-step `cursor_count`: O(grammar size) = O(1), not O(N). **chain_10000 working set: 200-400 MB** if the bypass triggers cleanly.

**Realism caveat**: cross-category implicit casts in Calculator (`Int ↑ Real`, `Int ↑ Complex`) are exactly the cohort revives we'd be bypassing. The RHS of `+` in `1+1+1+…` is well-typed Int and statically known to need no cross-cat dispatch. The cleanest codegen gate: enable the fast path only when `is_iterative_eligible_operator` AND the rhs category has no cross-cat ascent paths from the operator's home category at `rhs_bp`. This is a codegen-time static analysis using the existing `BindingPowerTable`. If that gate fires on Calculator AddInt (it should), the bypass is sound. If it doesn't fire (e.g., another grammar needs the casts), the cohort path is used as today and we get no win on that grammar — by design.

**Estimated LOC: ~800-1200**, concentrated in three files:
- `wpda_walker.rs::IterativeChainAbsorb` arm (~150)
- `wpda_walker.rs::dispatch_step` + new `chain_interior_dispatch_step` (~400)
- `engine_impl.rs::InfixChainIterative` arm + `chain_interior_prefix_dispatch` codegen variant (~250)
- walker-stats counters + tests (~200)

---

## 4. Substage roadmap

| # | Title | LOC | Pre-gate | Falsifier |
|---|-------|-----|----------|-----------|
| **E1** | Static gate instrumentation (READ-ONLY) — new codegen helper `is_chain_interior_rhs_static`; per (operator_category, rhs_bp) report whether rhs prefix dispatch can reach ANY `CrossCatDelegate`. Add `chain_interior_eligible_operators: u64` counter; assert no false positives at runtime. | ~120 | Calculator AddInt MUST register as eligible AND zero runtime violations across gauntlet | any false positive → redesign or gate off Calculator only |
| **E2** | `chain_interior_prefix_dispatch` codegen arm — new `WpdaStepAction::ChainInteriorPrefixDispatch { rhs_category, rhs_bp }`; engine emits from `InfixChainIterative` (replacing today's `PrefixDispatch{cur_bp: rhs_bp}`). Walker forwards to existing path. | ~250 | gauntlet 4213/0; chain_500 wall within 5% of baseline | any regression → revert |
| **E3** | Cohort-cache bypass on chain-interior — `allocate_fork_push_child`'s CrossCatDelegate branch accepts `bypass_cohort_cache: bool`. When true: skip register; run sub-parse eagerly per cursor. | ~400 | instrument `chain_interior_bypass_count`; verify > 99% of chain_500's 100M registrations now bypass | gauntlet < 4213/0; chain_500 RSS > 16 GB |
| **E4** | Tomita ingest for chain-interior pre-merge — verify `tomita_key_projection` avg merge factor at chain_500 jumps from 3.0× to > 50× | ~200 | < 10× → SPPF stack still diverging; investigate | as stated |
| **E5** | chain_10000 close + walker-stats panel — tune `tomita_frontier_map.evict_stale`, drain-vec capacity, retire chain_interior-bypassed `DispatchCacheEntry`s | ~150 | chain_500 ≤ 5 GB RSS / ≤ 6 min wall | **chain_10000 ≤ 500 MB peak RSS in 24 GB cap**; if > 1 GB → fix structurally insufficient; STOP + REPORT |

Total: ~1120 LOC over ~5.5 days.

---

## 5. Soundness

**Gauntlet preservation**: E1 instrumentation only. E2 forwards to existing PrefixDispatch (byte-identical). E3 bypass gated on E1's static analysis — only fires when rhs sub-parse has no CrossCatDelegate reachability (i.e., when `dispatch_cohort_cache` would have only Worker entries; no inflight collisions possible by definition). Bypassing the cache returns exactly the same cursor as the WorkerInserted path.

**chain_500 preservation**: post-E5, all wins from Exp 14 S3-6 + Exp 15 S2-4 (40% wall, 36% RSS) preserved. Fast path only adds work removal, never insertion.

**`-3!` invariant**: multi-packing on infix operators unaffected — `-3!` does not exercise iterative-eligible operators (postfix `!` excluded by `is_iterative_eligible_operator`).

---

## 6. First 30 minutes (actions)

1. `prattail/src/wpda_walker.rs:5354-5417` — `IterativeChainAbsorb` arm; existing emit_fire_action elision + chain-extension witness detection.
2. `prattail/src/wpda_walker.rs:11681-11860` — `allocate_fork_push_child` CrossCatDelegate branch; cohort cache registration point.
3. `macros/src/gen/runtime/wpda_codegen/engine_impl.rs:~1170-1210` — `InfixChainIterative` engine arm; locate `PrefixDispatch{rhs_bp}` emission to replace.
4. `prattail/src/binding_power.rs:81-130` — `is_iterative_eligible` predicate; codegen integration point.

---

## 7. What NOT to do

- Do NOT propose more `ConfigKey` axis drops (Exp 10 S1 REJECT at -7.4%).
- Do NOT propose another `register_arc_with_aggregation` extension; `merge_disambiguator` requires sppf_stack_id equality which chain-interior cursors do not provide.
- Do NOT propose `MAX_PENDING_COHORT_PER_KEY` raises (Stage L6 blew up to 22 GB).
- Do NOT propose streaming SPPF (Exp D-E4 DATA-CONCLUDED futile).
- Do NOT propose Earley/CYK/LR/PEG/Tomita-full-merge.

---

## 8. Honesty addendum (from Plan agent v5 verbatim)

> "The 4 prior plans claimed projections that were not delivered. Empirically, the post-Tomita + im::OrdSet architecture has been measured at 44.7 GB still-growing at chain_10000. The fix above attacks the cohort emission rate, which is the largest empirically-attributed driver (29M cursor emissions/500 chain = ~580M projected at chain_10000; eliminating these is necessary). If after E5 chain_10000 still exceeds 500 MB, the honest answer is that 24 GB chain_10000 is not achievable in this parser representation without an algorithmic substitution (which the user has forbidden), and the gauntlet target should move to 32–48 GB. I will not pre-commit to delivering < 500 MB; I commit to falsifying the fix at each pre-gate and reporting truthfully."
